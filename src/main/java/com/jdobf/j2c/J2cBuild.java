package com.jdobf.j2c;

import com.jdobf.core.Obfuscator;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

/**
 * j2c 构建编排：PE/ZIP 多态 jar + 双 payload 全内存加载链。
 *
 * <h3>产物</h3>
 * <ul>
 *   <li><b>payload1 / payload2</b>：两个独立编译的原生桥，各含一半隐藏类
 *       加密 blob（按引用闭包连通分量分区）。编译后各自整体 XOR 加密，
 *       作为两个普通资源打进 jar，运行时<b>永不落地</b>，由 loader 在
 *       native 内存中解密 + VirtualAlloc 手动映射；payload2 按需映射
 *       （首个本区 shell 绑定时才映射）；</li>
 *   <li><b>loader</b>：与业务无关的通用 PE 手动映射器（双映像状态），
 *       <b>明文 PE 字节</b>前置到 out.jar 字节流开头（zip overlay，
 *       同步重定位中央目录偏移），既不进 zip 资源也不加密。运行时
 *       {@code System.load(jar 自身路径)} 让 OS 直接把用户手里的 jar
 *       当 PE 映射——<b>全程零临时文件</b>。其 JNI 导出名经 j2cconf.h
 *       按每构建随机的桥类名/方法名注入；</li>
 *   <li>每 payload 两个 C 导出符号（arm/bind），四个符号每构建随机。</li>
 * </ul>
 * 临时构建目录用完即删（失败保留编译器输出在异常消息中）。
 */
public final class J2cBuild {

    /** payload native 内解密乘子（与 loader.c 一致）。 */
    public static final int PAYLOAD_MUL = 73;

    private static final String LOADER_RESOURCE = "/com/jdobf/j2c/loader.c";
    /** 伪装用资源目录（jar 条目外观与普通二进制资源一致）。 */
    private static final String[] ENTRY_DIRS = {
            "codec/base", "io/chunk", "rt/buffer", "core/seq",
            "org/jc/base", "util/seq",
    };
    private static final String[] SYM_PREFIX = {
            "jrt_", "awt_", "jfx_", "d3d_", "gdi_", "dwm_",
    };
    private static final String SYM_CHARS = "abcdefghijkmnopqrstuvwxyz0123456789";

    private J2cBuild() {
    }

    public static BootImage.Art build(BootImage.Spec spec, J2c.Plan plan,
                                      Map<String, byte[]> hiddenBytes,
                                      Random random, Obfuscator.Listener listener,
                                      Set<String> usedEntries,
                                      String customEntryName, boolean vmp)
            throws IOException, InterruptedException {
        return build(spec, plan, hiddenBytes, random, listener, usedEntries,
                customEntryName, vmp, false);
    }

    public static BootImage.Art build(BootImage.Spec spec, J2c.Plan plan,
                                      Map<String, byte[]> hiddenBytes,
                                      Random random, Obfuscator.Listener listener,
                                      Set<String> usedEntries,
                                      String customEntryName, boolean vmp,
                                      boolean dbp)
            throws IOException, InterruptedException {
        if (vmp && dbp) {
            throw new IllegalArgumentException("j2c: 不能同时启用 VMProtect 与 DoubaoProtect 加壳");
        }
        boolean protect = vmp || dbp;
        // 完整性检查：每个计划类都必须有捕获字节
        for (J2c.ClassPlan cp : plan.classes.values()) {
            if (!hiddenBytes.containsKey(cp.hiddenName)) {
                throw new IOException("j2c 内部错误：缺少隐藏类字节 " + cp.hiddenName);
            }
        }

        List<CppEmitter.CClass> cclasses = new ArrayList<CppEmitter.CClass>();
        for (J2c.ClassPlan cp : plan.classes.values()) {
            List<CppEmitter.CMethod> methods = new ArrayList<CppEmitter.CMethod>();
            for (String[] k : cp.extract) {
                methods.add(new CppEmitter.CMethod(k[0], k[1],
                        J2c.returnKind(k[1]), parseParams(k[1])));
            }
            int key = 1 + random.nextInt(254);
            cclasses.add(new CppEmitter.CClass(cp.cn.name, cp.hiddenName,
                    hiddenBytes.get(cp.hiddenName), key, methods, cp.group));
        }
        List<CppEmitter.CClass> g0 = new ArrayList<CppEmitter.CClass>();
        List<CppEmitter.CClass> g1 = new ArrayList<CppEmitter.CClass>();
        for (CppEmitter.CClass cc : cclasses) {
            (cc.group == 1 ? g1 : g0).add(cc);
        }
        listener.log("  j2c 分区：payload1 " + g0.size() + " 个隐藏类"
                + (plan.crossPart ? "（单连通分量，镜像2 boot 联动）"
                        : "，payload2 " + g1.size()
                                + " 个隐藏类（严格按需映射）"));

        // 每构建随机的四个 payload 导出符号（互不相同）
        String arm1 = randomSymbol(random);
        String bind1 = distinctSymbol(random, arm1);
        String arm2 = distinctSymbol(random, arm1, bind1);
        String bind2 = distinctSymbol(random, arm1, bind1, arm2);

        // 诊断开关：J2C_VMP_SCOPE / J2C_DBP_SCOPE = loader|payload（默认全部）
        String scope = vmp ? System.getenv("J2C_VMP_SCOPE")
                : dbp ? System.getenv("J2C_DBP_SCOPE") : null;
        boolean packPayload = protect && !"loader".equals(scope);
        boolean packLoader = protect && !"payload".equals(scope);

        String cpp1 = CppEmitter.emit(g0, random, arm1, bind1,
                spec.boot, spec.map, plan.crossPart, packPayload);
        String cpp2 = CppEmitter.emit(g1, random, arm2, bind2,
                spec.boot, spec.map, false, packPayload);

        NativeToolchain.Toolchain tc = NativeToolchain.preflight();
        File dir = Files.createTempDirectory("j2c-build-").toFile();
        try {
            long t0 = System.currentTimeMillis();

            // 标记适配头（始终生成；未定义 J2C_VMP/J2C_DBP 时宏为空操作）
            // 与内置加壳工具链（仅对应加壳构建释放）
            writeFile(new File(dir, "vmpmark.h"), markHeader(vmp, dbp));
            if (vmp) {
                VmpPacker.prepare(dir);
            } else if (dbp) {
                DbpPacker.prepare(dir);
            }

            // 1) 两个 payload DLL（各含一半隐藏类 blob，编译后加密，
            //    永不落地于运行机，全部由 loader 在 native 内存中映射）。
            //    只有实际要加壳的 PE 才带 SDK 标记（VMP 依赖
            //    VMProtectSDK64.dll 导入；DBP 的标记库为静态链接，不会
            //    给运行机新增任何外部依赖）。
            File cpp1File = new File(dir, "j2c1.cpp");
            File cpp2File = new File(dir, "j2c2.cpp");
            File p1Dll = new File(dir, "j2p1.dll");
            File p2Dll = new File(dir, "j2p2.dll");
            writeFile(cpp1File, cpp1.getBytes(StandardCharsets.UTF_8));
            writeFile(cpp2File, cpp2.getBytes(StandardCharsets.UTF_8));
            listener.log("  j2c 正在用 "
                    + (tc.msvc ? "MSVC" : tc.compiler.getName())
                    + " 编译双原生桥接 payload"
                    + (packPayload ? "（含 "
                            + (vmp ? "VMProtect" : "DoubaoProtect")
                            + " 标记）" : "") + "...");
            NativeToolchain.compile(tc, dir, cpp1File, p1Dll,
                    packPayload && vmp, packPayload && dbp);
            NativeToolchain.compile(tc, dir, cpp2File, p2Dll,
                    packPayload && vmp, packPayload && dbp);
            byte[] p1Plain = readFile(p1Dll);
            byte[] p2Plain = readFile(p2Dll);
            // 加壳发生在 XOR 之前：加壳后的高熵 PE 再经密钥流加密入 jar。
            // 单个 PE 加壳失败不拖垮整个 j2c：该 PE 保留未加壳版本（仍经
            // XOR 加密入资源），仅告警。
            if (packPayload) {
                File p1v = new File(dir, "j2p1v.dll");
                File p2v = new File(dir, "j2p2v.dll");
                p1Plain = packOrPlain(dir, "payload1", p1Dll, p1v, p1Plain,
                        listener, vmp, dbp);
                p2Plain = packOrPlain(dir, "payload2", p2Dll, p2v, p2Plain,
                        listener, vmp, dbp);
            }
            int key1 = 1 + random.nextInt(254);
            int key2 = 1 + random.nextInt(254);
            byte[] p1Enc = xor(p1Plain, key1, PAYLOAD_MUL);
            byte[] p2Enc = xor(p2Plain, key2, PAYLOAD_MUL);
            listener.log("  j2c 双 payload 编译完成，耗时 "
                    + (System.currentTimeMillis() - t0) / 1000.0 + "s，明文 "
                    + p1Plain.length / 1024 + "+" + p2Plain.length / 1024
                    + " KB（入 jar 均为加密态）");

            // 2) loader DLL：通用双映像手动映射器，明文以前缀 PE 形态
            //    拼到 jar 头部；JNI 导出名按本构建桥类注入
            String conf = "#pragma once\n"
                    + "/* generated per build; do not edit */\n"
                    + "#define J2C_MAPFN "
                    + jniMangleClass(spec.map) + "_" + jniMangleMethod(spec.mapM) + "\n"
                    + "#define J2C_MAPFN2 "
                    + jniMangleClass(spec.map) + "_" + jniMangleMethod(spec.mapM2) + "\n"
                    + "#define J2C_BINDFN "
                    + jniMangleClass(spec.bind) + "_" + jniMangleMethod(spec.bindM) + "\n"
                    + "#define J2C_BINDFN2 "
                    + jniMangleClass(spec.bind) + "_" + jniMangleMethod(spec.bindM2) + "\n"
                    + "#define J2C_PINGFN "
                    + jniMangleClass(spec.str) + "_" + jniMangleMethod(spec.pingM) + "\n";
            writeFile(new File(dir, "j2cconf.h"),
                    conf.getBytes(StandardCharsets.UTF_8));
            byte[] loaderSrc = readResource();
            // 用 .cpp 扩展名强制 C++ 编译（jni.h 的 env-> 调用约定）
            File loaderFile = new File(dir, "j2ldr.cpp");
            File loaderDll = new File(dir, "j2l.dll");
            writeFile(loaderFile, loaderSrc);
            long t1 = System.currentTimeMillis();
            NativeToolchain.compile(tc, dir, loaderFile, loaderDll,
                    packLoader && vmp, packLoader && dbp);
            byte[] loaderPlain = readFile(loaderDll);
            if (packLoader) {
                // loader 由 OS 直接 LoadLibrary（System.load），不经手动映射，
                // 加壳后兼容性最有保障
                File loaderV = new File(dir, "j2lv.dll");
                loaderPlain = packOrPlain(dir, "loader", loaderDll, loaderV,
                        loaderPlain, listener, vmp, dbp);
            }
            listener.log("  j2c loader 编译完成，耗时 "
                    + (System.currentTimeMillis() - t1) / 1000.0 + "s，体积 "
                    + loaderPlain.length / 1024 + " KB（"
                    + (vmp ? "VMProtect 加壳态"
                            : dbp ? "DoubaoProtect 加壳态" : "明文 PE")
                    + "前置进 jar，运行时 System.load 自身，零落地）");

            // 3) 两个 jar 加密资源条目名：用户自定义模板优先，
            //    留空/非法/冲突时回退随机伪装名
            String[] custom = resolveCustomEntries(customEntryName,
                    usedEntries, listener);
            String entry1;
            String entry2;
            if (custom != null) {
                entry1 = custom[0];
                entry2 = custom[1];
                listener.log("  j2c native 资源名使用自定义模板：" + entry1
                        + " / " + entry2);
            } else {
                entry1 = chooseEntry(random, usedEntries, "b");
                usedEntries.add(entry1);
                entry2 = chooseEntry(random, usedEntries, "q");
            }
            usedEntries.add(entry1);
            usedEntries.add(entry2);

            return new BootImage.Art(entry1, entry2, p1Enc, p2Enc, key1, key2,
                    arm1, bind1, arm2, bind2, loaderPlain);
        } finally {
            // 诊断用：设置 J2C_KEEP_DIR 时保留构建临时目录（含生成的 cpp/dll）
            if (System.getenv("J2C_KEEP_DIR") == null) {
                deleteQuietly(dir);
            } else {
                listener.log("  [诊断] j2c 构建目录已保留：" + dir);
            }
        }
    }

    // ------------------------------------------------------------------
    // 命名/加密辅助
    // ------------------------------------------------------------------

    /**
     * 对单个 PE 加壳；失败时告警并回退未加壳字节（InterruptedException
     * 属用户取消，向上抛出不降级）。
     */
    private static byte[] packOrPlain(File dir, String tag, File input, File output,
                                      byte[] plainBytes, Obfuscator.Listener listener,
                                      boolean vmp, boolean dbp)
            throws IOException, InterruptedException {
        try {
            if (vmp) {
                VmpPacker.pack(dir, tag, input, output, listener);
            } else if (dbp) {
                DbpPacker.pack(dir, tag, input, output, listener);
            } else {
                return plainBytes;
            }
            return readFile(output);
        } catch (InterruptedException ie) {
            throw ie;
        } catch (IOException ioe) {
            String name = vmp ? "VMProtect" : "DoubaoProtect";
            listener.log("[警告] " + tag + " " + name + " 加壳失败，该 PE 回退为"
                    + "未加壳版本（其余 PE 不受影响）：" + ioe.getMessage());
            return plainBytes;
        }
    }

    /**
     * 标记适配头（C/C++ 双兼容，payload C++ 与 loader 均 include）。
     * J2C_VMP / J2C_DBP 由 {@link NativeToolchain} 仅在对应加壳构建时定义；
     * 都未定义时所有标记为空操作，普通 j2c 产物与旧路径字节一致。
     */
    private static byte[] markHeader(boolean vmp, boolean dbp) {
        return dbp ? dbpMarkHeader() : vmpMarkHeader();
    }

    /**
     * VMProtect 标记适配头：J2C_VMP 定义时链接 VMProtect SDK，否则空操作。
     */
    private static byte[] vmpMarkHeader() {
        // 诊断开关 J2C_VMP_LEVEL：mut=Ultra 降级为纯变异；virt=纯虚拟化
        String ultraCall = "VMProtectBeginUltra(n)";
        String level = System.getenv("J2C_VMP_LEVEL");
        if ("mut".equals(level)) {
            ultraCall = "VMProtectBeginMutation(n)";
        } else if ("virt".equals(level)) {
            ultraCall = "VMProtectBeginVirtualization(n)";
        }
        String h = "#pragma once\n"
                + "/* generated per build; do not edit */\n"
                + "#ifdef J2C_VMP\n"
                + "#include \"VMProtectSDK.h\"\n"
                + "#define VMP_BEGIN_ULTRA(n) " + ultraCall + "\n"
                + "#define VMP_BEGIN_VIRT(n)  VMProtectBeginVirtualization(n)\n"
                + "#define VMP_BEGIN_MUT(n)   VMProtectBeginMutation(n)\n"
                + "#define VMP_END()          VMProtectEnd()\n"
                + "/* MSVC 自动向量化器（VS2022 起即使默认 /arch:SSE2 也可能经\n"
                + " * 运行时 CPUID 分发发射 AVX-512VL 的 EVEX 指令，vpmovwb 等）\n"
                + " * 会让 VMProtect 反汇编器报 \"Command not supported db 62\"。\n"
                + " * 标记区内的字节循环一律禁止向量化。 */\n"
                + "#if defined(_MSC_VER)\n"
                + "#define VMP_NOVEC __pragma(loop(no_vector))\n"
                + "#define J2C_NOINLINE __declspec(noinline)\n"
                + "#else\n"
                + "#define VMP_NOVEC\n"
                + "#define J2C_NOINLINE __attribute__((noinline))\n"
                + "#endif\n"
                + "#else\n"
                + "#define VMP_BEGIN_ULTRA(n) ((void)0)\n"
                + "#define VMP_BEGIN_VIRT(n)  ((void)0)\n"
                + "#define VMP_BEGIN_MUT(n)   ((void)0)\n"
                + "#define VMP_END()          ((void)0)\n"
                + "#define VMP_NOVEC\n"
                + "#define J2C_NOINLINE\n"
                + "#endif\n";
        return h.getBytes(StandardCharsets.UTF_8);
    }

    /**
     * DoubaoProtect 标记适配头：J2C_DBP 定义时展开为 DoubaoProtect SDK
     * 标记函数，否则空操作。沿用 VMP_* 宏名以复用 CppEmitter/loader.c。
     */
    private static byte[] dbpMarkHeader() {
        String h = "#pragma once\n"
                + "/* generated per build; do not edit */\n"
                + "#ifdef J2C_DBP\n"
                + "#include \"DoubaoProtect.h\"\n"
                + "#define VMP_BEGIN_ULTRA(n) DoubaoProtectBeginUltra(n)\n"
                + "#define VMP_BEGIN_VIRT(n)  DoubaoProtectBeginUltra(n)\n"
                + "#define VMP_BEGIN_MUT(n)   DoubaoProtectBeginMutation(n)\n"
                + "#define VMP_END()          DoubaoProtectEnd()\n"
                + "#if defined(_MSC_VER)\n"
                + "#define VMP_NOVEC __pragma(loop(no_vector))\n"
                + "#define J2C_NOINLINE __declspec(noinline)\n"
                + "#else\n"
                + "#define VMP_NOVEC\n"
                + "#define J2C_NOINLINE __attribute__((noinline))\n"
                + "#endif\n"
                + "#else\n"
                + "#define VMP_BEGIN_ULTRA(n) ((void)0)\n"
                + "#define VMP_BEGIN_VIRT(n)  ((void)0)\n"
                + "#define VMP_BEGIN_MUT(n)   ((void)0)\n"
                + "#define VMP_END()          ((void)0)\n"
                + "#define VMP_NOVEC\n"
                + "#define J2C_NOINLINE\n"
                + "#endif\n";
        return h.getBytes(StandardCharsets.UTF_8);
    }

    private static String randomSymbol(Random random) {
        StringBuilder sb = new StringBuilder(
                SYM_PREFIX[random.nextInt(SYM_PREFIX.length)]);
        int n = 6 + random.nextInt(5);
        for (int i = 0; i < n; i++) {
            sb.append(SYM_CHARS.charAt(random.nextInt(SYM_CHARS.length())));
        }
        return sb.toString();
    }

    private static String distinctSymbol(Random random, String... taken) {
        java.util.Set<String> set = new java.util.HashSet<String>(
                java.util.Arrays.asList(taken));
        for (int t = 0; t < 64; t++) {
            String s = randomSymbol(random);
            if (set.add(s)) {
                return s;
            }
        }
        throw new IllegalStateException("j2c: 无法分配唯一导出符号");
    }

    /**
     * 解析用户自定义的 native 资源名模板为两个互不冲突的 jar 条目名。
     * 模板为空返回 null（走随机伪装名）；模板非法或派生出的名称冲突时
     * 警告并返回 null（回退随机名，绝不让坏名字进产物）。
     *
     * <p>规则：{@code {}} 占位符整体替换为 1/2；无占位符时序号插入到
     * 最后一个扩展名前（{@code a/b.x} → {@code a/b1.x}、{@code a/b2.x}），
     * 无扩展名则直接追加。
     */
    private static String[] resolveCustomEntries(String template,
                                                 Set<String> used,
                                                 Obfuscator.Listener listener) {
        if (template == null) {
            return null;
        }
        String t = template.trim();
        if (t.isEmpty()) {
            return null;
        }
        String raw = t;
        // 容错：Windows 分隔符统一为 '/'；去掉前导 '/'（jar 条目是相对名）
        t = t.replace('\\', '/');
        while (t.startsWith("/")) {
            t = t.substring(1);
        }
        if (t.isEmpty() || t.endsWith("/") || t.length() > 200) {
            listener.log("[警告] j2c native 资源名模板非法（空/目录形态/过长），"
                    + "已回退随机名：" + raw);
            return null;
        }
        // zip 条目安全字符：ASCII 可见字符，排除 : * ? " < > |
        for (int i = 0; i < t.length(); i++) {
            char c = t.charAt(i);
            if (c < 0x20 || c > 0x7E || c == ':' || c == '*' || c == '?'
                    || c == '"' || c == '<' || c == '>' || c == '|') {
                listener.log("[警告] j2c native 资源名模板含非法字符 '"
                        + c + "'，已回退随机名：" + raw);
                return null;
            }
        }
        String n1;
        String n2;
        if (t.contains("{}")) {
            n1 = t.replace("{}", "1");
            n2 = t.replace("{}", "2");
        } else {
            int slash = t.lastIndexOf('/');
            int dot = t.lastIndexOf('.');
            if (dot > slash && dot > 0) {
                n1 = t.substring(0, dot) + "1" + t.substring(dot);
                n2 = t.substring(0, dot) + "2" + t.substring(dot);
            } else {
                n1 = t + "1";
                n2 = t + "2";
            }
        }
        if (n1.equals(n2) || used.contains(n1) || used.contains(n2)
                || n1.isEmpty() || n2.isEmpty()) {
            listener.log("[警告] j2c native 资源名派生冲突或与现有 jar 条目重名"
                    + "（" + n1 + " / " + n2 + "），已回退随机名：" + raw);
            return null;
        }
        return new String[] { n1, n2 };
    }

    private static String chooseEntry(Random random, Set<String> used, String tag) {
        for (int t = 0; t < 64; t++) {
            String dir = ENTRY_DIRS[random.nextInt(ENTRY_DIRS.length)];
            StringBuilder sb = new StringBuilder(dir).append('/').append(tag);
            for (int i = 0; i < 10; i++) {
                sb.append(Character.forDigit(random.nextInt(16), 16));
            }
            sb.append(".bin");
            String entry = sb.toString();
            if (!used.contains(entry)) {
                return entry;
            }
        }
        throw new IllegalStateException("j2c: 无法分配资源条目名");
    }

    static byte[] xor(byte[] data, int key, int mul) {
        byte[] out = new byte[data.length];
        for (int i = 0; i < data.length; i++) {
            out[i] = (byte) (data[i] ^ ((key + i * mul) & 255));
        }
        return out;
    }

    /** JNI 短名 mangle：Java_&lt;类：/ → _、_ → _1、$ → _00024&gt;。 */
    static String jniMangleClass(String internalName) {
        StringBuilder sb = new StringBuilder("Java_");
        for (int i = 0; i < internalName.length(); i++) {
            char ch = internalName.charAt(i);
            switch (ch) {
                case '/':
                    sb.append('_');
                    break;
                case '_':
                    sb.append("_1");
                    break;
                case ';':
                    sb.append("_2");
                    break;
                case '[':
                    sb.append("_3");
                    break;
                case '$':
                    sb.append("_00024");
                    break;
                default:
                    sb.append(ch);
            }
        }
        return sb.toString();
    }

    /** JNI 方法名 mangle（桥方法无重载，不追加描述符后缀）。 */
    static String jniMangleMethod(String method) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < method.length(); i++) {
            char ch = method.charAt(i);
            if (ch == '_') {
                sb.append("_1");
            } else if (ch == '$') {
                sb.append("_00024");
            } else {
                sb.append(ch);
            }
        }
        return sb.toString();
    }

    private static byte[] readResource() throws IOException {
        InputStream in = J2cBuild.class.getResourceAsStream(LOADER_RESOURCE);
        if (in == null) {
            throw new IOException("j2c 内部错误：classpath 缺少 " + LOADER_RESOURCE);
        }
        try {
            ByteArrayOutputStream bos = new ByteArrayOutputStream(65536);
            byte[] buf = new byte[8192];
            int n;
            while ((n = in.read(buf)) > 0) {
                bos.write(buf, 0, n);
            }
            return bos.toByteArray();
        } finally {
            in.close();
        }
    }

    /** 解析描述符参数为桥接类型：Z B C S I J F D，对象与<b>任意数组</b>为 O。 */
    static List<Character> parseParams(String desc) {
        List<Character> out = new ArrayList<Character>();
        int i = desc.indexOf(')');
        int p = 1;
        while (p < i) {
            boolean isArray = false;
            while (p < i && desc.charAt(p) == '[') {
                isArray = true;
                p++;
            }
            char c = desc.charAt(p);
            if (c == 'L') {
                p = desc.indexOf(';', p) + 1;
                out.add(Character.valueOf('O'));
            } else {
                p++;
                out.add(Character.valueOf((!isArray && "ZBCSIJFD".indexOf(c) >= 0)
                        ? c : 'O'));
            }
        }
        return out;
    }

    private static void writeFile(File f, byte[] data) throws IOException {
        FileOutputStream fos = new FileOutputStream(f);
        try {
            fos.write(data);
        } finally {
            fos.close();
        }
    }

    private static byte[] readFile(File f) throws IOException {
        ByteArrayOutputStream bos = new ByteArrayOutputStream((int) f.length());
        java.io.FileInputStream in = new java.io.FileInputStream(f);
        try {
            byte[] buf = new byte[16384];
            int n;
            while ((n = in.read(buf)) > 0) {
                bos.write(buf, 0, n);
            }
        } finally {
            in.close();
        }
        return bos.toByteArray();
    }

    private static void deleteQuietly(File f) {
        if (!f.exists()) {
            return;
        }
        File[] kids = f.listFiles();
        if (kids != null) {
            for (File k : kids) {
                deleteQuietly(k);
            }
        }
        //noinspection ResultOfMethodCallIgnored
        f.delete();
    }
}
