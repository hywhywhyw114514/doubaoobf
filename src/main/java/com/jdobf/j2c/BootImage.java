package com.jdobf.j2c;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

/**
 * 生成运行时引导桥簇（字节码手工搭建，Java 8 兼容）。
 *
 * <h3>全内存加载链（零临时文件，两个 payload 均不落地）</h3>
 * shell 的 &lt;clinit&gt; 调用入口类 {@code tie(Class)}：
 * <ol>
 *   <li>jar 本身是 PE/ZIP 多态文件：通用 loader（手动映射器）明文 PE
 *       前置在文件头，ZIP 部分作 overlay。{@code M.stage} 取本类
 *       ProtectionDomain 的 CodeSource 定位 jar 自身路径并
 *       {@code System.load(该路径)}——OS 直接把用户手里的 jar 映射为
 *       loader 镜像，<b>全程不写任何临时文件</b>；</li>
 *   <li>loader 的 mapM native 接收仍处于加密状态的 payload1 字节，在
 *       native 内解密 + VirtualAlloc 手动映射
 *       （节区/重定位/IAT/异常表/TLS/入口），解析两个随机命名的
 *       arm/bind 导出并调 arm：arm 立即用 boot 桥类的 ClassLoader
 *       多趟 DefineClass 复活本区全部隐藏类；</li>
 *   <li>每个 shell 再经 bind(Class) 让对应 payload 对自己
 *       RegisterNatives；bind 返回 2（非本区）时才经 stage2/mapM2
 *       <b>按需</b>在内存中映射 payload2（其加密资源此前从不解密）。</li>
 * </ol>
 *
 * <h3>反分析伪装</h3>
 * 5 个外观普通的工具类（cache/codec/res 风格）：敏感字符串全部 XOR
 * 字节数组 + 解码器动态还原；密钥拆成 3 个常量碎片；真实逻辑拆在不同
 * 类中并穿插大量伪工具方法（数组/字符串/hash/有界循环/TABLESWITCH）、
 * 不透明谓词、垃圾字段与从不调用的诱饵 native 声明。
 */
public final class BootImage {

    private BootImage() {
    }

    /** 桥簇角色与真实 native 成员命名（编译 loader 的 conf.h 也要用）。 */
    public static final class Spec {
        public final String boot;
        public final String res;
        public final String str;
        public final String map;
        public final String bind;
        /** 镜像1 映射 native（map 类）。 */
        public final String mapM;
        /** 镜像2 按需映射 native（map 类）。 */
        public final String mapM2;
        /** 镜像1 shell 绑定 native（bind 类）。 */
        public final String bindM;
        /** 镜像2 shell 绑定 native（bind 类）。 */
        public final String bindM2;
        /** 掩护用真实导出 native（str 类）。 */
        public final String pingM;

        Spec(String[] names, String mapM, String mapM2,
             String bindM, String bindM2, String pingM) {
            this.boot = names[0];
            this.res = names[1];
            this.str = names[2];
            this.map = names[3];
            this.bind = names[4];
            this.mapM = mapM;
            this.mapM2 = mapM2;
            this.bindM = bindM;
            this.bindM2 = bindM2;
            this.pingM = pingM;
        }

        public String[] all() {
            return new String[] { boot, res, str, map, bind };
        }
    }

    /** 构建产物：两个加密资源 + 随机导出符号 + 明文 loader PE。 */
    public static final class Art {
        /** 镜像1/2 的 jar 加密资源条目名（无前导 /）。 */
        public final String entry1;
        public final String entry2;
        public final byte[] enc1;
        public final byte[] enc2;
        public final int key1;
        public final int key2;
        public final String arm1;
        public final String bind1;
        public final String arm2;
        public final String bind2;
        /** 明文 loader PE：前置进 jar 文件头，不进 zip 资源。 */
        public final byte[] loaderPlain;

        Art(String entry1, String entry2, byte[] enc1, byte[] enc2,
            int key1, int key2,
            String arm1, String bind1, String arm2, String bind2,
            byte[] loaderPlain) {
            this.entry1 = entry1;
            this.entry2 = entry2;
            this.enc1 = enc1;
            this.enc2 = enc2;
            this.key1 = key1;
            this.key2 = key2;
            this.arm1 = arm1;
            this.bind1 = bind1;
            this.arm2 = arm2;
            this.bind2 = bind2;
            this.loaderPlain = loaderPlain;
        }
    }

    private static final String[] METHOD_WORDS = {
            "readFully", "drain", "copyTo", "checksum", "fold", "inflate",
            "deflate", "merge", "coalesce", "adopt", "retain", "purge",
            "scan", "locate", "prepare", "verify", "touch", "warm", "probe",
            "reset", "bump", "appendEscaped", "parseToken", "encodeBytes",
            "decodeBytes", "indexOf", "hashOf", "normalize", "digest",
            "stamp", "markUsed", "closeQuietly", "canReuse", "seqValue",
            "tabAt", "fillTable", "applyMask", "mixInto", "asString",
    };
    private static final String[] FIELD_WORDS = {
            "buf", "seq", "mask", "table", "factor", "tag", "hits",
            "offset", "seed", "state", "tmp", "locked", "ver", "inited",
            "cache",
    };
    private static final String[] STRING_POOL = {
            "0", "1", "x", "a", "v=", "idx", "n=", "-", "ok", "tmp", "key",
    };
    /** 诱饵 native 描述符：从不调用，VM 懒绑定，无导出也不会出错。 */
    private static final String[] DECOY_DESCS = {
            "()V", "(I)V", "(J)J", "(Z)Z", "(D)D", "([B)I",
            "(Ljava/lang/String;)I", "(II)Z", "([I)V",
            "(Ljava/lang/Object;I)V",
    };

    // ------------------------------------------------------------------
    // 规划
    // ------------------------------------------------------------------

    public static Spec plan(String[] names, Random rnd) {
        if (names.length != 5) {
            throw new IllegalArgumentException("j2c bridge needs 5 class names");
        }
        // mapM/mapM2 同在 map 类、bindM/bindM2 同在 bind 类，
        // 各自池互不相交
        return new Spec(names.clone(),
                pickWord(rnd, "adopt", "coalesce", "prepare"),
                pickWord(rnd, "drain", "inflate", "merge"),
                pickWord(rnd, "touch", "verify", "markUsed"),
                pickWord(rnd, "scan", "locate", "stamp"),
                pickWord(rnd, "probe", "bump", "knock"));
    }

    private static String pickWord(Random rnd, String... fixed) {
        return fixed[rnd.nextInt(fixed.length)];
    }

    // ------------------------------------------------------------------
    // 生成
    // ------------------------------------------------------------------

    public static Map<String, byte[]> generate(Spec spec, Art art, Random rnd) {
        Cx B = new Cx(spec.boot, rnd);
        Cx R = new Cx(spec.res, rnd);
        Cx S = new Cx(spec.str, rnd);
        Cx M = new Cx(spec.map, rnd);
        Cx N = new Cx(spec.bind, rnd);

        // 不透明谓词三元组：r == p*q（clinit 建立）
        for (Cx c : new Cx[] { B, R, S, M, N }) {
            c.addTriplet();
            c.ensureSeq();
        }

        // ---- S：字符串 blobs + 解码器 + 两组密钥碎片 ----
        StringItem sOs = addString(S, "sysKey", "os.name", rnd);
        StringItem sArch = addString(S, "sysKind", "os.arch", rnd);
        StringItem sWin = addString(S, "winTag", "win", rnd);
        StringItem s64 = addString(S, "tag64", "amd64", rnd);
        StringItem s86 = addString(S, "tag86", "x86_64", rnd);
        StringItem sPay1 = addString(S, "blobPath", "/" + art.entry1, rnd);
        StringItem sPay2 = addString(S, "blobPath2", "/" + art.entry2, rnd);
        StringItem sArm1 = addString(S, "armRef", art.arm1, rnd);
        StringItem sBind1 = addString(S, "bindRef", art.bind1, rnd);
        StringItem sArm2 = addString(S, "armRef2", art.arm2, rnd);
        StringItem sBind2 = addString(S, "bindRef2", art.bind2, rnd);
        StringItem sPlat = addString(S, "msgPlatform", "platform init failed", rnd);
        StringItem sStream = addString(S, "msgStream", "stream unavailable", rnd);
        StringItem sStage = addString(S, "msgStage", "stage failed", rnd);
        StringItem sBindErr = addString(S, "msgBind", "bind failed", rnd);

        emitDecoder(S);
        // 密钥碎片：deriveKey()  = (f0 ^ f1) + f2 == key1；
        //           deriveKey2() = (g0 ^ g1) + g2 == key2
        int f0 = 1000 + rnd.nextInt(50000);
        int f1 = 1000 + rnd.nextInt(50000);
        int f2 = art.key1 - (f0 ^ f1);
        int g0 = 1000 + rnd.nextInt(50000);
        int g1 = 1000 + rnd.nextInt(50000);
        int g2 = art.key2 - (g0 ^ g1);
        emitKeyMethod(S, "deriveKey", f0, f1, f2);
        emitKeyMethod(S, "deriveKey2", g0, g1, g2);
        // ping：真实导出但只做无意义热身
        emitPingWrapper(S, spec.pingM);

        // ---- R：资源读取（两个加密 payload） ----
        emitReader(R, S, spec, sStream);
        emitPayloadAccessor(R, S, sPay1, "payload");
        emitPayloadAccessor(R, S, sPay2, "payload2");

        // ---- M：System.load(jar 自身) + mapM/mapM2 双映射 ----
        emitMapper(M, R, S, spec, sStage, sArm2, sBind2);

        // ---- N：bind native 三态路由（2 时按需拉起镜像2） ----
        emitBinder(N, M, S, spec, sBindErr);

        // ---- B：入口 tie ----
        emitTie(B, R, S, M, N, sOs, sArch, sWin, s64, s86, sPlat, sStage,
                sArm1, sBind1);

        // ---- 屎山填充 + 诱饵 native + 重排 ----
        fillJunk(B, rnd, 8, 2);
        fillJunk(R, rnd, 10, 2);
        fillJunk(S, rnd, 12, 2);
        fillJunk(M, rnd, 9, 3);
        fillJunk(N, rnd, 8, 2);

        Map<String, byte[]> out = new LinkedHashMap<String, byte[]>();
        for (Cx c : new Cx[] { B, R, S, M, N }) {
            out.put(c.cn.name, c.finish());
        }
        return out;
    }

    // ------------------------------------------------------------------
    // 类构建辅助
    // ------------------------------------------------------------------

    static final class Cx {
        final ClassNode cn;
        final Random rnd;
        final List<String> used = new ArrayList<String>();
        final InsnList clinit = new InsnList();
        final List<MethodNode> methods = new ArrayList<MethodNode>();
        String pF, qF, rF;       // 不透明谓词三元组
        String seqF;             // 抖动静态 int

        Cx(String name, Random rnd) {
            this.cn = new ClassNode(Opcodes.ASM9);
            this.cn.version = Opcodes.V1_8;
            this.cn.access = Opcodes.ACC_PUBLIC | Opcodes.ACC_FINAL
                    | Opcodes.ACC_SYNTHETIC;
            this.cn.name = name;
            this.cn.superName = "java/lang/Object";
            this.rnd = rnd;
            // 私有构造器：工具类外观
            MethodNode ctor = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE, "<init>", "()V", null, null);
            ctor.instructions.add(new VarInsnNode(Opcodes.ALOAD, 0));
            ctor.instructions.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                    "java/lang/Object", "<init>", "()V", false));
            ctor.instructions.add(new InsnNode(Opcodes.RETURN));
            methods.add(ctor);
        }

        String name() {
            String[] src = METHOD_WORDS;
            for (int t = 0; ; t++) {
                String base = src[rnd.nextInt(src.length)];
                String n = t == 0 ? base : base + t;
                if (!used.contains(n)) {
                    used.add(n);
                    return n;
                }
            }
        }

        String fieldName() {
            for (int t = 0; ; t++) {
                String n = FIELD_WORDS[rnd.nextInt(FIELD_WORDS.length)]
                        + (t == 0 ? "" : String.valueOf(t));
                if (!used.contains(n)) {
                    used.add(n);
                    return n;
                }
            }
        }

        void addTriplet() {
            pF = fieldName();
            qF = fieldName();
            rF = fieldName();
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, pF, "I", null, null));
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, qF, "I", null, null));
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, rF, "I", null, null));
            int p = 3 + rnd.nextInt(16);
            int q = 5 + rnd.nextInt(18);
            clinit.add(ldc(p));
            clinit.add(new FieldInsnNode(Opcodes.PUTSTATIC, cn.name, pF, "I"));
            clinit.add(ldc(q));
            clinit.add(new FieldInsnNode(Opcodes.PUTSTATIC, cn.name, qF, "I"));
            clinit.add(new FieldInsnNode(Opcodes.GETSTATIC, cn.name, pF, "I"));
            clinit.add(new FieldInsnNode(Opcodes.GETSTATIC, cn.name, qF, "I"));
            clinit.add(new InsnNode(Opcodes.IMUL));
            clinit.add(new FieldInsnNode(Opcodes.PUTSTATIC, cn.name, rF, "I"));
        }

        void ensureSeq() {
            seqF = fieldName();
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, seqF, "I", null,
                    Integer.valueOf(rnd.nextInt(256))));
        }

        /** 恒真不透明谓词：真路径落到 fallthrough，假路径跳到 dead。 */
        void opaqueTrue(InsnList il, LabelNode dead) {
            il.add(new FieldInsnNode(Opcodes.GETSTATIC, cn.name, pF, "I"));
            il.add(new FieldInsnNode(Opcodes.GETSTATIC, cn.name, qF, "I"));
            il.add(new InsnNode(Opcodes.IMUL));
            il.add(new FieldInsnNode(Opcodes.GETSTATIC, cn.name, rF, "I"));
            il.add(new JumpInsnNode(Opcodes.IF_ICMPNE, dead));
        }

        byte[] finish() {
            clinit.add(new InsnNode(Opcodes.RETURN));
            MethodNode ci = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                    "<clinit>", "()V", null, null);
            ci.instructions = clinit;
            // <clinit> 置首，<init> 次之，其余成员随机穿插
            List<MethodNode> rest = new ArrayList<MethodNode>(methods);
            MethodNode init = null;
            for (MethodNode m : rest) {
                if (m.name.equals("<init>")) {
                    init = m;
                }
            }
            rest.remove(init);
            Collections.shuffle(rest, rnd);
            cn.methods.clear();
            cn.methods.add(ci);
            if (init != null) {
                cn.methods.add(init);
            }
            cn.methods.addAll(rest);
            Collections.shuffle(cn.fields, rnd);
            ClassWriter cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES
                    | ClassWriter.COMPUTE_MAXS);
            cn.accept(cw);
            return cw.toByteArray();
        }
    }

    static final class StringItem {
        final String field;
        final int key;
        final String accessor;

        StringItem(String field, int key, String accessor) {
            this.field = field;
            this.key = key;
            this.accessor = accessor;
        }
    }

    private static StringItem addString(Cx S, String accessor, String value,
                                        Random rnd) {
        String field = S.fieldName();
        int key = 1 + rnd.nextInt(254);
        byte[] raw = value.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1);
        S.cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL
                        | Opcodes.ACC_SYNTHETIC,
                field, "[B", null, null));
        // clinit: new byte[N] { xor(plain, key, 31) ... }
        S.clinit.add(ldc(raw.length));
        S.clinit.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_BYTE));
        S.clinit.add(new FieldInsnNode(Opcodes.PUTSTATIC, S.cn.name, field, "[B"));
        for (int i = 0; i < raw.length; i++) {
            int v = (raw[i] & 255) ^ ((key + i * 31) & 255);
            S.clinit.add(new FieldInsnNode(Opcodes.GETSTATIC, S.cn.name, field, "[B"));
            S.clinit.add(ldc(i));
            S.clinit.add(intPush(v));
            S.clinit.add(new InsnNode(Opcodes.BASTORE));
        }
        // accessor(): return d(FIELD, key)
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                accessor, "()Ljava/lang/String;", null, null);
        m.instructions.add(new FieldInsnNode(Opcodes.GETSTATIC,
                S.cn.name, field, "[B"));
        m.instructions.add(ldc(key));
        m.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, "d", "([BI)Ljava/lang/String;", false));
        m.instructions.add(new InsnNode(Opcodes.ARETURN));
        S.methods.add(m);
        S.used.add(accessor);
        return new StringItem(field, key, accessor);
    }

    /** static String d(byte[] a, int k)：b[i] = a[i] ^ (k + i*31)。 */
    private static void emitDecoder(Cx S) {
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                "d", "([BI)Ljava/lang/String;", null, null);
        InsnList il = m.instructions;
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new InsnNode(Opcodes.ARRAYLENGTH));
        il.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_BYTE));
        il.add(new VarInsnNode(Opcodes.ASTORE, 2));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new InsnNode(Opcodes.ARRAYLENGTH));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.BALOAD));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(intPush(31));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new InsnNode(Opcodes.I2B));
        il.add(new InsnNode(Opcodes.BASTORE));
        il.add(new org.objectweb.asm.tree.IincInsnNode(3, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.NEW,
                "java/lang/String"));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/String", "<init>", "([B)V", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        S.methods.add(m);
        S.used.add("d");

        // 形态近似的伪解码器（无人调用）
        MethodNode f = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC,
                S.name(), "([BI)[B", null, null);
        f.instructions.add(new VarInsnNode(Opcodes.ALOAD, 0));
        f.instructions.add(new InsnNode(Opcodes.ARETURN));
        S.methods.add(f);
    }

    /** static int name() { return (a ^ b) + c; } */
    private static void emitKeyMethod(Cx S, String name, int a, int b, int c) {
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                name, "()I", null, null);
        m.instructions.add(ldc(a));
        m.instructions.add(ldc(b));
        m.instructions.add(new InsnNode(Opcodes.IXOR));
        m.instructions.add(ldc(c));
        m.instructions.add(new InsnNode(Opcodes.IADD));
        m.instructions.add(new InsnNode(Opcodes.IRETURN));
        S.methods.add(m);
        S.used.add(name);
    }

    /** int warm(int x)：恒真分支里调真实 ping native，假分支算术。 */
    private static void emitPingWrapper(Cx S, String pingM) {
        MethodNode nat = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_NATIVE,
                pingM, "(I)I", null, null);
        S.methods.add(nat);
        S.used.add(pingM);

        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                "warm", "(I)I", null, null);
        InsnList il = m.instructions;
        LabelNode dead = new LabelNode();
        LabelNode end = new LabelNode();
        S.opaqueTrue(il, dead);
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, pingM, "(I)I", false));
        il.add(new JumpInsnNode(Opcodes.GOTO, end));
        il.add(dead);
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(intPush(31));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(intPush(17));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(end);
        il.add(new InsnNode(Opcodes.IRETURN));
        S.methods.add(m);
        S.used.add("warm");
    }

    /** R.read(String path)：bootClass.getResourceAsStream + BAOS，IOEx 包 ULE。 */
    private static void emitReader(Cx R, Cx S, Spec spec, StringItem msg) {
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                "read", "(Ljava/lang/String;)[B", null, null);
        InsnList il = m.instructions;
        LabelNode tryStart = new LabelNode();
        LabelNode have = new LabelNode();
        LabelNode loop = new LabelNode();
        LabelNode done = new LabelNode();
        LabelNode tryEnd = new LabelNode();
        LabelNode handler = new LabelNode();

        m.tryCatchBlocks.add(new TryCatchBlockNode(tryStart, tryEnd, handler,
                "java/io/IOException"));
        il.add(tryStart);
        il.add(new LdcInsnNode(Type.getObjectType(spec.boot)));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/Class",
                "getResourceAsStream",
                "(Ljava/lang/String;)Ljava/io/InputStream;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, have));
        ule(il, S, msg);
        il.add(have);
        il.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.NEW,
                "java/io/ByteArrayOutputStream"));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(intPush(4096));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/io/ByteArrayOutputStream", "<init>", "(I)V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 2));
        il.add(intPush(8192));
        il.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_BYTE));
        il.add(new VarInsnNode(Opcodes.ASTORE, 3));
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/io/InputStream", "read", "([B)I", false));
        il.add(new VarInsnNode(Opcodes.ISTORE, 4));
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(new JumpInsnNode(Opcodes.IFLE, done));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/io/ByteArrayOutputStream", "write", "([BII)V", false));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(done);
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/io/InputStream", "close", "()V", false));
        il.add(tryEnd);
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/io/ByteArrayOutputStream", "toByteArray", "()[B", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        il.add(handler);
        il.add(new VarInsnNode(Opcodes.ASTORE, 5));
        ule(il, S, msg);
        R.methods.add(m);
        R.used.add("read");
    }

    /** R.<acc>()：抖动后 read(字符串访问器)。 */
    private static void emitPayloadAccessor(Cx R, Cx S, StringItem path,
                                            String accessor) {
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                accessor, "()[B", null, null);
        InsnList il = m.instructions;
        emitChurn(il, R);
        LabelNode dead = new LabelNode();
        LabelNode cont = new LabelNode();
        R.opaqueTrue(il, dead);
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, path.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                R.cn.name, "read", "(Ljava/lang/String;)[B", false));
        il.add(new JumpInsnNode(Opcodes.GOTO, cont));
        il.add(dead);
        il.add(new InsnNode(Opcodes.ACONST_NULL));
        il.add(cont);
        il.add(new InsnNode(Opcodes.ARETURN));
        R.methods.add(m);
        R.used.add(accessor);
    }

    /**
     * M.stage(byte[] pay, int k, String arm, String bind)：
     * 首次调用时 System.load(jar 自身路径)（loader PE 就前置在该文件头，
     * 零临时文件），随后把加密 payload1 交给 mapM 在 native 内存中映射。
     */
    private static void emitMapper(Cx M, Cx R, Cx S, Spec spec,
                                   StringItem msg,
                                   StringItem arm2, StringItem bind2) {
        final String mapDesc = "([BILjava/lang/String;Ljava/lang/String;)I";
        // private static native int mapM / mapM2(byte[], int, String, String)
        MethodNode nat1 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_NATIVE,
                spec.mapM, mapDesc, null, null);
        MethodNode nat2 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_NATIVE,
                spec.mapM2, mapDesc, null, null);
        M.methods.add(nat1);
        M.methods.add(nat2);
        M.used.add(spec.mapM);
        M.used.add(spec.mapM2);

        String flag1 = M.fieldName();
        String flag2 = M.fieldName();
        M.cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, flag1, "I", null, null));
        M.cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, flag2, "I", null, null));

        // ---- stage：自路径 System.load + mapM ----
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                "stage", mapDesc, null, null);
        InsnList il = m.instructions;
        LabelNode tryStart = new LabelNode();
        LabelNode tryEnd = new LabelNode();
        LabelNode call = new LabelNode();
        LabelNode handler = new LabelNode();
        m.tryCatchBlocks.add(new TryCatchBlockNode(tryStart, tryEnd, handler,
                "java/lang/Throwable"));

        il.add(new FieldInsnNode(Opcodes.GETSTATIC, M.cn.name, flag1, "I"));
        il.add(new JumpInsnNode(Opcodes.IFNE, call));
        il.add(tryStart);
        // File f = new File(M.class.getProtectionDomain()
        //                       .getCodeSource().getLocation().toURI());
        il.add(new LdcInsnNode(Type.getObjectType(M.cn.name)));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/Class",
                "getProtectionDomain",
                "()Ljava/security/ProtectionDomain;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/security/ProtectionDomain", "getCodeSource",
                "()Ljava/security/CodeSource;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/security/CodeSource", "getLocation",
                "()Ljava/net/URL;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/net/URL", "toURI", "()Ljava/net/URI;", false));
        il.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.NEW,
                "java/io/File"));
        il.add(new InsnNode(Opcodes.DUP_X1));
        il.add(new InsnNode(Opcodes.SWAP));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/io/File", "<init>", "(Ljava/net/URI;)V", false));
        // System.load(f.getPath()) —— OS 直接把当前 jar（PE 头）映射
        // 进本进程，磁盘上没有任何新增文件
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/io/File",
                "getPath", "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/System",
                "load", "(Ljava/lang/String;)V", false));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, M.cn.name, flag1, "I"));
        il.add(tryEnd);
        il.add(new JumpInsnNode(Opcodes.GOTO, call));
        il.add(handler);
        il.add(new VarInsnNode(Opcodes.ASTORE, 8));
        ule(il, S, msg);

        il.add(call);
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                M.cn.name, spec.mapM, mapDesc, false));
        il.add(new InsnNode(Opcodes.IRETURN));
        M.methods.add(m);
        M.used.add("stage");

        // ---- stage2：按需在内存中映射 payload2（幂等） ----
        MethodNode m2 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                "stage2", "()V", null, null);
        InsnList i2 = m2.instructions;
        LabelNode done = new LabelNode();
        LabelNode ok = new LabelNode();
        i2.add(new FieldInsnNode(Opcodes.GETSTATIC, M.cn.name, flag2, "I"));
        i2.add(new JumpInsnNode(Opcodes.IFNE, done));
        i2.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                R.cn.name, "payload2", "()[B", false));
        i2.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, "deriveKey2", "()I", false));
        i2.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, arm2.accessor, "()Ljava/lang/String;", false));
        i2.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, bind2.accessor, "()Ljava/lang/String;", false));
        i2.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                M.cn.name, spec.mapM2, mapDesc, false));
        i2.add(new InsnNode(Opcodes.ICONST_1));
        i2.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, ok));
        ule(i2, S, msg);
        i2.add(ok);
        i2.add(new InsnNode(Opcodes.ICONST_1));
        i2.add(new FieldInsnNode(Opcodes.PUTSTATIC, M.cn.name, flag2, "I"));
        i2.add(done);
        i2.add(new InsnNode(Opcodes.RETURN));
        M.methods.add(m2);
        M.used.add("stage2");
    }

    /**
     * N.bind(Object cls)：bindM(cls) 三态路由——1 本区已注册；
     * 2 非本区：先 M.stage2() 按需在内存映射镜像2，再 bindM2(cls)；
     * 其余（0/异常）ULE。
     */
    private static void emitBinder(Cx N, Cx M, Cx S, Spec spec,
                                   StringItem msg) {
        MethodNode nat1 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_NATIVE,
                spec.bindM, "(Ljava/lang/Object;)I", null, null);
        MethodNode nat2 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_NATIVE,
                spec.bindM2, "(Ljava/lang/Object;)I", null, null);
        N.methods.add(nat1);
        N.methods.add(nat2);
        N.used.add(spec.bindM);
        N.used.add(spec.bindM2);

        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_FINAL,
                "bind", "(Ljava/lang/Object;)V", null, null);
        InsnList il = m.instructions;
        LabelNode ok = new LabelNode();
        LabelNode route2 = new LabelNode();
        LabelNode bad = new LabelNode();
        // r1 = bindM(cls);  if (r1 == 1) return;
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                N.cn.name, spec.bindM, "(Ljava/lang/Object;)I", false));
        il.add(new VarInsnNode(Opcodes.ISTORE, 1));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, ok));
        // if (r1 != 2) ULE
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ICONST_2));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, route2));
        il.add(new JumpInsnNode(Opcodes.GOTO, bad));
        // M.stage2(); r2 = bindM2(cls); if (r2 == 1) return;
        il.add(route2);
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                M.cn.name, "stage2", "()V", false));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                N.cn.name, spec.bindM2, "(Ljava/lang/Object;)I", false));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, ok));
        il.add(bad);
        ule(il, S, msg);
        il.add(ok);
        il.add(new InsnNode(Opcodes.RETURN));
        N.methods.add(m);
        N.used.add("bind");
    }

    /** B.tie(Class)：平台检查 → stage（System.load 自身 + 映射镜像1）
     *  → 每个 shell 绑定（镜像2 由 bind 路由按需拉起）。 */
    private static void emitTie(Cx B, Cx R, Cx S, Cx M, Cx N,
                                StringItem os, StringItem arch,
                                StringItem win, StringItem a64, StringItem a86,
                                StringItem platMsg, StringItem stageMsg,
                                StringItem arm1, StringItem bind1) {
        String stageF = B.fieldName();
        B.cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_VOLATILE,
                stageF, "I", null, null));

        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_SYNCHRONIZED,
                "tie", "(Ljava/lang/Class;)V", null, null);
        InsnList il = m.instructions;
        LabelNode doInit = new LabelNode();
        LabelNode bindL = new LabelNode();
        LabelNode platOk = new LabelNode();
        LabelNode stageOk = new LabelNode();
        LabelNode bad = new LabelNode();
        LabelNode stageBad = new LabelNode();

        // if (stage != 0) goto bind
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, B.cn.name, stageF, "I"));
        il.add(new JumpInsnNode(Opcodes.IFNE, bindL));
        il.add(doInit);

        // 平台检查
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, os.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/System",
                "getProperty", "(Ljava/lang/String;)Ljava/lang/String;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, arch.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/System",
                "getProperty", "(Ljava/lang/String;)Ljava/lang/String;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 2));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFNULL, bad));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "toLowerCase", "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, win.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "contains", "(Ljava/lang/CharSequence;)Z", false));
        il.add(new JumpInsnNode(Opcodes.IFEQ, bad));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, a64.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "equals", "(Ljava/lang/Object;)Z", false));
        il.add(new JumpInsnNode(Opcodes.IFNE, platOk));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, a86.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "equals", "(Ljava/lang/Object;)Z", false));
        il.add(new JumpInsnNode(Opcodes.IFEQ, bad));

        il.add(platOk);
        // pay = R.payload()
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                R.cn.name, "payload", "()[B", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 3));
        // pk = S.deriveKey()
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, "deriveKey", "()I", false));
        il.add(new VarInsnNode(Opcodes.ISTORE, 4));
        // arm / bind 引用（镜像1 导出符号名）
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, arm1.accessor, "()Ljava/lang/String;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 5));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, bind1.accessor, "()Ljava/lang/String;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 6));
        // r = M.stage(...)
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(new VarInsnNode(Opcodes.ALOAD, 5));
        il.add(new VarInsnNode(Opcodes.ALOAD, 6));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                M.cn.name, "stage",
                "([BILjava/lang/String;Ljava/lang/String;)I", false));
        il.add(new VarInsnNode(Opcodes.ISTORE, 7));
        il.add(new VarInsnNode(Opcodes.ILOAD, 7));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, stageOk));
        il.add(stageBad);
        ule(il, S, stageMsg);
        il.add(stageOk);
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, B.cn.name, stageF, "I"));

        il.add(bindL);
        // 无意义热身：真实 ping native，结果丢掉（也顺带验证 loader 在位）
        il.add(intPush(7));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, "warm", "(I)I", false));
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, B.cn.name, B.seqF, "I"));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, B.cn.name, B.seqF, "I"));
        // N.bind(cls)
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                N.cn.name, "bind", "(Ljava/lang/Object;)V", false));
        il.add(new InsnNode(Opcodes.RETURN));

        il.add(bad);
        ule(il, S, platMsg);

        B.methods.add(m);
        B.used.add("tie");
    }

    private static void ule(InsnList il, Cx S, StringItem msg) {
        il.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.NEW,
                "java/lang/UnsatisfiedLinkError"));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                S.cn.name, msg.accessor, "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/UnsatisfiedLinkError", "<init>",
                "(Ljava/lang/String;)V", false));
        il.add(new InsnNode(Opcodes.ATHROW));
    }

    private static void emitChurn(InsnList il, Cx c) {
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, c.cn.name, c.seqF, "I"));
        il.add(intPush(0x9e37));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(intPush(3));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, c.cn.name, c.seqF, "I"));
    }

    // ------------------------------------------------------------------
    // 屎山填充
    // ------------------------------------------------------------------

    private static void fillJunk(Cx c, Random rnd, int want, int decoys) {
        List<String> smallPool = new ArrayList<String>();
        int made = 0;
        int guard = 0;
        while (made < want && guard++ < want * 4) {
            int kind = rnd.nextInt(7);
            MethodNode mn;
            switch (kind) {
                case 0: mn = junkStorm(c, rnd); break;
                case 1: mn = junkBuilder(c, rnd); break;
                case 2: mn = junkArray(c, rnd); break;
                case 3: mn = junkSwitch(c, rnd); break;
                case 4: mn = junkObject(c, rnd); break;
                case 5: mn = junkChurn(c); break;
                default: mn = junkNested(c, rnd); break;
            }
            if (mn == null) {
                continue;
            }
            c.methods.add(mn);
            if ("(II)I".equals(mn.desc)) {
                smallPool.add(mn.name);
            }
            made++;
        }
        for (int i = 0; i < decoys; i++) {
            MethodNode d = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_NATIVE,
                    c.name(),
                    DECOY_DESCS[rnd.nextInt(DECOY_DESCS.length)], null, null);
            c.methods.add(d);
        }
        // 少量无环互调，让假方法之间形成正常调用图
        for (MethodNode mn : new ArrayList<MethodNode>(c.methods)) {
            if (smallPool.size() < 2 || !"(II)I".equals(mn.desc)
                    || (mn.access & Opcodes.ACC_NATIVE) != 0) {
                continue;
            }
            if (rnd.nextInt(100) >= 45) {
                continue;
            }
            String callee;
            do {
                callee = smallPool.get(rnd.nextInt(smallPool.size()));
            } while (callee.equals(mn.name));
            InsnList extra = new InsnList();
            extra.add(new VarInsnNode(Opcodes.ILOAD, 0));
            extra.add(new VarInsnNode(Opcodes.ILOAD, 1));
            extra.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    c.cn.name, callee, "(II)I", false));
            extra.add(new InsnNode(Opcodes.POP));
            mn.instructions.insertBefore(mn.instructions.getLast(), extra);
        }
    }

    /** (II)I 算术风暴 + 有界循环。 */
    private static MethodNode junkStorm(Cx c, Random rnd) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, n, "(II)I", null, null);
        InsnList il = m.instructions;
        int[] slots = { 3, 4, 5 };
        int[] arith = { Opcodes.IADD, Opcodes.ISUB, Opcodes.IMUL,
                Opcodes.IXOR, Opcodes.IAND, Opcodes.IOR };
        for (int s = 0; s < slots.length; s++) {
            il.add(new VarInsnNode(Opcodes.ILOAD, rnd.nextInt(2)));
            il.add(intPush(1 + rnd.nextInt(999)));
            il.add(new InsnNode(arith[rnd.nextInt(arith.length)]));
            il.add(new VarInsnNode(Opcodes.ISTORE, slots[s]));
        }
        int bound = 2 + rnd.nextInt(6);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 6));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 6));
        il.add(intPush(bound));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        for (int s = 0; s < slots.length; s++) {
            il.add(new VarInsnNode(Opcodes.ILOAD, slots[s]));
            il.add(new VarInsnNode(Opcodes.ILOAD, 6));
            il.add(intPush(3 + rnd.nextInt(29)));
            il.add(new InsnNode(Opcodes.IMUL));
            il.add(new InsnNode(arith[rnd.nextInt(arith.length)]));
            il.add(new VarInsnNode(Opcodes.ISTORE, slots[s]));
        }
        il.add(new org.objectweb.asm.tree.IincInsnNode(6, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, slots[0]));
        il.add(new VarInsnNode(Opcodes.ILOAD, slots[1]));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new VarInsnNode(Opcodes.ILOAD, slots[2]));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** (I)Ljava/lang/String; StringBuilder 循环拼接。 */
    private static MethodNode junkBuilder(Cx c, Random rnd) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, n,
                "(I)Ljava/lang/String;", null, null);
        InsnList il = m.instructions;
        il.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.NEW,
                "java/lang/StringBuilder"));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(intPush(32));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/StringBuilder", "<init>", "(I)V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(intPush(7));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(intPush(2));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new LdcInsnNode(STRING_POOL[rnd.nextInt(STRING_POOL.length)]));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "append",
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;", false));
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "append",
                "(I)Ljava/lang/StringBuilder;", false));
        il.add(new InsnNode(Opcodes.POP));
        il.add(new org.objectweb.asm.tree.IincInsnNode(2, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "toString",
                "()Ljava/lang/String;", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return m;
    }

    /** ([II)I 有界数组求和。 */
    private static MethodNode junkArray(Cx c, Random rnd) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, n, "([II)I", null, null);
        InsnList il = m.instructions;
        LabelNode notNull = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, notNull));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(notNull);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new InsnNode(Opcodes.ARRAYLENGTH));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(intPush(8));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.IALOAD));
        il.add(intPush(3));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new org.objectweb.asm.tree.IincInsnNode(3, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** (I)I TABLESWITCH 假分支。 */
    private static MethodNode junkSwitch(Cx c, Random rnd) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_STATIC, n, "(I)I", null, null);
        InsnList il = m.instructions;
        LabelNode dflt = new LabelNode();
        LabelNode[] cs = new LabelNode[4];
        LabelNode end = new LabelNode();
        for (int i = 0; i < cs.length; i++) {
            cs[i] = new LabelNode();
        }
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(intPush(3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new org.objectweb.asm.tree.TableSwitchInsnNode(0, 3, dflt, cs));
        for (int i = 0; i < cs.length; i++) {
            il.add(cs[i]);
            il.add(new VarInsnNode(Opcodes.ILOAD, 0));
            il.add(intPush(7 + i * 13));
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new JumpInsnNode(Opcodes.GOTO, end));
        }
        il.add(dflt);
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(intPush(101));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(end);
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** (Ljava/lang/Object;)Z 空值/hash 判断。 */
    private static MethodNode junkObject(Cx c, Random rnd) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, n,
                "(Ljava/lang/Object;)Z", null, null);
        InsnList il = m.instructions;
        LabelNode notNull = new LabelNode();
        LabelNode yes = new LabelNode();
        LabelNode no = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, notNull));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(notNull);
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/Object",
                "hashCode", "()I", false));
        il.add(intPush(255));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, yes));
        il.add(no);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(yes);
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** ()V 静态字段抖动。 */
    private static MethodNode junkChurn(Cx c) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, n, "()V", null, null);
        InsnList il = m.instructions;
        emitChurn(il, c);
        LabelNode nonNeg = new LabelNode();
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, c.cn.name, c.seqF, "I"));
        il.add(new JumpInsnNode(Opcodes.IFGE, nonNeg));
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, c.cn.name, c.seqF, "I"));
        il.add(intPush(0x55aa));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, c.cn.name, c.seqF, "I"));
        il.add(nonNeg);
        il.add(new InsnNode(Opcodes.RETURN));
        return m;
    }

    /** (III)I 双层有界循环。 */
    private static MethodNode junkNested(Cx c, Random rnd) {
        String n = c.name();
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, n, "(III)I", null, null);
        InsnList il = m.instructions;
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 4));
        LabelNode oi = new LabelNode();
        LabelNode oe = new LabelNode();
        LabelNode ii = new LabelNode();
        LabelNode ie = new LabelNode();
        il.add(oi);
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(intPush(3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, oe));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 5));
        il.add(ii);
        il.add(new VarInsnNode(Opcodes.ILOAD, 5));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(intPush(3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, ie));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(intPush(7));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 5));
        il.add(intPush(13));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(new org.objectweb.asm.tree.IincInsnNode(5, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, ii));
        il.add(ie);
        il.add(new org.objectweb.asm.tree.IincInsnNode(4, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, oi));
        il.add(oe);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    // ------------------------------------------------------------------

    private static org.objectweb.asm.tree.AbstractInsnNode ldc(int v) {
        if (v >= -1 && v <= 5) {
            return new InsnNode(Opcodes.ICONST_0 + v);
        }
        if (v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE) {
            return new IntInsnNode(Opcodes.BIPUSH, v);
        }
        if (v >= Short.MIN_VALUE && v <= Short.MAX_VALUE) {
            return new IntInsnNode(Opcodes.SIPUSH, v);
        }
        return new LdcInsnNode(Integer.valueOf(v));
    }

    private static org.objectweb.asm.tree.AbstractInsnNode intPush(int v) {
        return ldc(v);
    }
}
