package com.jdobf.core;

import com.jdobf.transform.ControlFlow;
import com.jdobf.transform.ControlFlowFlatten;
import com.jdobf.transform.DecompilerHardening;
import com.jdobf.transform.CrossClassOutliner;
import com.jdobf.transform.DeadClassFactory;
import com.jdobf.transform.InterClassWeaver;
import com.jdobf.transform.MethodSplitter;
import com.jdobf.transform.GuardChain;
import com.jdobf.transform.JunkCode;
import com.jdobf.transform.LocalToField;
import com.jdobf.transform.NumberObfuscation;
import com.jdobf.transform.ShitBloat;
import com.jdobf.transform.StatementOutliner;
import com.jdobf.transform.StripDebug;
import com.jdobf.transform.StringEncryption;
import com.jdobf.transform.Watermarker;
import com.jdobf.j2c.BootImage;
import com.jdobf.j2c.DbpPacker;
import com.jdobf.j2c.J2c;
import com.jdobf.j2c.J2cBuild;
import com.jdobf.j2c.NativeToolchain;
import com.jdobf.j2c.PolyJar;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.commons.ClassRemapper;
import org.objectweb.asm.tree.ClassNode;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * 混淆主流程：
 * 读 jar -> 建类图 -> 全局改名 -> 逐类字节码变换 -> 处理资源/manifest/services -> 写 jar。
 */
public class Obfuscator {

    public interface Listener {
        void log(String message);

        void progress(int done, int total);

        boolean cancelled();
    }

    private static final String SERVICES_PREFIX = "META-INF/services/";
    private static final String VERSIONS_PREFIX = "META-INF/versions/";

    private final ObfConfig cfg;
    private final Listener listener;

    /** 本次运行规整后的水印文本；null 表示不嵌入。 */
    private String watermarkText;

    public Obfuscator(ObfConfig cfg, Listener listener) {
        this.cfg = cfg;
        this.listener = listener != null ? listener : new Listener() {
            public void log(String m) {
            }

            public void progress(int d, int t) {
            }

            public boolean cancelled() {
                return false;
            }
        };
    }

    // ------------------------------------------------------------------
    // jar 条目浏览（供 GUI 建树使用）
    // ------------------------------------------------------------------

    public static class EntryInfo {
        public final String path;
        public final boolean directory;
        public final boolean isClass;
        /** 若为普通 .class 条目，对应内部类名；否则 null */
        public final String classInternal;

        EntryInfo(String path, boolean directory, boolean isClass, String classInternal) {
            this.path = path;
            this.directory = directory;
            this.isClass = isClass;
            this.classInternal = classInternal;
        }
    }

    public static List<EntryInfo> listEntries(String jarPath) throws IOException {
        List<EntryInfo> result = new ArrayList<EntryInfo>();
        ZipFile zf = new ZipFile(jarPath);
        try {
            Enumeration<? extends ZipEntry> en = zf.entries();
            while (en.hasMoreElements()) {
                ZipEntry e = en.nextElement();
                String name = e.getName();
                boolean isClass = !e.isDirectory()
                        && name.endsWith(".class")
                        && !name.endsWith("module-info.class")
                        && !name.endsWith("package-info.class");
                String internal = isClass ? name.substring(0, name.length() - ".class".length()) : null;
                result.add(new EntryInfo(name, e.isDirectory(), isClass, internal));
            }
        } finally {
            zf.close();
        }
        return result;
    }

    // ------------------------------------------------------------------
    // 主流程
    // ------------------------------------------------------------------

    public void run() throws IOException {
        File in = new File(cfg.inputJar);
        File out = new File(cfg.outputJar);
        if (!in.isFile()) {
            throw new IOException("输入 jar 不存在: " + cfg.inputJar);
        }
        if (out.getParentFile() != null) {
            out.getParentFile().mkdirs();
        }
        boolean watermarkOnly = cfg.watermarkEnabled
                && Watermarker.normalize(cfg.watermarkText) != null;
        if (!cfg.anyTransformEnabled() && !watermarkOnly) {
            listener.log("未启用任何混淆选项，直接复制 jar。");
            copyPlain(in, out);
            return;
        }

        long t0 = System.currentTimeMillis();

        // 1. 读入全部条目
        Map<String, byte[]> rawClassBytes = new LinkedHashMap<String, byte[]>();
        Map<String, byte[]> resources = new LinkedHashMap<String, byte[]>();
        readJar(in, rawClassBytes, resources);

        // 2. 解析 ClassNode，确定排除集合
        Map<String, ClassNode> nodes = new LinkedHashMap<String, ClassNode>();
        for (Map.Entry<String, byte[]> e : rawClassBytes.entrySet()) {
            String entryPath = e.getKey();
            if (entryPath.startsWith(VERSIONS_PREFIX)) {
                continue; // 多版本 jar 的版本化类，稍后只做改名
            }
            ClassReader cr = new ClassReader(e.getValue());
            ClassNode cn = new ClassNode(Opcodes.ASM9);
            cr.accept(cn, 0);
            nodes.put(cn.name, cn);
        }
        Set<String> excluded = new TreeSet<String>();
        for (String name : nodes.keySet()) {
            if (cfg.isClassExcluded(name)) {
                excluded.add(name);
            }
        }
        // 内部类 / nest 成员必须与外部类一起排除，否则包级私有/合成访问会跨包断裂
        expandNestExclusions(nodes, excluded);
        listener.log("共读取 " + nodes.size() + " 个类，排除 " + excluded.size() + " 个。");

        // 原始真实类快照（注入伪代码类之前），供类拆分选取捐赠方法
        Set<String> originalRealNames = new LinkedHashSet<String>(nodes.keySet());

        // 每次构建的随机根：默认取运行时熵，令外提选择/字段提升/谓词模板/
        // 环境垃圾片段/随机命名每次构建都不同，避免固定模板被通解；
        // 需要复现同一次构建时可用 -Dcom.jdobf.seed=<n> 固定。
        long obfSeed;
        String seedProp = System.getProperty("com.jdobf.seed");
        if (seedProp != null) {
            obfSeed = Long.parseLong(seedProp.trim());
        } else {
            obfSeed = new Random().nextLong() ^ System.nanoTime()
                    ^ (Runtime.getRuntime().maxMemory() * 0x9E3779B97F4A7C15L);
        }
        listener.log("本次混淆随机种子: " + obfSeed + (seedProp != null ? "（-Dcom.jdobf.seed 固定）" : "（运行时随机）"));

        // 2.5 死代码 / 伪代码类注入：必须在全局改名映射构建之前加入，
        //     伪代码类随后会被同等改名、字符串加密与控制流平坦化，
        //     与真实业务类无法从“是否被混淆”区分
        int deadCount = cfg.deadCodeClasses ? Math.max(0, cfg.deadClassCount) : 0;
        List<String> deadOriginalNames = new ArrayList<String>();
        List<String> guardShellOriginalNames = new ArrayList<String>();
        if (deadCount > 0) {
            // 真实类所在包的加权列表：每个未排除的真实类贡献一个元素
            // （含内部类），大类包因此按比例分到更多伪代码类；
            // 无 '/' 的默认包类贡献空字符串。伪代码类直接进入这些包，
            // 与业务类同目录混杂，绝不新建独立文件夹。
            List<String> realPackages = new ArrayList<String>();
            for (String name : nodes.keySet()) {
                if (excluded.contains(name)) {
                    continue;
                }
                int slash = name.lastIndexOf('/');
                realPackages.add(slash > 0 ? name.substring(0, slash) : "");
            }
            Random deadRandom = new Random(obfSeed ^ 0xDEC0A7L);
            List<ClassNode> dead = DeadClassFactory.generate(deadCount, nodes.keySet(),
                    realPackages, deadRandom);
            for (ClassNode d : dead) {
                nodes.put(d.name, d);
                deadOriginalNames.add(d.name);
            }
            // 完整性暗桩链的分发节点空壳：与伪代码类一起注册进改名/混淆流水线，
            // 保证改名后与业务类命名风格一致；真正的校验入口在所有变换后追加
            int dispatchers = GuardChain.dispatcherCountFor(deadCount);
            List<ClassNode> shells = DeadClassFactory.generateDispatcherShells(
                    dispatchers, nodes.keySet(), realPackages, deadRandom);
            for (ClassNode s : shells) {
                nodes.put(s.name, s);
                guardShellOriginalNames.add(s.name);
            }
            listener.log("注入死代码/伪代码类 " + dead.size()
                    + " 个（含不透明谓词与跨类伪装调用），分发节点空壳 " + dispatchers + " 个");
        }

        // 2.6 类拆分与重定向：把真实类的静态方法迁移进同包伪代码类藏匿，
        //     原方法只留转发桩；必须在全局改名映射构建之前完成，
        //     迁移后的方法与伪代码方法一起被同等改名与后续变换。
        //     计划全部扫描合法后才统一改字节码，任何异常都放弃拆分、保持原样。
        if (cfg.splitRedirect) {
            if (!cfg.deadCodeClasses || deadCount == 0) {
                listener.log("[警告] 类拆分与重定向依赖伪代码类生成，未生成伪代码类，已跳过。");
            } else {
                try {
                    MethodSplitter.Stats splitStats = MethodSplitter.apply(
                            nodes, originalRealNames, excluded,
                            deadOriginalNames, new Random(obfSeed ^ 0x5917L));
                    listener.log("类拆分与重定向：迁移 " + splitStats.movedMethods
                            + " 个真实静态方法到 " + splitStats.carriersUsed
                            + " 个伪代码类中，保留 " + splitStats.decoys
                            + " 个纯诱饵假类（另有 " + splitStats.skippedMethods
                            + " 个方法不满足安全条件保持原位）");
                } catch (RuntimeException se) {
                    listener.log("[警告] 类拆分与重定向执行失败，已保持原方法不变："
                            + se);
                }
            }
        }

        // 3. 建立全局改名映射
        Hierarchy hierarchy = new Hierarchy(nodes, excluded);
        NameGenerator nameGen = new NameGenerator(
                cfg.renameStyle == ObfConfig.RenameStyle.BRAINDEAD
                        ? NameGenerator.Style.BRAINDEAD
                        : NameGenerator.Style.NORMAL,
                obfSeed ^ 0x5DEECE66DL);
        // “更脑残的 rename”下类名含组合附加符号；名字会写进 MANIFEST / services
        // 等纯文本资源的入口/服务类必须保持 ASCII（I/l/1 眼瞎名），
        // 与示例 jar 里 IlIlll... 类 + caobi... 类并存的做法一致
        Set<String> asciiSafeClasses = cfg.renameStyle == ObfConfig.RenameStyle.BRAINDEAD
                ? collectAsciiSafeClasses(resources) : Collections.<String>emptySet();
        if (!asciiSafeClasses.isEmpty()) {
            listener.log("ASCII 安全类（入口/服务，使用 I/l/1 名）: " + asciiSafeClasses.size() + " 个");
        }
        GlobalRemapper remapper = new GlobalRemapper(cfg, hierarchy, nameGen, asciiSafeClasses);
        remapper.build(nodes.values());
        listener.log("重命名：类 " + remapper.renamedClassCount
                + "，方法组 " + remapper.renamedMethodCount
                + "，字段 " + remapper.renamedFieldCount);

        // 4. 改名（ClassRemapper -> 新 ClassNode），构建改名后的类图
        Map<String, ClassNode> renamedNodes = new LinkedHashMap<String, ClassNode>();
        Map<String, byte[]> baselineBytes = new LinkedHashMap<String, byte[]>();
        Set<String> renamedExcluded = new TreeSet<String>();
        for (ClassNode cn : nodes.values()) {
            ClassNode rn = new ClassNode(Opcodes.ASM9);
            cn.accept(new ClassRemapper(rn, remapper));
            renamedNodes.put(rn.name, rn);
            if (excluded.contains(cn.name)) {
                renamedExcluded.add(rn.name);
            }
        }
        Hierarchy renamedHierarchy = new Hierarchy(renamedNodes, renamedExcluded);

        // 4.6 类间交织网络：disperseLogic 开启时，在全局改名完成后、baseline
        //     生成前，向真实业务包注入一组跨包中继类（接口 + 5-7 实现）。
        //     Hierarchy 持有 renamedNodes 同一引用，随后 COMPUTE_FRAMES
        //     与 typeLoader 都能解析它们；中继类自身跳过全部逐类变换。
        InterClassWeaver.Network weaveNetwork = null;
        Set<String> weaveRelayNames = new HashSet<String>();
        if (cfg.disperseLogic) {
            List<String> realPackages = new ArrayList<String>();
            for (ClassNode rn : renamedNodes.values()) {
                if (renamedExcluded.contains(rn.name)) {
                    continue;
                }
                int slash = rn.name.lastIndexOf('/');
                realPackages.add(slash > 0 ? rn.name.substring(0, slash) : "");
            }
            weaveNetwork = InterClassWeaver.build(renamedNodes.values(), realPackages,
                    new Random(obfSeed ^ 0xC1A55E77L));
            for (ClassNode rc : weaveNetwork.nodes) {
                renamedNodes.put(rc.name, rc);
                weaveRelayNames.add(rc.name);
            }
            listener.log("类间交织网络：注入 " + weaveNetwork.relayClassCount()
                    + " 个跨包中继类（恒等编码链/接口多态/ThreadLocal/互递归），"
                    + "不透明谓词改为跨类取值");
        }

        // 4.5 数字水印：写入改名后节点的 SourceFile（常量池首批 UTF8，
        //     hex 打开即在文件顶部），此后所有渲染路径（基线/变换/回退/
        //     GuardChain 重渲染）都会把它写进 class，暗桩 CRC 一并覆盖
        watermarkText = null;
        if (cfg.watermarkEnabled) {
            watermarkText = Watermarker.normalize(cfg.watermarkText);
            if (watermarkText != null) {
                Watermarker.attach(renamedNodes.values(), watermarkText);
                listener.log("数字水印：已向全部 " + renamedNodes.size()
                        + " 个类嵌入水印（" + watermarkText + "）");
            } else {
                listener.log("[警告] 水印文本为空，跳过数字水印。");
            }
        }

        // 5. 先产出每个类的“仅改名基线字节码”，作为变换失败时的回退
        for (ClassNode rn : renamedNodes.values()) {
            try {
                baselineBytes.put(rn.name, writeClassNode(rn, renamedHierarchy));
            } catch (Throwable t) {
                listener.log("[警告] 基线生成失败，将使用原始字节码: " + rn.name + " -> " + t);
                String oldName = remapper.reverseMap(rn.name);
                byte[] raw = rawClassBytes.get(oldName + ".class");
                if (raw == null) {
                    raw = rawClassBytes.get(oldName);
                }
                if (raw != null) {
                    baselineBytes.put(rn.name, raw);
                }
            }
        }

        // 平坦化的局部变量提升需要解析 jar 内类型，提供基于改名字节码的 ClassLoader
        ClassLoader typeLoader = new BytesClassLoader(getClass().getClassLoader(), baselineBytes);

        // 5.5 跨类代码派分（全局，逐类变换之前）：把方法体在栈空边界切成
        //     直线片段，随机派发到其他类新生成的 public static(Object[]) 方法，
        //     局部变量经 Object[] 装箱桥接，原方法体只剩跨类调用链。外提方法
        //     随宿主类走完整逐类变换（字符串/数字混淆、垃圾、状态机平坦化、
        //     谓词），关键逻辑被拆碎散落到数十个类中。先全量规划再统一改写，
        //     任何异常整体放弃，节点保持原样
        Set<String> outlineHostNames = new HashSet<String>();
        Set<String> outlineSinkSide = null;
        // j2c 放松名单（伪代码假类最终名）外提隔离探测就要用，提前构造
        Set<String> j2cRelaxed = new HashSet<String>();
        j2cRelaxed.addAll(mapFinalNames(remapper, deadOriginalNames));
        if (cfg.disperseLogic) {
            try {
                Set<String> outlineSkip = new HashSet<String>();
                outlineSkip.addAll(renamedExcluded);
                outlineSkip.addAll(weaveRelayNames);
                outlineSkip.addAll(mapFinalNames(remapper, guardShellOriginalNames));
                // 伪代码/诱饵类只能做宿主（业务片段藏入其中），不能做源：
                // 其合成方法体从不被执行、从未经 JVM 验证，槽位生命周期
                // 不可作为帧分析依据（迁移进来的真实方法一并保守排除）
                Set<String> hostAllowed = new HashSet<String>();
                hostAllowed.addAll(mapFinalNames(remapper, guardShellOriginalNames));
                hostAllowed.addAll(mapFinalNames(remapper, deadOriginalNames));
                outlineSkip.addAll(hostAllowed);
                if (!Boolean.getBoolean("jdobf.xo.off")) {
                // j2c 开启时先探测下沉集合，外提按"源/宿主同处下沉侧或同处
                // 明文侧"隔离派发，避免 $$n 对象跨隐藏/明文边界 ClassCastException
                Set<String> sinkSide = null;
                if (cfg.j2c) {
                    try {
                        Set<String> probeSkip = new HashSet<String>();
                        probeSkip.addAll(renamedExcluded);
                        probeSkip.addAll(weaveRelayNames);
                        J2c.Plan probe = J2c.plan(renamedNodes.values(), probeSkip,
                                j2cRelaxed, resolveMainClass(remapper, resources),
                                new Random(obfSeed ^ 0x9E3779B9L));
                        sinkSide = new HashSet<String>(probe.classes.keySet());
                    } catch (Throwable pt) {
                        listener.log("[警告] j2c 下沉集合探测失败，外提按不隔离执行："
                                + pt.getMessage());
                    }
                }
                CrossClassOutliner.Stats xs = CrossClassOutliner.apply(
                        renamedNodes.values(), outlineSkip, hostAllowed, sinkSide,
                        typeLoader, new Random(obfSeed ^ 0xC0551A7L));
                if (xs.segments > 0) {
                    listener.log("跨类代码派分：" + xs);
                }
                outlineHostNames.addAll(xs.hostNames);
                outlineSinkSide = sinkSide;
                }
            } catch (Throwable t) {
                listener.log("[警告] 跨类代码派分执行失败，已保持原方法不变：" + t);
            }
        }

        // 6. 逐类做字节码变换（根随机种子 obfSeed 已在流程早期确定并记录）
        Random random = new Random(obfSeed ^ 0x1234ABCDL);
        // 屎山只灌真实业务类；生成的伪代码类/分发壳本身已是诱饵，不再灌屎，
        // 避免平坦化对数千个假方法做全方法分析导致耗时失控
        Set<String> shitSkipNames = new HashSet<String>();
        shitSkipNames.addAll(mapFinalNames(remapper, deadOriginalNames));
        shitSkipNames.addAll(mapFinalNames(remapper, guardShellOriginalNames));

        // 6.0 j2c：环境预检查 + 下沉规划（在逐类变换前确定，捕获在变换后进行）
        boolean j2cActive = false;
        J2c.Plan j2cPlan = null;
        BootImage.Spec j2cSpec = null;
        BootImage.Art j2cArt = null;
        final Map<String, byte[]> j2cFullBytes = new LinkedHashMap<String, byte[]>();
        // 放松名单：伪代码假类最终名。它们允许自带静态字段（SEED/TAG），
        // shell 化时全空心（字段/实例方法删除），假逻辑整体进 DLL
        if (cfg.j2c) {
            try {
                NativeToolchain.Toolchain toolchain = NativeToolchain.preflight();
                Set<String> j2cSkip = new HashSet<String>();
                j2cSkip.addAll(renamedExcluded);
                j2cSkip.addAll(weaveRelayNames);
                // 仅明文侧实际承载过外提片段的宿主强制留明文（下沉侧宿主
                // 本就计划下沉，外提方法随 blob 一起隐藏，不能 skip）
                if (outlineSinkSide != null) {
                    for (String h : outlineHostNames) {
                        if (!outlineSinkSide.contains(h)) {
                            j2cSkip.add(h);
                        }
                    }
                } else {
                    j2cSkip.addAll(outlineHostNames);
                }
                String j2cMain = resolveMainClass(remapper, resources);
                j2cPlan = J2c.plan(renamedNodes.values(), j2cSkip, j2cRelaxed,
                        j2cMain, random);
                if (outlineSinkSide != null) {
                    // 隔离一致性：下沉侧宿主在外提后不得被正式规划甩出计划
                    int dropped = 0;
                    for (String h : outlineHostNames) {
                        if (outlineSinkSide.contains(h)
                                && !j2cPlan.classes.containsKey(h)) {
                            dropped++;
                        }
                    }
                    if (dropped > 0) {
                        listener.log("[警告] " + dropped
                                + " 个外提宿主被 j2c 护栏甩出下沉计划，"
                                + "建议关闭跨类派分或 j2c 后重试运行。");
                    }
                }
                if (j2cPlan.isEmpty()) {
                    listener.log("[警告] j2c 已开启，但没有满足安全护栏的类/方法，已跳过。");
                } else {
                    j2cSpec = BootImage.plan(
                            chooseBridgeNames(renamedNodes, rawClassBytes, random),
                            random);
                    j2cActive = true;
                    int fakeInPlan = 0;
                    for (String name : j2cPlan.classes.keySet()) {
                        if (j2cRelaxed.contains(name)) {
                            fakeInPlan++;
                        }
                    }
                    listener.log("j2c 预检查通过（" + toolchain.describe()
                            + "），计划把 " + j2cPlan.methodCount() + " 个方法下沉到 "
                            + j2cPlan.classes.size() + " 个隐藏类（含伪代码假类 "
                            + fakeInPlan + " 个）");
                    if (j2cRelaxed.size() > fakeInPlan) {
                        listener.log("[警告] 伪代码假类数量超出 j2c 单批上限 "
                                + J2c.FAKE_CAP + "，其余 "
                                + (j2cRelaxed.size() - fakeInPlan)
                                + " 个假类保留为普通混淆类。");
                    }
                }
            } catch (Throwable jt) {
                listener.log("[警告] j2c 环境预检查失败，已跳过该选项："
                        + jt.getMessage());
            }
        }

        Map<String, byte[]> finalClassBytes = new LinkedHashMap<String, byte[]>();
        int total = renamedNodes.size();
        int done = 0;
        listener.progress(0, total);
        for (ClassNode rn : renamedNodes.values()) {
            if (listener.cancelled()) {
                listener.log("用户取消。");
                return;
            }
            // 逐类上报进度（早期版本每 25 类才上报，首个大类变换耗时长时
            // 界面长期显示“卡在 0”）；同时记录异常慢的类便于定位
            long classT0 = System.currentTimeMillis();
            boolean wasExcluded = renamedExcluded.contains(rn.name);
            byte[] bytes;
            if (wasExcluded) {
                bytes = baselineBytes.get(rn.name);
            } else {
                bytes = transformNode(rn, renamedHierarchy, baselineBytes.get(rn.name), random,
                        typeLoader, shitSkipNames, weaveNetwork);
            }
            if (bytes == null) {
                bytes = baselineBytes.get(rn.name);
            }
            finalClassBytes.put(rn.name, bytes);
            done++;
            long classMs = System.currentTimeMillis() - classT0;
            if (classMs > 3000L) {
                listener.log("慢类 " + rn.name + " 变换耗时 " + classMs / 1000.0 + "s");
            }
            listener.progress(done, total);
        }

        // 6.5 j2c：混淆全部完成后，再把真实逻辑 + 40 个屎山假方法 + 伪代码假类
        //     一起下沉进 DLL（先混淆、后 j2c）：
        //       灌假方法(副本) -> 捕获完整混淆字节 -> 编码隐藏类 -> 编译 DLL
        //       -> 基于副本生成 shell（原节点不动） -> GuardChain 覆盖最终 shell。
        //     任一步失败：原节点/字节均未被污染，恢复快照后等价于未开启 j2c。
        if (j2cActive) {
            Map<String, byte[]> preJ2cBytes = new LinkedHashMap<String, byte[]>();
            try {
                int decoyTotal = 0;
                for (J2c.ClassPlan cp : j2cPlan.classes.values()) {
                    preJ2cBytes.put(cp.cn.name, finalClassBytes.get(cp.cn.name));
                    if (cp.extract.isEmpty() && !j2cRelaxed.contains(cp.cn.name)) {
                        // 簇内纯依赖成员：不灌诱饵、不 shell 化，仅作为隐藏类复活
                        j2cFullBytes.put(cp.cn.name, finalClassBytes.get(cp.cn.name));
                        continue;
                    }
                    // 在副本上灌屎山假方法海：假方法体随完整字节进隐藏 blob，
                    // shell 中它们只保留 native 声明
                    ClassNode full = new ClassNode(Opcodes.ASM9);
                    cp.cn.accept(full);
                    ShitBloat.Stats st = ShitBloat.floodMethods(
                            full, random, J2c.DECOY_METHODS);
                    for (org.objectweb.asm.tree.MethodNode fm : st.fakes) {
                        cp.extract.add(new String[] { fm.name, fm.desc });
                    }
                    decoyTotal += st.fakeMethods;
                    cp.full = full;
                    j2cFullBytes.put(cp.cn.name,
                            writeClassNode(full, renamedHierarchy));
                }

                Map<String, byte[]> hidden =
                        J2c.encodeHidden(j2cPlan, j2cFullBytes);
                // 双 DLL：payload（含隐藏类 blob）加密入 jar 永不落地；
                // 通用 loader 加密入 jar，运行时短暂落地
                boolean vmpAvailable = com.jdobf.j2c.VmpPacker.available();
                boolean dbpAvailable = DbpPacker.available();
                boolean vmpWanted = cfg.vmpPack && vmpAvailable;
                boolean dbpWanted = cfg.dbpPack && dbpAvailable && !vmpWanted;
                if (cfg.vmpPack && cfg.dbpPack) {
                    listener.log("[警告] VMProtect 与 DoubaoProtect 加壳互斥，"
                            + (vmpWanted ? "已优先使用 VMProtect。"
                                    : dbpWanted ? "已改用 DoubaoProtect。"
                                            : "两者当前均不可用，回退为普通 j2c。"));
                }
                if (cfg.vmpPack && !vmpWanted && !dbpWanted) {
                    listener.log("[警告] VMProtect 加壳仅支持 Windows x64 且需要内置"
                            + "加壳器，本次构建回退为普通 j2c。");
                }
                if (cfg.dbpPack && !dbpWanted && !vmpWanted) {
                    listener.log("[警告] DoubaoProtect 加壳仅支持 Windows x64 且需要内置"
                            + "加壳器/运行时，本次构建回退为普通 j2c。");
                }
                if (vmpWanted) {
                    listener.log("VMProtect 加壳已启用：虚拟化+变异标记覆盖全部下沉"
                            + "函数，开启打包/反调试/内存保护（关闭反虚拟机与内核检测）。");
                } else if (dbpWanted) {
                    listener.log("DoubaoProtect 加壳已启用：Ultra/变异标记覆盖"
                            + "全部下沉函数，嵌入 DoubaoRT 运行时（默认关闭反虚拟机）。");
                }
                j2cArt = J2cBuild.build(j2cSpec, j2cPlan, hidden, random,
                        listener, new HashSet<String>(resources.keySet()),
                        cfg.j2cNativeName, vmpWanted, dbpWanted);

                // DLL 编译成功后再生成 shell（假类全空心），替换节点映射，
                // 使随后的 GuardChain 直接在 shell 上挂暗桩（CRC 覆盖最终字节）
                for (J2c.ClassPlan cp : j2cPlan.classes.values()) {
                    if (cp.full == null) {
                        continue;
                    }
                    ClassNode shell = J2c.shell(cp, j2cSpec.boot, random,
                            j2cRelaxed.contains(cp.cn.name));
                    renamedNodes.put(cp.cn.name, shell);
                    finalClassBytes.put(cp.cn.name,
                            writeClassNode(shell, renamedHierarchy));
                }
                // 两个 payload 均以加密资源入 jar（XOR 高熵），运行时由
                // loader 在 native 内存中手动映射，全程零落地
                resources.put(j2cArt.entry1, j2cArt.enc1);
                resources.put(j2cArt.entry2, j2cArt.enc2);
                Map<String, byte[]> bridge =
                        BootImage.generate(j2cSpec, j2cArt, random);
                for (Map.Entry<String, byte[]> bc : bridge.entrySet()) {
                    finalClassBytes.put(bc.getKey(), bc.getValue());
                }
                listener.log("  j2c 原生下沉完成：" + j2cPlan.methodCount()
                        + " 个方法（含 " + decoyTotal + " 个屎山假方法）-> "
                        + j2cPlan.classes.size()
                        + " 个隐藏类，拆分为 2 个 payload（镜像2 按需映射）；"
                        + "payload1 " + j2cArt.enc1.length / 1024
                        + " KB / payload2 " + j2cArt.enc2.length / 1024
                        + " KB 均为 XOR 加密态、不落地；loader PE "
                        + j2cArt.loaderPlain.length / 1024
                        + " KB 前置 jar 文件头，System.load 自身路径零临时文件");
            } catch (Throwable jt) {
                listener.log("[警告] j2c 构建失败，已回退为普通混淆产物：" + jt);
                for (J2c.ClassPlan cp : j2cPlan.classes.values()) {
                    byte[] pre = preJ2cBytes.get(cp.cn.name);
                    if (pre != null) {
                        finalClassBytes.put(cp.cn.name, pre);
                    }
                    // 节点映射恢复为未 shell 化的原混淆节点
                    renamedNodes.put(cp.cn.name, cp.cn);
                    cp.full = null;
                }
                if (j2cArt != null) {
                    resources.remove(j2cArt.entry1);
                    resources.remove(j2cArt.entry2);
                    j2cArt = null;
                }
                for (String bn : j2cSpec.all()) {
                    finalClassBytes.remove(bn);
                }
            }
        }

        // 6.6 完整性暗桩链：把全部伪代码类、分发节点与 Main 入口串联。
        //     必须在 j2c 之后（prime/run 直接挂在 shell 上，CRC 覆盖最终 shell
        //     字节；隐藏类不含 prime，DLL 此时已构建完毕不再读 class 字节）。
        if (!deadOriginalNames.isEmpty()) {
            String mainFinal = resolveMainClass(remapper, resources);
            if (mainFinal == null) {
                listener.log("[警告] MANIFEST 未声明 Main-Class，无法挂接完整性暗桩链，已跳过。");
            } else {
                List<String> chain = mapFinalNames(remapper, deadOriginalNames);
                List<String> dispatchers = mapFinalNames(remapper, guardShellOriginalNames);
                final Hierarchy guardHierarchy = renamedHierarchy;
                GuardChain.install(chain, dispatchers, mainFinal,
                        renamedNodes, finalClassBytes, baselineBytes,
                        new Random(obfSeed ^ 0x6A2D5A5L),
                        new GuardChain.Renderer() {
                            public byte[] render(ClassNode cn) {
                                return writeClassNode(cn, guardHierarchy);
                            }
                        },
                        new GuardChain.Log() {
                            public void log(String message) {
                                listener.log(message);
                            }
                        });
            }
        }

        // 7. 多版本条目：仅改名，不做高级变换
        Map<String, byte[]> versionedOutput = new LinkedHashMap<String, byte[]>();
        for (Map.Entry<String, byte[]> e : rawClassBytes.entrySet()) {
            if (!e.getKey().startsWith(VERSIONS_PREFIX)) {
                continue;
            }
            try {
                ClassReader cr = new ClassReader(e.getValue());
                ClassWriter cw = new SafeClassWriter(renamedHierarchy);
                ClassVisitor sink = watermarkText != null
                        ? Watermarker.visitor(cw, watermarkText) : cw;
                cr.accept(new ClassRemapper(sink, remapper), 0);
                versionedOutput.put(e.getKey(), cw.toByteArray());
            } catch (Throwable t) {
                listener.log("[警告] 版本化类处理失败，保留原字节: " + e.getKey() + " -> " + t);
                versionedOutput.put(e.getKey(), e.getValue());
            }
        }

        // 8. 写 jar（manifest / services / 资源 / 类）
        writeOutput(in, out, resources, finalClassBytes, versionedOutput, remapper);

        // 8.1 j2c：把明文 loader PE 前置到 jar 文件头，并重定位全部 zip
        //     中央目录偏移，得到 PE/ZIP 多态文件：java -jar 仍照常运行；
        //     运行时 M.stage 对自身路径 System.load，OS 直接把这个文件
        //     头部的 PE 映射进进程——不产生任何临时文件
        if (j2cArt != null) {
            PolyJar.prefixPe(out, j2cArt.loaderPlain);
            listener.log("  多态 jar 完成：loader PE(" + j2cArt.loaderPlain.length
                    + " B) 已前置，ZIP 偏移同步重定位；运行时零落地");
        }

        // 9. 可选：导出重命名映射表
        if (cfg.exportMapping && (cfg.renameClasses || cfg.renameMethods || cfg.renameFields)) {
            String outName = out.getName();
            int dot = outName.lastIndexOf('.');
            String base = dot > 0 ? outName.substring(0, dot) : outName;
            File mapFile = new File(out.getParentFile(), base + "-mapping.txt");
            Writer w = new OutputStreamWriter(new FileOutputStream(mapFile), "UTF-8");
            try {
                remapper.writeMapping(w);
            } finally {
                w.close();
            }
            listener.log("映射表: " + mapFile.getAbsolutePath());
        }

        listener.progress(total, total);
        listener.log("完成，耗时 " + (System.currentTimeMillis() - t0) / 1000.0 + "s");
        listener.log("输出: " + out.getAbsolutePath());
    }

    private void readJar(File in, Map<String, byte[]> classes, Map<String, byte[]> resources)
            throws IOException {
        ZipFile zf = new ZipFile(in);
        try {
            Enumeration<? extends ZipEntry> en = zf.entries();
            while (en.hasMoreElements()) {
                ZipEntry e = en.nextElement();
                if (e.isDirectory()) {
                    continue;
                }
                byte[] data = readAll(zf, e);
                if (e.getName().endsWith(".class")) {
                    classes.put(e.getName(), data);
                } else {
                    resources.put(e.getName(), data);
                }
            }
        } finally {
            zf.close();
        }
    }

    private static byte[] readAll(ZipFile zf, ZipEntry e) throws IOException {
        InputStream is = zf.getInputStream(e);
        try {
            ByteArrayOutputStream bos = new ByteArrayOutputStream(Math.max(32, (int) e.getSize()));
            byte[] buf = new byte[8192];
            int r;
            while ((r = is.read(buf)) != -1) {
                bos.write(buf, 0, r);
            }
            return bos.toByteArray();
        } finally {
            is.close();
        }
    }

    private byte[] writeClassNode(ClassNode cn, Hierarchy h) {
        ClassWriter cw = new SafeClassWriter(h);
        cn.accept(cw);
        return cw.toByteArray();
    }

    private byte[] transformNode(ClassNode cn, Hierarchy h, byte[] baseline, Random random,
                                 ClassLoader typeLoader, Set<String> shitSkipNames,
                                 InterClassWeaver.Network weaveNetwork) {
        try {
            boolean shitAllowed = cfg.shitBloat && !shitSkipNames.contains(cn.name);
            if (cfg.stripDebug) {
                StripDebug.apply(cn);
            }
            // 水印写在 SourceFile 上，剥离调试信息后必须补回
            if (watermarkText != null) {
                cn.sourceFile = Watermarker.sourceName(watermarkText);
            }
            // 类间交织中继类是手工构造的混淆态代码，跳过字符串/屎山/网络
            // 谓词等逐类变换（自指无意义且有类初始化耦合），但其编码链/
            // 解密原语方法本身就是反破解目标（被看懂即可复现通用脱密器），
            // Network 构建时方法体已定型（weave 只引用不改写），对其补跑
            // 一次平坦化，让中继方法同样进入三寄存器状态机
            if (weaveNetwork != null && weaveNetwork.isRelay(cn.name)) {
                if (cfg.flattenControlFlow) {
                    int n = ControlFlowFlatten.apply(cn, random, typeLoader);
                    if (n > 0) {
                        listener.log("  中继类平坦化 " + n + " 个方法: " + cn.name);
                    }
                }
                // 中继类也属于输出字节码的可见攻击面。它们不能参与前面的
                // 字符串/交织变换，但可以安全接受最后一层结构扰动。
                if (cfg.decompilerHardening && cfg.decompilerHardeningPasses > 0) {
                    int n = DecompilerHardening.apply(cn, random,
                            Math.max(1, Math.min(3, cfg.decompilerHardeningPasses)));
                    if (n > 0) {
                        listener.log("  中继类反编译器抗性增强 " + n
                                + " 个方法: " + cn.name);
                    }
                }
                return writeClassNode(cn, h);
            }
            if (cfg.encryptStrings) {
                int n = StringEncryption.apply(cn, random);
                if (n > 0) {
                    listener.log("  字符串加密 " + n + " 处: " + cn.name);
                }
            }
            if (cfg.obfuscateNumbers) {
                NumberObfuscation.apply(cn, random);
            }
            if (cfg.disperseLogic) {
                // 先局部变量字段化（更多语句随后满足"只碰字段"的外提条件），
                // 再语句外提打散逻辑聚集，最后在真实方法锚点插入真实 JDK
                // 环境调用垃圾，业务外部调用不再被纯算术衬托
                int promoted = LocalToField.apply(cn, random, typeLoader);
                int outlined = StatementOutliner.apply(cn, random);
                if (promoted + outlined > 0) {
                    listener.log("  逻辑分散 字段化 " + promoted + " 槽/外提 "
                            + outlined + " 语句: " + cn.name);
                }
            }
            if (cfg.junkCode && cfg.junkMethodsPerClass > 0) {
                JunkCode.apply(cn, random, cfg.junkMethodsPerClass);
            }
            // 屎山阶段一：假方法海（在平坦化前注入，让带跳转的假方法
            // 也被纳入状态机，真假同构）
            ShitBloat.Stats shitStats = null;
            if (shitAllowed && cfg.shitMethodsPerClass > 0) {
                shitStats = ShitBloat.floodMethods(cn, random, cfg.shitMethodsPerClass);
                if (shitStats.fakeMethods > 0) {
                    listener.log("  屎山注入 " + shitStats.fakeMethods
                            + " 个脑残假方法: " + cn.name);
                }
            }
            // 平坦化最后执行：不透明谓词、垃圾方法的控制流也会被纳入状态机
            if (cfg.flattenControlFlow) {
                int n = ControlFlowFlatten.apply(cn, random, typeLoader);
                if (n > 0) {
                    listener.log("  控制流平坦化 " + n + " 个方法: " + cn.name);
                }
            }
            // 屎山阶段二：真实方法体内灌屎（必须在平坦化之后，只在栈空
            // 安全点插入栈中性片段，不破坏状态机）
            if (shitStats != null) {
                int snippets = ShitBloat.floodInline(cn, random, shitStats);
                if (snippets > 0) {
                    listener.log("  屎山灌入真实方法 " + snippets
                            + " 段脑残代码: " + cn.name);
                }
            }
            // 环境调用垃圾与不透明谓词守卫都必须在平坦化/屎山之后注入：
            // 它们引用方法级垃圾槽，若先于平坦化插入，槽初始化序言会被
            // 状态机切碎进独立 case，与引用点失去支配关系，触发 VerifyError。
            // 顺序上 env 先于守卫：否则守卫的"语义死块"在字节码层面仍可达，
            // env 会把 API 片段插进死块；env 先跑时方法里只有真实路径锚点。
            if (cfg.disperseLogic) {
                int env = JunkCode.injectEnvIntoMethods(cn, random);
                if (env > 0) {
                    listener.log("  环境调用垃圾 " + env + " 段: " + cn.name);
                }
            }
            // 数据流强绑定必须先于类间交织注入：此处改写业务常量/算术/局部
            // 槽时，weave 的垃圾槽与 ControlFlow 的谓词槽尚未分配，槽位扫描
            // 不会把合成槽误当业务槽；后续 weave/ControlFlow 都在其结果之上工作
            if (weaveNetwork != null) {
                int[] bound = com.jdobf.transform.DataFlowBinder.bind(
                        cn, weaveNetwork, random);
                if (bound[0] + bound[1] + bound[2] > 0) {
                    listener.log("  数据流绑定 常量解密 " + bound[0]
                            + " / MBA 代换 " + bound[1]
                            + " / 局部加密槽 " + bound[2] + ": " + cn.name);
                }
            }
            // 类间交织注入必须同样在平坦化/屎山之后：片段引用的垃圾槽
            // 序言不能被状态机切碎；env 先于交织，避免 API 片段落入死块
            if (weaveNetwork != null) {
                int woven = weaveNetwork.weave(cn, random);
                if (woven > 0) {
                    listener.log("  类间交织注入 " + woven + " 段: " + cn.name);
                }
            }
            if (cfg.controlFlow && cfg.controlFlowPasses > 0) {
                ControlFlow.apply(cn, random,
                        Math.max(1, Math.min(3, cfg.controlFlowPasses)), weaveNetwork);
            }
            // 最后一层结构扰动：在所有业务/垃圾控制流已经定型后再加稀疏
            // switch 入口与不可达异常岛，避免被后续平坦化重新规整。
            if (cfg.decompilerHardening && cfg.decompilerHardeningPasses > 0) {
                int n = DecompilerHardening.apply(cn, random,
                        Math.max(1, Math.min(3, cfg.decompilerHardeningPasses)));
                if (n > 0) {
                    listener.log("  反编译器抗性增强 " + n + " 个方法: " + cn.name);
                }
            }
            return writeClassNode(cn, h);
        } catch (Throwable t) {
            listener.log("[警告] 高级变换失败，回退到仅改名字节码: " + cn.name + " -> " + t);
            return baseline;
        }
    }

    /**
     * 按嵌套关系扩张排除集合：
     * 依据 1) nestHost 属性；2) InnerClasses 属性中的 outer/inner；3) "$" 命名约定。
     * 只要同一 nest 中有一个成员被排除，整个 nest 全部排除。
     */
    private void expandNestExclusions(Map<String, ClassNode> nodes, Set<String> excluded) {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (ClassNode cn : nodes.values()) {
                if (excluded.contains(cn.name)) {
                    continue;
                }
                boolean linkedExcluded = false;
                if (cn.nestHostClass != null && excluded.contains(cn.nestHostClass)) {
                    linkedExcluded = true;
                }
                if (!linkedExcluded && cn.outerClass != null && excluded.contains(cn.outerClass)) {
                    linkedExcluded = true;
                }
                if (!linkedExcluded && cn.innerClasses != null) {
                    for (org.objectweb.asm.tree.InnerClassNode ic : cn.innerClasses) {
                        if (ic.name.equals(cn.name) && ic.outerName != null
                                && excluded.contains(ic.outerName)) {
                            linkedExcluded = true;
                            break;
                        }
                        if (ic.outerName != null && ic.outerName.equals(cn.name)
                                && excluded.contains(ic.name)) {
                            linkedExcluded = true;
                            break;
                        }
                    }
                }
                if (!linkedExcluded) {
                    // "$" 命名约定（javac 内部类），覆盖属性缺失的极端情况
                    int dollar = cn.name.indexOf('$');
                    while (dollar > 0 && !linkedExcluded) {
                        if (excluded.contains(cn.name.substring(0, dollar))) {
                            linkedExcluded = true;
                        }
                        dollar = cn.name.indexOf('$', dollar + 1);
                    }
                }
                if (linkedExcluded) {
                    excluded.add(cn.name);
                    listener.log("嵌套联动排除: " + cn.name);
                    changed = true;
                }
            }
        }
    }

    /** 把原始内部名列表映射为最终内部名（未开启类改名时保持原名）。 */
    private static List<String> mapFinalNames(GlobalRemapper remapper, List<String> originals) {
        List<String> out = new ArrayList<String>();
        for (String orig : originals) {
            String mapped = remapper.classMap().get(orig);
            out.add(mapped != null ? mapped : orig);
        }
        return out;
    }

    /**
     * 分配 5 个互不冲突、外观普通的桥簇类内部名（全局改名已结束）。
     * 包名/类名每构建随机选取：落地 loader 的 JNI 导出符号随之变化，
     * 复制走临时文件也无法据此识别固定桥接结构。
     */
    private static final String[] BRIDGE_PACKAGES = {
            "codec/base", "io/chunk", "rt/buffer", "core/seq",
            "org/jc/base", "util/seq",
    };
    private static final String[] BRIDGE_CLASSES = {
            "ChunkTable", "SeqBuffer", "ByteCache", "CodecUtil", "ResourceChunk",
            "TableBuffer", "IndexCache", "StreamKit", "MapBuffer", "Holder",
            "Values", "Tables", "Buffers", "Sources", "Digests",
    };

    private static String[] chooseBridgeNames(Map<String, ClassNode> renamedNodes,
                                              Map<String, byte[]> rawClassBytes,
                                              Random random) {
        List<String> packages = new ArrayList<String>();
        for (String p : BRIDGE_PACKAGES) {
            packages.add(p);
        }
        Collections.shuffle(packages, random);
        List<String> simple = new ArrayList<String>();
        for (String c : BRIDGE_CLASSES) {
            simple.add(c);
        }
        Collections.shuffle(simple, random);
        for (String pkg : packages) {
            List<String> picked = new ArrayList<String>();
            for (String s : simple) {
                String c = pkg + "/" + s;
                if (renamedNodes.containsKey(c)
                        || rawClassBytes.containsKey(c + ".class")) {
                    continue;
                }
                picked.add(c);
                if (picked.size() == 5) {
                    return picked.toArray(new String[5]);
                }
            }
        }
        throw new IllegalStateException("j2c: 无法分配 5 个桥簇类名");
    }

    /**
     * 收集名字会落入纯文本资源（MANIFEST.MF / META-INF/services）的类内部名。
     * BRAINDEAD 风格下这些类必须使用 ASCII 简单名，避免资源文件 Unicode
     * 编码差异导致入口类/服务发现失败。
     */
    private Set<String> collectAsciiSafeClasses(Map<String, byte[]> resources) throws IOException {
        Set<String> safe = new TreeSet<String>();
        byte[] manifestBytes = resources.get("META-INF/MANIFEST.MF");
        if (manifestBytes != null) {
            Manifest manifest = new Manifest();
            manifest.read(new java.io.ByteArrayInputStream(manifestBytes));
            Attributes main = manifest.getMainAttributes();
            String[] manifestClassAttrs = {
                    Attributes.Name.MAIN_CLASS.toString(),
                    "Launcher-Agent-Class", "Premain-Class", "Agent-Class"
            };
            for (String attr : manifestClassAttrs) {
                String value = main.getValue(attr);
                addAsciiSafe(safe, value);
            }
        }
        for (Map.Entry<String, byte[]> e : resources.entrySet()) {
            String path = e.getKey();
            if (!path.startsWith(SERVICES_PREFIX)) {
                continue;
            }
            // 服务接口：文件名本身就是类名
            addAsciiSafe(safe, path.substring(SERVICES_PREFIX.length()));
            // 服务实现：文件每行一个实现类
            String text = new String(e.getValue(), "UTF-8");
            for (String rawLine : text.split("\n", -1)) {
                int hash = rawLine.indexOf('#');
                String code = hash >= 0 ? rawLine.substring(0, hash) : rawLine;
                String trimmed = code.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                // 兼容 "ClassName 其他构造参数" 的扩展写法，只取首段
                addAsciiSafe(safe, trimmed.split("\\s+", 2)[0]);
            }
        }
        return safe;
    }

    private static void addAsciiSafe(Set<String> safe, String binaryName) {
        if (binaryName == null) {
            return;
        }
        String t = binaryName.trim();
        if (t.isEmpty()) {
            return;
        }
        safe.add(t.replace('.', '/'));
    }

    /** 解析 MANIFEST 中的 Main-Class 并映射为改名后的最终内部名；无则 null。 */
    private String resolveMainClass(GlobalRemapper remapper,
                                    Map<String, byte[]> resources) throws IOException {
        byte[] manifestBytes = resources.get("META-INF/MANIFEST.MF");
        if (manifestBytes == null) {
            return null;
        }
        Manifest manifest = new Manifest();
        manifest.read(new java.io.ByteArrayInputStream(manifestBytes));
        String mainClass = manifest.getMainAttributes().getValue(Attributes.Name.MAIN_CLASS);
        if (mainClass == null || mainClass.isEmpty()) {
            return null;
        }
        String internal = mainClass.replace('.', '/');
        String mapped = remapper.classMap().get(internal);
        return mapped != null ? mapped : internal;
    }

    // ------------------------------------------------------------------
    // 输出
    // ------------------------------------------------------------------

    private void writeOutput(File in, File out, Map<String, byte[]> resources,
                             Map<String, byte[]> classBytes,
                             Map<String, byte[]> versionedBytes,
                             GlobalRemapper remapper) throws IOException {
        Manifest manifest = null;
        byte[] manifestBytes = resources.get("META-INF/MANIFEST.MF");
        if (manifestBytes != null) {
            manifest = new Manifest();
            manifest.read(new java.io.ByteArrayInputStream(manifestBytes));
            Attributes main = manifest.getMainAttributes();
            String mainClass = main.getValue(Attributes.Name.MAIN_CLASS);
            if (mainClass != null && !mainClass.isEmpty()) {
                String internal = mainClass.replace('.', '/');
                String mapped = remapper.classMap().get(internal);
                if (mapped != null) {
                    main.put(Attributes.Name.MAIN_CLASS, mapped.replace('/', '.'));
                    listener.log("Manifest Main-Class: " + mainClass + " -> " + mapped.replace('/', '.'));
                }
            }
        }

        FileOutputStream fos = new FileOutputStream(out);
        try {
            JarOutputStream jos;
            if (manifest != null) {
                jos = new JarOutputStream(fos, manifest);
            } else {
                jos = new JarOutputStream(fos);
            }
            try {
                Set<String> written = new java.util.HashSet<String>();

                // 资源（保持原顺序）
                for (Map.Entry<String, byte[]> e : resources.entrySet()) {
                    String name = e.getKey();
                    if ("META-INF/MANIFEST.MF".equals(name)) {
                        continue; // JarOutputStream 已写入
                    }
                    if (isSignatureFile(name)) {
                        listener.log("删除签名文件: " + name);
                        continue;
                    }
                    if (listener.cancelled()) {
                        break;
                    }
                    byte[] data = e.getValue();
                    if (name.startsWith(SERVICES_PREFIX)) {
                        writeService(jos, name, data, remapper, written);
                        continue;
                    }
                    putEntry(jos, name, data);
                    written.add(name);
                }

                // 多版本资源
                for (Map.Entry<String, byte[]> e : versionedBytes.entrySet()) {
                    putEntry(jos, e.getKey(), e.getValue());
                    written.add(e.getKey());
                }

                // 类（使用新内部名作为路径）
                for (Map.Entry<String, byte[]> e : classBytes.entrySet()) {
                    putEntry(jos, e.getKey() + ".class", e.getValue());
                }
            } finally {
                jos.close();
            }
        } finally {
            fos.close();
        }
    }

    private void writeService(java.util.jar.JarOutputStream jos, String path, byte[] data,
                              GlobalRemapper remapper, Set<String> written) throws IOException {
        String serviceBinary = path.substring(SERVICES_PREFIX.length());
        String mappedServiceBinary = remapper.mapBinaryName(serviceBinary);
        String newPath = SERVICES_PREFIX + mappedServiceBinary;

        String text = new String(data, "UTF-8");
        StringBuilder sb = new StringBuilder();
        for (String rawLine : text.split("\n", -1)) {
            int hash = rawLine.indexOf('#');
            String code = hash >= 0 ? rawLine.substring(0, hash) : rawLine;
            String comment = hash >= 0 ? rawLine.substring(hash) : "";
            String trimmed = code.trim();
            String mappedLine = rawLine;
            if (!trimmed.isEmpty()) {
                String mapped = remapper.mapBinaryName(trimmed);
                String leading = code.substring(0, code.length() - stripLeading(code).length());
                mappedLine = leading + mapped + comment;
            }
            sb.append(mappedLine).append('\n');
        }
        if (!written.contains(newPath)) {
            putEntry(jos, newPath, sb.toString().getBytes("UTF-8"));
            written.add(newPath);
            if (!newPath.equals(path)) {
                listener.log("服务文件改名: " + path + " -> " + newPath);
            }
        }
    }

    private static String stripLeading(String s) {
        int i = 0;
        while (i < s.length() && Character.isWhitespace(s.charAt(i))) {
            i++;
        }
        return s.substring(i);
    }

    private static boolean isSignatureFile(String name) {
        if (!name.startsWith("META-INF/")) {
            return false;
        }
        // 只处理 META-INF 根目录下的签名文件
        if (name.indexOf('/', "META-INF/".length()) >= 0) {
            return false;
        }
        String upper = name.toUpperCase(java.util.Locale.ROOT);
        return upper.endsWith(".SF") || upper.endsWith(".RSA")
                || upper.endsWith(".DSA") || upper.endsWith(".EC");
    }

    private static void putEntry(JarOutputStream jos, String name, byte[] data) throws IOException {
        JarEntry je = new JarEntry(name);
        je.setTime(0L); // 固定时间戳，构建结果可复现
        jos.putNextEntry(je);
        jos.write(data);
        jos.closeEntry();
    }

    private void copyPlain(File in, File out) throws IOException {
        ZipFile zf = new ZipFile(in);
        try {
            FileOutputStream fos = new FileOutputStream(out);
            try {
                JarOutputStream jos = new JarOutputStream(fos);
                try {
                    Enumeration<? extends ZipEntry> en = zf.entries();
                    while (en.hasMoreElements()) {
                        ZipEntry e = en.nextElement();
                        if (e.isDirectory()) {
                            continue;
                        }
                        putEntry(jos, e.getName(), readAll(zf, e));
                    }
                } finally {
                    jos.close();
                }
            } finally {
                fos.close();
            }
        } finally {
            zf.close();
        }
    }

    /** 基于 jar 内改名字节码按需 defineClass 的 ClassLoader，供字节码数据流分析解析类型。 */
    private static final class BytesClassLoader extends ClassLoader {
        private final Map<String, byte[]> classes;

        BytesClassLoader(ClassLoader parent, Map<String, byte[]> classes) {
            super(parent);
            this.classes = classes;
        }

        @Override
        protected Class<?> findClass(String name) throws ClassNotFoundException {
            byte[] b = classes.get(name.replace('.', '/'));
            if (b == null) {
                throw new ClassNotFoundException(name);
            }
            return defineClass(name, b, 0, b.length);
        }
    }
}
