package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AnnotationNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * 死代码 / 伪代码类工厂：批量生成“看起来极其真实，但对业务毫无用处”的类。
 *
 * 生成的类具备以下伪装特征：
 * <ul>
 *   <li>贴近真实工程的类名（CacheManager、RequestValidator、RetryPolicy 等），
 *       并<b>直接放入输入 jar 真实类所在的包内</b>（与业务类同目录混杂，
 *       按包内类数量加权分布，绝不新建独立包/文件夹）；</li>
 *   <li>拥有字段、构造器、静态初始化块、私有辅助方法、toString、业务风格方法；</li>
 *   <li>方法体内含 HashMap/ArrayList/StringBuilder/Iterator 等真实 API 调用、
 *       循环、提前返回与字符串常量；</li>
 *   <li>方法体内随机插入 {@code (r|1)!=0}、{@code (r^r)==0}、
 *       {@code (r+1)-r==1} 等数学恒真的<b>不透明谓词</b>，谓词的假分支
 *       抛出真实异常类型，静态分析/反编译难以判定其不可达；</li>
 *   <li>类之间通过构造与方法调用互相引用，形成跨类“依赖网”。</li>
 * </ul>
 *
 * 安全前提：
 * <ul>
 *   <li>字节码版本 Java 8，仅引用 JDK 自带 API（JDK8 可用）；</li>
 *   <li>所有跳转目标处操作数栈为空，maxStack/maxLocals 由 COMPUTE_FRAMES 重算；</li>
 *   <li>生成类会作为普通 ClassNode 进入后续改名 / 加密 / 平坦化流水线，
 *       与真实类被同等混淆，无法从“是否被混淆”区分。</li>
 * </ul>
 */
public final class DeadClassFactory {

    private static final String OBJ = "java/lang/Object";
    private static final String SB = "java/lang/StringBuilder";
    private static final String LIST = "java/util/List";
    private static final String MAP = "java/util/Map";
    private static final String HMAP = "java/util/HashMap";

    // 类名风格池：伪装成真实工程组件
    private static final String[] CLASS_NAMES = {
            "CacheManager", "RequestValidator", "ConnectionPool", "EventDispatcher",
            "RetryPolicy", "PropertyBinder", "HashRing", "TokenBucket",
            "SqlFragmentBuilder", "ResourceLocator", "DefaultRegistry", "CircuitBreaker",
            "CronExpressionParser", "ByteArrayBuffer", "ServiceDescriptor", "HttpHeaderCodec",
            "SnowflakeId", "LruCache", "ClassPathScanner", "PipelineStage",
            "TemplateRenderer", "RateLimiter", "BeanIntrospector", "MetricsCollector",
            "JsonNodeAdapter", "AsyncTaskScheduler", "LeaseCoordinator", "VersionRange",
            "DigestHelper", "RouteResolver", "CharsetDetector", "PayloadEnvelope",
            "ThreadContext", "BackoffStrategy", "TypeCoercion", "LockManager",
            "BufferAllocator", "ManifestParser", "QueueBalancer", "DeltaMerger",
    };
    private static final String[] CLASS_SUFFIX = {
            "", "", "", "Impl", "Support", "Base", "Adapter", "Handler",
            "Factory", "Strategy", "Bean", "Config", "Keeper", "Provider",
    };
    private static final String[] NAMESPACES = {
            "default", "core", "svc", "cache", "http", "batch", "sys", "async",
    };
    private static final String[] TAG_WORDS = {
            "primary", "shadow", "warm", "cold", "v1", "v2", "canary", "stable",
    };
    private static final String[] MAP_KEYS = {
            "mode", "region", "tenant", "channel", "schema",
    };
    private static final String[] MAP_VALUES = {
            "rw", "cn-1", "shared", "tcp", "v3",
    };
    private static final String[] ROUTES = {
            "GET:/v1/items", "POST:/v1/jobs", "topic://audit", "queue://delay",
    };
    private static final String[] DEAD_MESSAGES = {
            "invariant violated", "unreachable state", "negative size",
            "schema mismatch", "pool exhausted", "stale lease",
    };

    private static final class Fld {
        final String name;
        final String desc;

        Fld(String name, String desc) {
            this.name = name;
            this.desc = desc;
        }
    }

    private static final class GenClass {
        final ClassNode node;
        final String describe;
        final String estimate;
        final List<Fld> fields;

        GenClass(ClassNode node, String describe, String estimate, List<Fld> fields) {
            this.node = node;
            this.describe = describe;
            this.estimate = estimate;
            this.fields = fields;
        }
    }

    private DeadClassFactory() {
    }

    /**
     * 生成 count 个伪代码类。
     *
     * @param existingNames jar 内已有类内部名（避免重名）
     * @param realPackages  真实类所在包的加权列表：每个真实类贡献一个元素，
     *                      因此大类包会按比例分到更多伪代码类；空字符串表示默认包。
     *                      伪代码类直接放进这些包，与业务类同目录混杂。
     */
    public static List<ClassNode> generate(int count, Set<String> existingNames,
                                           List<String> realPackages, Random random) {
        Set<String> used = new LinkedHashSet<String>(existingNames);

        // 第一阶段：确定类名
        List<String> names = new ArrayList<String>();
        int nameIdx = 0;
        int serial = 0;
        while (names.size() < count) {
            String base = CLASS_NAMES[nameIdx % CLASS_NAMES.length];
            String suffix = CLASS_SUFFIX[random.nextInt(CLASS_SUFFIX.length)];
            String simple = base + suffix;
            String pkg = pickPackage(realPackages, random);
            String full = pkg.isEmpty() ? simple : pkg + "/" + simple;
            if (used.contains(full)) {
                // 加序号，确保绝不重名
                String cand = pkg.isEmpty()
                        ? base + suffix + serial++
                        : pkg + "/" + base + suffix + serial++;
                if (used.contains(cand)) {
                    nameIdx++;
                    serial = 0;
                    continue;
                }
                full = cand;
            }
            used.add(full);
            names.add(full);
            nameIdx++;
        }

        // 第二阶段：先确定每类的固定方法名（跨类互调依赖），再构建方法体
        List<GenClass> gens = new ArrayList<GenClass>();
        for (String full : names) {
            ClassNode cn = new ClassNode(Opcodes.ASM9);
            cn.version = Opcodes.V1_8;
            cn.access = Opcodes.ACC_PUBLIC;
            cn.name = full;
            cn.superName = OBJ;

            String describeName = pick(
                    new String[]{"describe", "renderState", "dumpSnapshot", "debugInfo"}, random);
            String estimateName = pick(
                    new String[]{"estimate", "weightedScore", "capacity", "score"}, random);
            List<Fld> fields = chooseFields(random);
            gens.add(new GenClass(cn, describeName, estimateName, fields));
        }

        for (int i = 0; i < gens.size(); i++) {
            buildClass(gens.get(i), i, gens, random);
        }

        List<ClassNode> out = new ArrayList<ClassNode>();
        for (GenClass g : gens) {
            out.add(g.node);
        }
        return out;
    }

    /**
     * 生成 count 个“分发节点空壳”类：普通 public 类，仅含默认构造器。
     * 它们与伪代码类同时注入、随后被同等改名/混淆，最终由 GuardChain
     * 追加校验入口，因此在混淆产物中与普通业务类命名风格完全一致。
     */
    public static List<ClassNode> generateDispatcherShells(int count,
                                                           Set<String> existingNames,
                                                           List<String> realPackages,
                                                           Random random) {
        Set<String> used = new LinkedHashSet<String>(existingNames);
        List<ClassNode> out = new ArrayList<ClassNode>();
        int nameIdx = 0;
        int serial = 0;
        while (out.size() < count) {
            String base = CLASS_NAMES[nameIdx % CLASS_NAMES.length];
            String suffix = CLASS_SUFFIX[random.nextInt(CLASS_SUFFIX.length)];
            String pkg = pickPackage(realPackages, random);
            String full = pkg.isEmpty() ? base + suffix : pkg + "/" + base + suffix;
            if (used.contains(full)) {
                String cand = pkg.isEmpty()
                        ? base + suffix + serial++
                        : pkg + "/" + base + suffix + serial++;
                if (used.contains(cand)) {
                    nameIdx++;
                    serial = 0;
                    continue;
                }
                full = cand;
            }
            used.add(full);
            nameIdx++;

            ClassNode cn = new ClassNode(Opcodes.ASM9);
            cn.version = Opcodes.V1_8;
            cn.access = Opcodes.ACC_PUBLIC;
            cn.name = full;
            cn.superName = OBJ;
            org.objectweb.asm.tree.MethodNode init = new org.objectweb.asm.tree.MethodNode(
                    Opcodes.ASM9, Opcodes.ACC_PUBLIC, "<init>", "()V", null, null);
            init.visitCode();
            init.visitVarInsn(Opcodes.ALOAD, 0);
            init.visitMethodInsn(Opcodes.INVOKESPECIAL, OBJ, "<init>", "()V", false);
            init.visitInsn(Opcodes.RETURN);
            init.visitMaxs(1, 1);
            init.visitEnd();
            cn.methods.add(init);
            out.add(cn);
        }
        return out;
    }

    /**
     * 直接选取一个真实类所在的包。加权列表中每个真实类贡献一个元素，
     * 因此类越多的包分到伪代码类的概率越高；空字符串表示默认包（jar 根）。
     */
    private static String pickPackage(List<String> realPackages, Random random) {
        if (realPackages.isEmpty()) {
            return "";
        }
        return realPackages.get(random.nextInt(realPackages.size()));
    }

    private static String pick(String[] pool, Random random) {
        return pool[random.nextInt(pool.length)];
    }

    // ------------------------------------------------------------------
    // 字段
    // ------------------------------------------------------------------

    private static List<Fld> chooseFields(Random random) {
        List<Fld> f = new ArrayList<Fld>();
        f.add(new Fld("revision", "I"));
        f.add(new Fld("namespace", "Ljava/lang/String;"));
        f.add(new Fld("tags", "Ljava/util/List;"));
        f.add(new Fld("attributes", "Ljava/util/Map;"));
        f.add(new Fld("createdAt", "J"));
        f.add(new Fld("ttlMillis", "J"));
        Object[][] extras = {
                {"enabled", "Z"},
                {"maxRequests", "I"},
                {"weight", "D"},
                {"offsets", "[I"},
                {"aliases", "[Ljava/lang/String;"},
                {"inFlight", "Ljava/util/concurrent/atomic/AtomicInteger;"},
                {"checksum", "I"},
                {"routeKey", "Ljava/lang/String;"},
                {"expiresAt", "J"},
        };
        Collections.shuffle(Arrays.asList(extras), random);
        int n = 1 + random.nextInt(3);
        Set<String> names = new LinkedHashSet<String>();
        for (Fld fd : f) {
            names.add(fd.name);
        }
        for (int i = 0; i < n && i < extras.length; i++) {
            String fn = (String) extras[i][0];
            if (names.add(fn)) {
                f.add(new Fld(fn, (String) extras[i][1]));
            }
        }
        return f;
    }

    private static Fld field(List<Fld> fields, String name) {
        for (Fld f : fields) {
            if (f.name.equals(name)) {
                return f;
            }
        }
        return null;
    }

    // ------------------------------------------------------------------
    // 类构建
    // ------------------------------------------------------------------

    private static void buildClass(GenClass g, int index, List<GenClass> all, Random random) {
        ClassNode cn = g.node;
        Set<String> usedMembers = new LinkedHashSet<String>();

        for (Fld f : g.fields) {
            cn.fields.add(new FieldNode(Opcodes.ASM9, Opcodes.ACC_PRIVATE,
                    f.name, f.desc, null, null));
            usedMembers.add(f.name);
        }
        cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, "SEED", "I", null, null));
        cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC, "TAG", "Ljava/lang/String;", null, null));

        cn.methods.add(buildClinit(cn.name));
        cn.methods.add(buildInit(cn.name, g.fields, random));

        String pairName = unique(usedMembers,
                pick(new String[]{"appendPair", "appendField"}, random));
        cn.methods.add(buildAppendPair(cn.name, pairName));
        cn.methods.add(buildDescribe(cn.name, g.fields, g.describe, pairName));
        cn.methods.add(buildEstimate(cn.name, g.estimate, random));
        cn.methods.add(buildToString(cn.name, g.describe));
        cn.methods.add(buildTally(cn.name, random));
        cn.methods.add(buildNormalize(cn.name, random));

        List<MethodNode> optional = new ArrayList<MethodNode>();
        optional.add(buildRegister(cn.name));
        optional.add(buildSweep(cn.name));
        optional.add(buildNextWindow(cn.name));
        optional.add(buildShouldRetry(cn.name, random));
        optional.add(buildBackoff(cn.name));
        optional.add(buildChecksum(cn.name));
        optional.add(buildReset(cn.name, g.fields));
        Collections.shuffle(optional, random);
        int optCount = 2 + random.nextInt(3);
        for (int i = 0; i < optCount && i < optional.size(); i++) {
            MethodNode m = optional.get(i);
            if (usedMembers.add(m.name)) {
                cn.methods.add(m);
            }
        }

        // 跨类互调，形成伪装的依赖网
        if (all.size() >= 2 && random.nextInt(100) < 55) {
            GenClass peer = all.get(random.nextInt(all.size()));
            if (peer != g) {
                String probeName = unique(usedMembers,
                        pick(new String[]{"peerProbe", "probeUpstream", "askPeer"}, random));
                cn.methods.add(buildPeerProbe(cn.name, probeName, peer, random));
            }
        }

        // 随机给个别方法加 @Deprecated，增强真实感
        for (MethodNode m : cn.methods) {
            if (!m.name.equals("<init>") && !m.name.equals("<clinit>")
                    && random.nextInt(100) < 12) {
                AnnotationNode an = new AnnotationNode(Opcodes.ASM9,
                        "Ljava/lang/Deprecated;");
                if (m.visibleAnnotations == null) {
                    m.visibleAnnotations = new ArrayList<AnnotationNode>();
                }
                m.visibleAnnotations.add(an);
            }
        }
    }

    private static String unique(Set<String> used, String base) {
        if (used.add(base)) {
            return base;
        }
        int i = 0;
        String n;
        do {
            n = base + i++;
        } while (!used.add(n));
        return n;
    }

    // ------------------------------------------------------------------
    // 基础指令辅助
    // ------------------------------------------------------------------

    private static void pushInt(InsnList il, int v) {
        if (v >= -1 && v <= 5) {
            il.add(new InsnNode(Opcodes.ICONST_0 + v));
        } else if (v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE) {
            il.add(new IntInsnNode(Opcodes.BIPUSH, v));
        } else if (v >= Short.MIN_VALUE && v <= Short.MAX_VALUE) {
            il.add(new IntInsnNode(Opcodes.SIPUSH, v));
        } else {
            il.add(new LdcInsnNode(Integer.valueOf(v)));
        }
    }

    /** 栈：[sb, value] -> [sb]，调用对应重载的 StringBuilder.append。 */
    private static void append(InsnList il, char kind) {
        String desc;
        switch (kind) {
            case 'I':
                desc = "(I)L" + SB + ";";
                break;
            case 'J':
                desc = "(J)L" + SB + ";";
                break;
            case 'Z':
                desc = "(Z)L" + SB + ";";
                break;
            case 'D':
                desc = "(D)L" + SB + ";";
                break;
            case 'S':
                desc = "(Ljava/lang/String;)L" + SB + ";";
                break;
            case 'C':
                desc = "(C)L" + SB + ";";
                break;
            default:
                desc = "(Ljava/lang/Object;)L" + SB + ";";
        }
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, SB, "append", desc, false));
    }

    /** ALOAD this/slot ... GETFIELD */
    private static void loadField(InsnList il, String owner, Fld f, boolean storeTargetOnStack) {
        if (storeTargetOnStack) {
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        }
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, f.name, f.desc));
    }

    /**
     * 在空栈位置插入恒真不透明谓词，假分支抛异常（永不可达）。
     * <pre>
     *   &lt;恒真&gt; IFxx skip
     *   NEW X; DUP; ...; ATHROW
     * skip:
     * </pre>
     */
    private static LabelNode opaqueGuard(InsnList il, Random random, String owner) {
        LabelNode skip = new LabelNode();
        int variant = random.nextInt(4);
        int r = random.nextInt();
        switch (variant) {
            case 0: // (r | 1) != 0
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IOR));
                il.add(new JumpInsnNode(Opcodes.IFNE, skip));
                break;
            case 1: // (r ^ r) == 0
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new JumpInsnNode(Opcodes.IFEQ, skip));
                break;
            case 2: // SEED == SEED
                il.add(new FieldInsnNode(Opcodes.GETSTATIC, owner, "SEED", "I"));
                il.add(new FieldInsnNode(Opcodes.GETSTATIC, owner, "SEED", "I"));
                il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, skip));
                break;
            default: // (r + 1) - r == 1
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IADD));
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new InsnNode(Opcodes.ISUB));
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new JumpInsnNode(Opcodes.IF_ICMPEQ, skip));
                break;
        }
        emitDeadThrow(il, random);
        il.add(skip);
        return skip;
    }

    private static void emitDeadThrow(InsnList il, Random random) {
        int kind = random.nextInt(4);
        if (kind == 0) {
            il.add(new InsnNode(Opcodes.ACONST_NULL));
            il.add(new InsnNode(Opcodes.ATHROW));
            return;
        }
        String ex;
        boolean withMsg;
        switch (kind) {
            case 1:
                ex = "java/lang/IllegalStateException";
                withMsg = true;
                break;
            case 2:
                ex = "java/lang/ArithmeticException";
                withMsg = true;
                break;
            default:
                ex = "java/lang/RuntimeException";
                withMsg = random.nextBoolean();
        }
        il.add(new TypeInsnNode(Opcodes.NEW, ex));
        il.add(new InsnNode(Opcodes.DUP));
        if (withMsg) {
            il.add(new LdcInsnNode(pick(DEAD_MESSAGES, random)));
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, ex, "<init>",
                    "(Ljava/lang/String;)V", false));
        } else {
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, ex, "<init>", "()V", false));
        }
        il.add(new InsnNode(Opcodes.ATHROW));
    }

    private static MethodNode newMethod(int access, String name, String desc) {
        return new MethodNode(Opcodes.ASM9, access, name, desc, null, null);
    }

    // ------------------------------------------------------------------
    // <clinit> / <init>
    // ------------------------------------------------------------------

    private static MethodNode buildClinit(String owner) {
        MethodNode m = newMethod(Opcodes.ACC_STATIC, "<clinit>", "()V");
        InsnList il = m.instructions;
        // SEED = ((int)(System.nanoTime() & 0x7fffffff)) | 1 （恒非零）
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/System",
                "nanoTime", "()J", false));
        il.add(new LdcInsnNode(Long.valueOf(0x7fffffffL)));
        il.add(new InsnNode(Opcodes.LAND));
        il.add(new InsnNode(Opcodes.L2I));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IOR));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, owner, "SEED", "I"));
        // TAG = new StringBuilder("rev-").append(Integer.toHexString(SEED)).toString()
        // 静态方法槽 0=sb，槽 1=hex
        il.add(new TypeInsnNode(Opcodes.NEW, SB));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, SB, "<init>", "()V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 0));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new LdcInsnNode("rev-"));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, owner, "SEED", "I"));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Integer",
                "toHexString", "(I)Ljava/lang/String;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, SB,
                "toString", "()Ljava/lang/String;", false));
        il.add(new FieldInsnNode(Opcodes.PUTSTATIC, owner, "TAG",
                "Ljava/lang/String;"));
        il.add(new InsnNode(Opcodes.RETURN));
        return m;
    }

    private static MethodNode buildInit(String owner, List<Fld> fields, Random random) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "<init>", "()V");
        InsnList il = m.instructions;
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, OBJ, "<init>", "()V", false));

        for (Fld f : fields) {
            emitFieldDefault(il, owner, f, random);
        }
        il.add(new InsnNode(Opcodes.RETURN));
        return m;
    }

    /** 空栈：给某字段赋默认值。 */
    private static void emitFieldDefault(InsnList il, String owner, Fld f, Random random) {
        char c = f.desc.charAt(0);
        switch (c) {
            case 'Z':
                il.add(new VarInsnNode(Opcodes.ALOAD, 0));
                il.add(new InsnNode(random.nextBoolean() ? Opcodes.ICONST_1 : Opcodes.ICONST_0));
                il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, f.name, f.desc));
                break;
            case 'I': {
                int v;
                if (f.name.equals("revision")) {
                    v = 1 + random.nextInt(999);
                } else if (f.name.equals("maxRequests")) {
                    v = new int[]{16, 64, 128, 512}[random.nextInt(4)];
                } else {
                    v = random.nextInt(0xFFFF);
                }
                il.add(new VarInsnNode(Opcodes.ALOAD, 0));
                pushInt(il, v);
                il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, f.name, f.desc));
                break;
            }
            case 'J':
                il.add(new VarInsnNode(Opcodes.ALOAD, 0));
                if (f.name.equals("createdAt")) {
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/System",
                            "currentTimeMillis", "()J", false));
                } else if (f.name.equals("ttlMillis")) {
                    il.add(new LdcInsnNode(Long.valueOf(
                            new long[]{5000L, 15000L, 60000L, 300000L}[random.nextInt(4)])));
                } else {
                    il.add(new LdcInsnNode(Long.valueOf(random.nextInt(1000000) * 1000L)));
                }
                il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, f.name, f.desc));
                break;
            case 'D':
                il.add(new VarInsnNode(Opcodes.ALOAD, 0));
                il.add(new LdcInsnNode(Double.valueOf(0.25 + random.nextInt(8) * 0.125)));
                il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, f.name, f.desc));
                break;
            case 'L': {
                String n = f.desc;
                il.add(new VarInsnNode(Opcodes.ALOAD, 0));
                if (n.equals("Ljava/lang/String;")) {
                    String v;
                    if (f.name.equals("namespace")) {
                        v = pick(NAMESPACES, random);
                    } else if (f.name.equals("routeKey")) {
                        v = pick(ROUTES, random);
                    } else {
                        v = "val-" + Integer.toHexString(random.nextInt(0xFFFF));
                    }
                    il.add(new LdcInsnNode(v));
                } else if (n.equals("Ljava/util/List;")) {
                    il.add(new TypeInsnNode(Opcodes.NEW, "java/util/ArrayList"));
                    il.add(new InsnNode(Opcodes.DUP));
                    il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                            "java/util/ArrayList", "<init>", "()V", false));
                    int seeds = 1 + random.nextInt(2);
                    for (int i = 0; i < seeds; i++) {
                        il.add(new InsnNode(Opcodes.DUP));
                        il.add(new LdcInsnNode(pick(TAG_WORDS, random)));
                        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, LIST,
                                "add", "(Ljava/lang/Object;)Z", true));
                        il.add(new InsnNode(Opcodes.POP));
                    }
                } else if (n.equals("Ljava/util/Map;")) {
                    il.add(new TypeInsnNode(Opcodes.NEW, HMAP));
                    il.add(new InsnNode(Opcodes.DUP));
                    il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                            HMAP, "<init>", "()V", false));
                    il.add(new InsnNode(Opcodes.DUP));
                    il.add(new LdcInsnNode(pick(MAP_KEYS, random)));
                    il.add(new LdcInsnNode(pick(MAP_VALUES, random)));
                    il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, HMAP,
                            "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
                            false));
                    il.add(new InsnNode(Opcodes.POP));
                } else if (n.equals("Ljava/util/concurrent/atomic/AtomicInteger;")) {
                    il.add(new TypeInsnNode(Opcodes.NEW,
                            "java/util/concurrent/atomic/AtomicInteger"));
                    il.add(new InsnNode(Opcodes.DUP));
                    pushInt(il, random.nextInt(16));
                    il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                            "java/util/concurrent/atomic/AtomicInteger",
                            "<init>", "(I)V", false));
                } else {
                    il.add(new InsnNode(Opcodes.ACONST_NULL));
                }
                il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, f.name, n));
                break;
            }
            case '[': {
                int size = 1 + random.nextInt(3);
                il.add(new VarInsnNode(Opcodes.ALOAD, 0));
                pushInt(il, size);
                boolean isIntArr = f.desc.equals("[I");
                if (isIntArr) {
                    il.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_INT));
                } else {
                    il.add(new TypeInsnNode(Opcodes.ANEWARRAY, "java/lang/String"));
                }
                for (int i = 0; i < size; i++) {
                    il.add(new InsnNode(Opcodes.DUP));
                    pushInt(il, i);
                    if (isIntArr) {
                        pushInt(il, random.nextInt(256));
                        il.add(new InsnNode(Opcodes.IASTORE));
                    } else {
                        il.add(new LdcInsnNode(pick(TAG_WORDS, random)));
                        il.add(new InsnNode(Opcodes.AASTORE));
                    }
                }
                il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, f.name, f.desc));
                break;
            }
            default:
                break;
        }
    }

    // ------------------------------------------------------------------
    // 方法模板
    // ------------------------------------------------------------------

    /** private void appendPair(StringBuilder sb, String name, int value)，槽 0..3 */
    private static MethodNode buildAppendPair(String owner, String name) {
        MethodNode m = newMethod(Opcodes.ACC_PRIVATE, name,
                "(L" + SB + ";Ljava/lang/String;I)V");
        InsnList il = m.instructions;
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new LdcInsnNode("="));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        append(il, 'I');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new LdcInsnNode(","));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new InsnNode(Opcodes.RETURN));
        return m;
    }

    /** public String describe()，槽 0=this,1=sb */
    private static MethodNode buildDescribe(String owner, List<Fld> fields,
                                            String name, String pairName) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, name, "()Ljava/lang/String;");
        InsnList il = m.instructions;
        il.add(new TypeInsnNode(Opcodes.NEW, SB));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, SB, "<init>", "()V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        // sb.append(getClass().getSimpleName())
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, OBJ,
                "getClass", "()Ljava/lang/Class;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/Class",
                "getSimpleName", "()Ljava/lang/String;", false));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new LdcInsnNode("{"));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        // appendPair(sb, "rev", revision)
        Fld revision = field(fields, "revision");
        if (revision != null) {
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
            il.add(new VarInsnNode(Opcodes.ALOAD, 1));
            il.add(new LdcInsnNode("rev"));
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
            il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "revision", "I"));
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, owner, pairName,
                    "(L" + SB + ";Ljava/lang/String;I)V", false));
        }
        // 其余字段直接 sb.append(field)
        int shown = 0;
        for (Fld f : fields) {
            if (f.name.equals("revision") || shown >= 3) {
                continue;
            }
            char kind;
            switch (f.desc.charAt(0)) {
                case 'J':
                    kind = 'J';
                    break;
                case 'Z':
                    kind = 'Z';
                    break;
                case 'D':
                    kind = 'D';
                    break;
                case 'I':
                    kind = 'I';
                    break;
                default:
                    kind = 'O';
            }
            il.add(new VarInsnNode(Opcodes.ALOAD, 1));
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
            il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, f.name, f.desc));
            append(il, kind);
            il.add(new InsnNode(Opcodes.POP));
            shown++;
        }
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new LdcInsnNode("}"));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, SB,
                "toString", "()Ljava/lang/String;", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return m;
    }

    /** public String toString() { return describe(); } */
    private static MethodNode buildToString(String owner, String describe) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "toString", "()Ljava/lang/String;");
        InsnList il = m.instructions;
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, owner, describe,
                "()Ljava/lang/String;", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return m;
    }

    /** public int estimate()：带循环与不透明谓词。槽 0=this,1=n,2=i */
    private static MethodNode buildEstimate(String owner, String name, Random random) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, name, "()I");
        InsnList il = m.instructions;
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "revision", "I"));
        il.add(new VarInsnNode(Opcodes.ISTORE, 1));
        opaqueGuard(il, random, owner);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        pushInt(il, 4);
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        // n = n*31 + i*17
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        pushInt(il, 31);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        pushInt(il, 17);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 1));
        il.add(new IincInsnNode(2, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new LdcInsnNode(Integer.valueOf(0x7fffffff)));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** public int tally(Collection items)，槽 0..4 */
    private static MethodNode buildTally(String owner, Random random) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "tally", "(Ljava/util/Collection;)I");
        InsnList il = m.instructions;
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        LabelNode end = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFNULL, end));
        opaqueGuard(il, random, owner);
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Collection",
                "iterator", "()Ljava/util/Iterator;", true));
        il.add(new VarInsnNode(Opcodes.ASTORE, 3));
        LabelNode loop = new LabelNode();
        LabelNode skip = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Iterator",
                "hasNext", "()Z", true));
        il.add(new JumpInsnNode(Opcodes.IFEQ, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Iterator",
                "next", "()Ljava/lang/Object;", true));
        il.add(new VarInsnNode(Opcodes.ASTORE, 4));
        il.add(new VarInsnNode(Opcodes.ALOAD, 4));
        il.add(new JumpInsnNode(Opcodes.IFNULL, skip));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ALOAD, 4));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, OBJ,
                "hashCode", "()I", false));
        pushInt(il, 3);
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(skip);
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new LdcInsnNode(Integer.valueOf(0x7fffffff)));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** public String normalizeKey(String prefix, int parts)，槽 0..4 */
    private static MethodNode buildNormalize(String owner, Random random) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "normalizeKey",
                "(Ljava/lang/String;I)Ljava/lang/String;");
        InsnList il = m.instructions;
        LabelNode notNull = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, notNull));
        il.add(new LdcInsnNode("default"));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        il.add(notNull);
        // parts = min(parts, 12)
        LabelNode capped = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        pushInt(il, 12);
        il.add(new JumpInsnNode(Opcodes.IF_ICMPLE, capped));
        pushInt(il, 12);
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(capped);
        // sb = new StringBuilder(namespace)
        il.add(new TypeInsnNode(Opcodes.NEW, SB));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "namespace",
                "Ljava/lang/String;"));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, SB, "<init>",
                "(Ljava/lang/String;)V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 3));
        opaqueGuard(il, random, owner);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 4));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new LdcInsnNode(":"));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        pushInt(il, 7);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "revision", "I"));
        il.add(new InsnNode(Opcodes.IADD));
        append(il, 'I');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new IincInsnNode(4, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, SB,
                "toString", "()Ljava/lang/String;", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return m;
    }

    /** public boolean register(String key, Object value)，槽 0..3 */
    private static MethodNode buildRegister(String owner) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "register",
                "(Ljava/lang/String;Ljava/lang/Object;)Z");
        InsnList il = m.instructions;
        LabelNode keyOk = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, keyOk));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(keyOk);
        LabelNode mapOk = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "attributes",
                "Ljava/util/Map;"));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, mapOk));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new TypeInsnNode(Opcodes.NEW, HMAP));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, HMAP, "<init>", "()V", false));
        il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, "attributes",
                "Ljava/util/Map;"));
        il.add(mapOk);
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "attributes",
                "Ljava/util/Map;"));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, MAP, "size", "()I", true));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "attributes",
                "Ljava/util/Map;"));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, MAP,
                "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;", true));
        il.add(new InsnNode(Opcodes.POP));
        LabelNode grew = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "attributes",
                "Ljava/util/Map;"));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, MAP, "size", "()I", true));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPLE, grew));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(grew);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** public int sweep()，遍历 tags。槽 0..3 */
    private static MethodNode buildSweep(String owner) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "sweep", "()I");
        InsnList il = m.instructions;
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 1));
        LabelNode end = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "tags", "Ljava/util/List;"));
        il.add(new JumpInsnNode(Opcodes.IFNULL, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "tags", "Ljava/util/List;"));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, LIST,
                "iterator", "()Ljava/util/Iterator;", true));
        il.add(new VarInsnNode(Opcodes.ASTORE, 2));
        LabelNode loop = new LabelNode();
        LabelNode notNull = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Iterator",
                "hasNext", "()Z", true));
        il.add(new JumpInsnNode(Opcodes.IFEQ, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE, "java/util/Iterator",
                "next", "()Ljava/lang/Object;", true));
        il.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/String"));
        il.add(new VarInsnNode(Opcodes.ASTORE, 3));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new JumpInsnNode(Opcodes.IFNULL, notNull));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/String",
                "length", "()I", false));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(notNull);
        il.add(new IincInsnNode(1, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** public long nextWindow() */
    private static MethodNode buildNextWindow(String owner) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "nextWindow", "()J");
        InsnList il = m.instructions;
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "createdAt", "J"));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new FieldInsnNode(Opcodes.GETFIELD, owner, "ttlMillis", "J"));
        il.add(new InsnNode(Opcodes.LADD));
        il.add(new FieldInsnNode(Opcodes.GETSTATIC, owner, "SEED", "I"));
        il.add(new InsnNode(Opcodes.I2L));
        il.add(new InsnNode(Opcodes.LADD));
        il.add(new InsnNode(Opcodes.LRETURN));
        return m;
    }

    /** public boolean shouldRetry(int attempt, int status)，槽 0..2 */
    private static MethodNode buildShouldRetry(String owner, Random random) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "shouldRetry", "(II)Z");
        InsnList il = m.instructions;
        LabelNode no = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        pushInt(il, 3);
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, no));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        pushInt(il, 500);
        il.add(new JumpInsnNode(Opcodes.IF_ICMPLT, no));
        opaqueGuard(il, random, owner);
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(no);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** public long backoffMillis(int attempt)，槽 0..1 */
    private static MethodNode buildBackoff(String owner) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "backoffMillis", "(I)J");
        InsnList il = m.instructions;
        LabelNode nonNeg = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, nonNeg));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 1));
        il.add(nonNeg);
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        pushInt(il, 100);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.I2L));
        il.add(new InsnNode(Opcodes.LRETURN));
        return m;
    }

    /** public int checksumOf(byte[] data)，槽 0..3 */
    private static MethodNode buildChecksum(String owner) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "checksumOf", "([B)I");
        InsnList il = m.instructions;
        LabelNode ok = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, ok));
        il.add(new InsnNode(Opcodes.ICONST_M1));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(ok);
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new InsnNode(Opcodes.ARRAYLENGTH));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        pushInt(il, 31);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.BALOAD));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new IincInsnNode(3, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** public void resetCounters() */
    private static MethodNode buildReset(String owner, List<Fld> fields) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, "resetCounters", "()V");
        InsnList il = m.instructions;
        Fld revision = field(fields, "revision");
        if (revision != null) {
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
            il.add(new InsnNode(Opcodes.ICONST_0));
            il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, "revision", "I"));
        }
        Fld inflight = field(fields, "inFlight");
        if (inflight != null) {
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
            il.add(new TypeInsnNode(Opcodes.NEW,
                    "java/util/concurrent/atomic/AtomicInteger"));
            il.add(new InsnNode(Opcodes.DUP));
            il.add(new InsnNode(Opcodes.ICONST_0));
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                    "java/util/concurrent/atomic/AtomicInteger", "<init>", "(I)V", false));
            il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, "inFlight",
                    "Ljava/util/concurrent/atomic/AtomicInteger;"));
        }
        Fld enabled = field(fields, "enabled");
        if (enabled != null) {
            il.add(new VarInsnNode(Opcodes.ALOAD, 0));
            il.add(new InsnNode(Opcodes.ICONST_1));
            il.add(new FieldInsnNode(Opcodes.PUTFIELD, owner, "enabled", "Z"));
        }
        if (revision == null && inflight == null && enabled == null) {
            il.add(new FieldInsnNode(Opcodes.GETSTATIC, owner, "TAG",
                    "Ljava/lang/String;"));
            il.add(new InsnNode(Opcodes.POP));
        }
        il.add(new InsnNode(Opcodes.RETURN));
        return m;
    }

    /** public String peerProbe(int seed)：跨类调用。槽 0..4 */
    private static MethodNode buildPeerProbe(String owner, String name, GenClass peer,
                                             Random random) {
        MethodNode m = newMethod(Opcodes.ACC_PUBLIC, name, "(I)Ljava/lang/String;");
        InsnList il = m.instructions;
        // Peer p = new Peer();
        il.add(new TypeInsnNode(Opcodes.NEW, peer.node.name));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                peer.node.name, "<init>", "()V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 2));
        // p.estimate();
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, peer.node.name,
                peer.estimate, "()I", false));
        il.add(new InsnNode(Opcodes.POP));
        // String d = p.describe();
        il.add(new VarInsnNode(Opcodes.ALOAD, 2));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, peer.node.name,
                peer.describe, "()Ljava/lang/String;", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 3));
        // 恒真谓词：((seed | 1) & 1) != 0
        LabelNode skip = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IOR));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new JumpInsnNode(Opcodes.IFNE, skip));
        emitDeadThrow(il, random);
        il.add(skip);
        // return new StringBuilder(d).append('@').append(seed).toString();
        il.add(new TypeInsnNode(Opcodes.NEW, SB));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 3));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, SB, "<init>",
                "(Ljava/lang/String;)V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 4));
        il.add(new VarInsnNode(Opcodes.ALOAD, 4));
        il.add(new LdcInsnNode("@"));
        append(il, 'S');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 4));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        append(il, 'I');
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 4));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, SB,
                "toString", "()Ljava/lang/String;", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return m;
    }
}
