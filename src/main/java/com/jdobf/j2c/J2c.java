package com.jdobf.j2c;

import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.commons.ClassRemapper;
import org.objectweb.asm.commons.Remapper;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

/**
 * j2c 原生下沉的规划与字节码改写。
 *
 * <h3>下沉模型</h3>
 * <ol>
 *   <li><b>规划</b>：按 InnerClasses + Nestmates(JDK11+) 关系把类分成簇；
 *       合格簇中类的合格<i>静态方法</i>被整体抽走（实例方法因 this/字段
 *       状态问题保留）；</li>
 *   <li><b>Shell 化</b>：被抽方法改为 {@code native}，无静态字段的类
 *       &lt;clinit&gt; 换成“加载原生桥接 DLL”；含合成静态表/编译期常量的类
 *       保留原 &lt;clinit&gt; 仅前插加载调用（shell/隐藏两侧状态各自确定）。
 *       每个 shell 另配 40 个同样转 native 的屎山假方法
 *       （假方法体只存在于隐藏 blob）——Java 层只剩不含一丝真实逻辑的虚假类。
 *       伪代码假类做<b>全空心</b>处理：字段/构造器/实例方法全部从 shell 删除，
 *       仅留 native 静态声明（假类在 shell 世界永不被实例化，{@code new} 只
 *       发生在隐藏类互调中）；</li>
 *   <li><b>隐藏类编码</b>：Shell 化之前捕获的完整（已混淆）字节码，把
 *       簇内类名重映射为 {@code 原名$$n}、剥掉 InnerClasses/Enclosing
 *       属性但保留并重写 NestHost/NestMembers（高版本 JVM 跨类私有访问
 *       校验依赖），交给 C++ 端加密嵌入 DLL；运行时 JNI 在原 ClassLoader 中
 *       DefineClass 复活，按标准 JNI 导出符号惰性绑定并静态转发。</li>
 * </ol>
 *
 * <h3>护栏（不满足则整簇跳过，宁可不做也不做错）</h3>
 * 接口/注解/枚举/模块（不作为簇成员也不连坐引用它们的类）、非 ASCII 类名、
 * MANIFEST 主类及其簇、排除类均不参与；静态字段只允许编译器合成字段与
 * final 编译期常量（普通可变静态字段会造成 shell/隐藏状态分裂）；跨簇
 * GETSTATIC/PUTSTATIC、或对留在簇外的 nest 成员的私有访问均否决。
 * class 文件版本不限（52~最新均可，高版本 class 需高版本 JVM 运行，
 * DefineClass 与 JNI 行为一致）。伪代码假类在“放松名单”内：允许自带的
 * SEED/TAG 静态字段（shell 化时字段整体删除，状态只存于隐藏侧），其余
 * 护栏不变；放松名单受 {@link #FAKE_CAP} 上限保护，避免万级假类撑爆
 * 单翻译单元编译。
 */
public final class J2c {

    /** 隐藏类后缀：$ 在 JVM 二进制类名中合法。 */
    public static final String HIDDEN_SUFFIX = "$$n";
    /** Shell 类中注入的诱饵假方法数（方法体进 DLL，shell 只剩 native 声明）。 */
    public static final int DECOY_METHODS = 40;
    /** 放松名单（伪代码假类）最大下沉数量：控制 DLL 体积与 C++ 单 TU 编译规模。 */
    public static final int FAKE_CAP = 128;

    private J2c() {
    }

    /** 单个类的下沉计划。 */
    public static final class ClassPlan {
        public final ClassNode cn;
        public final String hiddenName;
        /** 要抽走转 native 的方法键 [name, desc]（在变换后的方法列表里匹配）。 */
        public final List<String[]> extract = new ArrayList<String[]>();
        /**
         * 含屎山假方法的完整节点（隐藏 blob 与 shell 的共同源），由编排层
         * 在捕获前灌入；为 {@code null} 时退化为 {@link #cn}（簇内纯依赖成员）。
         */
        public ClassNode full;
        /**
         * 双 payload 分区：0 = 首映射镜像（boot 时映射），
         * 1 = 按需镜像（首个本区 shell 绑定时才在内存中映射）。
         * 由 {@link #partition} 按引用闭包连通分量确定性分配。
         */
        public int group;

        ClassPlan(ClassNode cn, String hiddenName) {
            this.cn = cn;
            this.hiddenName = hiddenName;
        }
    }

    /** 全局下沉计划。 */
    public static final class Plan {
        /** shell 内部名 -> 计划，保持稳定顺序。 */
        public final LinkedHashMap<String, ClassPlan> classes =
                new LinkedHashMap<String, ClassPlan>();

        /**
         * 两个 payload 分区之间是否仍存在隐藏类引用（整个下沉图是单一
         * 连通分量、不得不在分量内部切开时置真）：为真时镜像1 的 arm
         * 在复活前主动把镜像2 一并拉起，保证跨区方法调用时类已定义；
         * 为假时镜像2 严格按需映射（不触碰区2 shell 就永不映射）。
         */
        public boolean crossPart;

        public boolean isEmpty() {
            return classes.isEmpty();
        }

        public int methodCount() {
            int n = 0;
            for (ClassPlan cp : classes.values()) {
                n += cp.extract.size();
            }
            return n;
        }
    }

    // ==================================================================
    // 规划
    // ==================================================================

    public static Plan plan(Collection<ClassNode> nodes, Set<String> skipNames,
                            Set<String> relaxedNames, String mainClass, Random random) {
        Plan plan = new Plan();
        Map<String, ClassNode> byName = new HashMap<String, ClassNode>();
        for (ClassNode cn : nodes) {
            byName.put(cn.name, cn);
        }

        // 1) 类关系图并查集：InnerClasses + Nestmates(JDK11+) 边都要并入，
        //    保证一个 nest/嵌套整体下沉，隐藏侧 shell/$$n 两套 nest 各自闭合。
        //    接口/注解/枚举/模块不下沉，也不作为并集边（它们只当普通引用类型，
        //    例如"包含一个嵌套接口"的业务类不应被连坐）。
        Map<String, String> parent = new HashMap<String, String>();
        for (ClassNode cn : nodes) {
            parent.put(cn.name, cn.name);
        }
        for (ClassNode cn : nodes) {
            if (cn.innerClasses != null) {
                for (org.objectweb.asm.tree.InnerClassNode ic : cn.innerClasses) {
                    if (ic.name != null && ic.outerName != null
                            && byName.containsKey(ic.name)
                            && byName.containsKey(ic.outerName)
                            && sinkableKind(byName.get(ic.name).access)
                            && sinkableKind(byName.get(ic.outerName).access)) {
                        union(parent, ic.name, ic.outerName);
                    }
                }
            }
            if (cn.nestHostClass != null && byName.containsKey(cn.nestHostClass)
                    && sinkableKind(cn.access)
                    && sinkableKind(byName.get(cn.nestHostClass).access)) {
                union(parent, cn.name, cn.nestHostClass);
            }
            if (cn.nestMembers != null) {
                for (String m : cn.nestMembers) {
                    if (m != null && byName.containsKey(m)
                            && sinkableKind(cn.access) && sinkableKind(byName.get(m).access)) {
                        union(parent, cn.name, m);
                    }
                }
            }
        }

        // 1.5) 原始 nest 关系全集 + nest 成员的 private 成员表：用于发现
        //      "下沉簇与留下的 nest 成员之间仍有私有访问"的危险拆分
        //      （留下的通常是嵌套接口/枚举；公开成员跨非 nest 调用仍合法）
        Map<String, Set<String>> nestMates = new HashMap<String, Set<String>>();
        for (ClassNode cn : nodes) {
            if (cn.nestMembers != null && !cn.nestMembers.isEmpty()) {
                Set<String> nest = new HashSet<String>();
                nest.add(cn.name);
                for (String m : cn.nestMembers) {
                    if (m != null && byName.containsKey(m)) {
                        nest.add(m);
                    }
                }
                for (String m : nest) {
                    nestMates.put(m, nest);
                }
            }
        }
        Map<String, Set<String>> privateMethods = new HashMap<String, Set<String>>();
        Map<String, Set<String>> privateFields = new HashMap<String, Set<String>>();
        for (ClassNode cn : nodes) {
            for (MethodNode mn : cn.methods) {
                if ((mn.access & Opcodes.ACC_PRIVATE) != 0) {
                    Set<String> set = privateMethods.get(cn.name);
                    if (set == null) {
                        set = new HashSet<String>();
                        privateMethods.put(cn.name, set);
                    }
                    set.add(mn.name + ' ' + mn.desc);
                }
            }
            for (FieldNode f : cn.fields) {
                if ((f.access & Opcodes.ACC_PRIVATE) != 0) {
                    Set<String> set = privateFields.get(cn.name);
                    if (set == null) {
                        set = new HashSet<String>();
                        privateFields.put(cn.name, set);
                    }
                    set.add(f.name + ' ' + f.desc);
                }
            }
        }

        // 2) 簇 -> 成员
        Map<String, List<ClassNode>> clusters = new LinkedHashMap<String, List<ClassNode>>();
        for (ClassNode cn : nodes) {
            String root = find(parent, cn.name);
            List<ClassNode> list = clusters.get(root);
            if (list == null) {
                list = new ArrayList<ClassNode>();
                clusters.put(root, list);
            }
            list.add(cn);
        }

        // 3) 跨类静态字段访问：owner -> 访问它的类集合（仅跨类）。
        //    簇内互访允许（如 switch-map 合成持有者），跨簇才整簇否决
        Map<String, Set<String>> staticAccessors = new HashMap<String, Set<String>>();
        for (ClassNode cn : nodes) {
            for (MethodNode mn : cn.methods) {
                if (mn.instructions == null) {
                    continue;
                }
                for (AbstractInsnNode in : mn.instructions.toArray()) {
                    if (in instanceof FieldInsnNode) {
                        FieldInsnNode f = (FieldInsnNode) in;
                        if ((f.getOpcode() == Opcodes.GETSTATIC
                                || f.getOpcode() == Opcodes.PUTSTATIC)
                                && !f.owner.equals(cn.name)) {
                            Set<String> set = staticAccessors.get(f.owner);
                            if (set == null) {
                                set = new HashSet<String>();
                                staticAccessors.put(f.owner, set);
                            }
                            set.add(cn.name);
                        }
                    }
                }
            }
        }

        int fakeBudget = FAKE_CAP;
        for (List<ClassNode> members : clusters.values()) {
            Set<String> memberNames = new HashSet<String>();
            for (ClassNode cn : members) {
                memberNames.add(cn.name);
            }
            if (!clusterEligible(members, memberNames, byName, skipNames, relaxedNames,
                    mainClass, staticAccessors, nestMates, privateMethods,
                    privateFields)) {
                continue;
            }
            int relaxedInCluster = 0;
            for (ClassNode cn : members) {
                if (relaxedNames.contains(cn.name)) {
                    relaxedInCluster++;
                }
            }
            // 整簇成员都要进计划（无方法可抽的成员类只生成隐藏字节，
            // 供簇内隐藏代码引用，例如 new Setters$Box$$n）
            List<ClassPlan> cps = new ArrayList<ClassPlan>();
            int total = 0;
            for (ClassNode cn : members) {
                ClassPlan cp = new ClassPlan(cn, cn.name + HIDDEN_SUFFIX);
                for (MethodNode mn : cn.methods) {
                    if (methodEligible(mn)) {
                        cp.extract.add(new String[] { mn.name, mn.desc });
                        total++;
                    }
                }
                cps.add(cp);
            }
            // 普通簇至少要有一个可抽方法；放松名单的假类没有静态方法也要进
            // （40 个诱饵假方法在捕获前才灌入），但受数量上限保护
            if (total == 0 && relaxedInCluster == 0) {
                continue;
            }
            if (relaxedInCluster == members.size() && members.size() > fakeBudget) {
                continue;
            }
            fakeBudget -= relaxedInCluster;
            for (ClassPlan cp : cps) {
                plan.classes.put(cp.cn.name, cp);
            }
        }
        partition(plan);
        return plan;
    }

    // ==================================================================
    // 双 payload 分区
    // ==================================================================

    /**
     * 把全部计划类按「定义/运行时引用闭包」的连通分量整体二分（LPT 均衡），
     * 写入 {@link ClassPlan#group}。分量整体分配保证：区1 复活与执行时
     * 绝不引用未映射的区2 隐藏类，因此区2 可严格按需映射。
     *
     * <p>极端情况下整个下沉图只有一个连通分量：退化为类级均衡切分并置
     * {@link Plan#crossPart}，由镜像1 arm 主动拉起镜像2（仍只从加密资源
     * 经内存映射，只是时机提前到 boot）。</p>
     */
    private static void partition(Plan plan) {
        if (plan.classes.isEmpty()) {
            return;
        }
        // 1) 仅针对计划类的引用并查集：父类/接口/嵌套/nest + 字节码中
        //    出现的全部类型引用（方法/字段 owner、描述符、类型指令、
        //    try/catch、invokedynamic 等），宁滥勿缺。
        Map<String, String> par = new HashMap<String, String>();
        for (String n : plan.classes.keySet()) {
            par.put(n, n);
        }
        for (ClassPlan cp : plan.classes.values()) {
            ClassNode cn = cp.cn;
            Set<String> refs = new HashSet<String>();
            addType(refs, cn.superName);
            if (cn.interfaces != null) {
                for (String itf : cn.interfaces) {
                    addType(refs, itf);
                }
            }
            addType(refs, cn.nestHostClass);
            if (cn.nestMembers != null) {
                for (String m : cn.nestMembers) {
                    addType(refs, m);
                }
            }
            for (FieldNode f : cn.fields) {
                collectTypes(f.desc, refs);
            }
            for (MethodNode mn : cn.methods) {
                collectTypes(mn.desc, refs);
                if (mn.tryCatchBlocks != null) {
                    for (org.objectweb.asm.tree.TryCatchBlockNode tb
                            : mn.tryCatchBlocks) {
                        if (tb.type != null) {
                            addType(refs, tb.type);
                        }
                    }
                }
                if (mn.signature != null) {
                    collectTypes(mn.signature, refs);
                }
                if (mn.instructions != null) {
                    for (AbstractInsnNode in : mn.instructions.toArray()) {
                        if (in instanceof MethodInsnNode) {
                            MethodInsnNode m = (MethodInsnNode) in;
                            addType(refs, m.owner);
                            collectTypes(m.desc, refs);
                            if (in instanceof org.objectweb.asm.tree.InvokeDynamicInsnNode) {
                                org.objectweb.asm.tree.InvokeDynamicInsnNode idy =
                                        (org.objectweb.asm.tree.InvokeDynamicInsnNode) in;
                                collectTypes(idy.desc, refs);
                                if (idy.bsmArgs != null) {
                                    for (Object a : idy.bsmArgs) {
                                        if (a instanceof Type) {
                                            collectType((Type) a, refs);
                                        } else if (a instanceof org.objectweb.asm.Handle) {
                                            addType(refs,
                                                    ((org.objectweb.asm.Handle) a).getOwner());
                                        }
                                    }
                                }
                            }
                        } else if (in instanceof FieldInsnNode) {
                            FieldInsnNode f = (FieldInsnNode) in;
                            addType(refs, f.owner);
                            collectTypes(f.desc, refs);
                        } else if (in instanceof org.objectweb.asm.tree.TypeInsnNode) {
                            collectTypes(
                                    ((org.objectweb.asm.tree.TypeInsnNode) in).desc, refs);
                        } else if (in instanceof
                                org.objectweb.asm.tree.MultiANewArrayInsnNode) {
                            collectTypes(
                                    ((org.objectweb.asm.tree.MultiANewArrayInsnNode) in)
                                            .desc, refs);
                        } else if (in instanceof LdcInsnNode) {
                            Object cst = ((LdcInsnNode) in).cst;
                            if (cst instanceof Type) {
                                collectType((Type) cst, refs);
                            }
                        }
                    }
                }
            }
            for (String r : refs) {
                if (par.containsKey(r)) {
                    union(par, cn.name, r);
                }
            }
        }

        // 2) 连通分量（保持计划顺序）
        Map<String, List<ClassPlan>> comps = new LinkedHashMap<String, List<ClassPlan>>();
        for (ClassPlan cp : plan.classes.values()) {
            String root = find(par, cp.cn.name);
            List<ClassPlan> list = comps.get(root);
            if (list == null) {
                list = new ArrayList<ClassPlan>();
                comps.put(root, list);
            }
            list.add(cp);
        }

        // 3) 整体分量 LPT 二分；单分量退化为类级切分 + crossPart
        List<List<ClassPlan>> units = new ArrayList<List<ClassPlan>>(comps.values());
        if (units.size() == 1 && plan.classes.size() >= 2) {
            plan.crossPart = true;
            List<ClassPlan> all = units.get(0);
            List<ClassPlan> g0 = new ArrayList<ClassPlan>();
            List<ClassPlan> g1 = new ArrayList<ClassPlan>();
            long w0 = 0, w1 = 0;
            for (ClassPlan cp : all) {
                long w = Math.max(1, cp.extract.size());
                if (w0 <= w1) { g0.add(cp); w0 += w; cp.group = 0; }
                else { g1.add(cp); w1 += w; cp.group = 1; }
            }
            return;
        }
        List<ClassPlan> g0 = new ArrayList<ClassPlan>();
        List<ClassPlan> g1 = new ArrayList<ClassPlan>();
        long w0 = 0, w1 = 0;
        // 重分量优先（LPT）
        List<List<ClassPlan>> ordered =
                new ArrayList<List<ClassPlan>>(units);
        java.util.Collections.sort(ordered,
                new java.util.Comparator<List<ClassPlan>>() {
                    @Override
                    public int compare(List<ClassPlan> a, List<ClassPlan> b) {
                        return Long.valueOf(weight(b)).compareTo(Long.valueOf(weight(a)));
                    }
                });
        for (List<ClassPlan> unit : ordered) {
            int g = w0 <= w1 ? 0 : 1;
            for (ClassPlan cp : unit) {
                cp.group = g;
                if (g == 0) { g0.add(cp); } else { g1.add(cp); }
            }
            if (g == 0) { w0 += weight(unit); } else { w1 += weight(unit); }
        }
    }

    private static long weight(List<ClassPlan> unit) {
        long w = 0;
        for (ClassPlan cp : unit) {
            // shell 类还会灌入固定数量诱饵假方法，计一份常量权重
            w += Math.max(1, cp.extract.size())
                    + (cp.extract.isEmpty() ? 0 : J2c.DECOY_METHODS);
        }
        return w;
    }

    private static void addType(Set<String> refs, String internalOrDesc) {
        if (internalOrDesc == null) {
            return;
        }
        if (internalOrDesc.indexOf('(') >= 0 || internalOrDesc.indexOf('[') >= 0
                || (internalOrDesc.length() > 0
                && internalOrDesc.charAt(internalOrDesc.length() - 1) == ';')) {
            collectTypes(internalOrDesc, refs);
        } else {
            refs.add(internalOrDesc);
        }
    }

    private static void collectTypes(String desc, Set<String> refs) {
        if (desc == null || desc.indexOf('L') < 0) {
            return;
        }
        try {
            int p = 0;
            while (p < desc.length()) {
                char c = desc.charAt(p);
                if (c == 'L') {
                    int semi = desc.indexOf(';', p);
                    if (semi < 0) {
                        break;
                    }
                    refs.add(desc.substring(p + 1, semi));
                    p = semi + 1;
                } else {
                    p++;
                }
            }
        } catch (RuntimeException ignored) {
            // 签名等非严格描述符：退化为正则式抽取 Lx; 形态
            int start = 0;
            for (;;) {
                int a = desc.indexOf('L', start);
                if (a < 0) {
                    break;
                }
                int b = desc.indexOf(';', a);
                if (b < 0) {
                    break;
                }
                refs.add(desc.substring(a + 1, b));
                start = b + 1;
            }
        }
    }

    private static void collectType(Type t, Set<String> refs) {
        if (t == null) {
            return;
        }
        // 注意：Type.INTERNAL 在 ASM 中不公开，且 getSort() 会把
        // INTERNAL 形态归一为 OBJECT
        if (t.getSort() == Type.OBJECT) {
            refs.add(t.getInternalName());
        } else if (t.getSort() == Type.ARRAY) {
            collectType(t.getElementType(), refs);
        } else if (t.getSort() == Type.METHOD) {
            collectType(t.getReturnType(), refs);
            for (Type a : t.getArgumentTypes()) {
                collectType(a, refs);
            }
        }
    }

    private static boolean sinkableKind(int access) {
        return (access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_ENUM | Opcodes.ACC_MODULE)) == 0;
    }

    private static boolean clusterEligible(List<ClassNode> members,
                                           Set<String> memberNames,
                                           Map<String, ClassNode> byName,
                                           Set<String> skipNames, Set<String> relaxedNames,
                                           String mainClass,
                                           Map<String, Set<String>> staticAccessors,
                                           Map<String, Set<String>> nestMates,
                                           Map<String, Set<String>> privateMethods,
                                           Map<String, Set<String>> privateFields) {
        for (ClassNode cn : members) {
            if (skipNames.contains(cn.name) || cn.name.equals(mainClass)) {
                return false;
            }
            int a = cn.access;
            if ((a & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                    | Opcodes.ACC_ENUM | Opcodes.ACC_MODULE)) != 0) {
                return false;
            }
            // 支持任意 class 文件版本：隐藏字节原样保留版本号，DefineClass
            // 由实际运行的 JVM 负责（高版本 class 本就需要高版本 JVM 运行）。
            // Nestmates（JDK11+）/匿名/局部/内部类（EnclosingMethod）不再否决：
            // nest 关系已整体并入簇，隐藏侧 NestHost/NestMembers 随改名重写，
            // shell 与 $$n 各自形成闭合的 nest；跨类私有访问在两侧都合法。
            // NestHost/NestMembers 允许指向簇外成员（典型：同 nest 的嵌套
            // 接口/枚举不下沉）：host 成员表是多对多的声明，JVM 只在真正
            // 发生 private 访问时校验；下面的指令扫描会拦截这种情况。
            // 隐藏侧属性经 ClassRemapper 重写：簇内变 $$n，簇外保留 shell
            // 原名（该类仍在 jar 中），两侧引用各自可解析。
            if (!isAscii(cn.name)) {
                return false;
            }
            if (cn.name.endsWith("package-info") || cn.name.endsWith("module-info")) {
                return false;
            }
            if (!relaxedNames.contains(cn.name)) {
                // 非放松类允许静态字段，但仅限 shell/隐藏两侧状态天然一致的：
                //   1) 合成字段（编译器生成，如 switch-map $SwitchMap 表）；
                //   2) 带 ConstantValue 的 final 编译期常量。
                // 普通可变静态字段仍整簇否决（shell 实例方法与隐藏静态方法
                // 会各自读写一份，语义分裂）。放松名单假类 shell 全空心，豁免。
                for (FieldNode f : cn.fields) {
                    if ((f.access & Opcodes.ACC_STATIC) == 0) {
                        continue;
                    }
                    boolean synthetic = (f.access & Opcodes.ACC_SYNTHETIC) != 0;
                    boolean constant = (f.access & Opcodes.ACC_FINAL) != 0
                            && f.value != null;
                    if (!synthetic && !constant) {
                        return false;
                    }
                }
            }
            // 簇级静态访问检查：任一方向跨簇即否决
            Set<String> accessors = staticAccessors.get(cn.name);
            if (accessors != null) {
                for (String ac : accessors) {
                    if (!memberNames.contains(ac)) {
                        return false;
                    }
                }
            }
            for (MethodNode mn : cn.methods) {
                if (!isAscii(mn.name) || !isAscii(mn.desc)) {
                    return false;
                }
                if (relaxedNames.contains(cn.name) || mn.instructions == null) {
                    continue;
                }
                Set<String> mates = nestMates.get(cn.name);
                for (AbstractInsnNode in : mn.instructions.toArray()) {
                    if (in instanceof FieldInsnNode) {
                        FieldInsnNode f = (FieldInsnNode) in;
                        boolean cross = !f.owner.equals(cn.name)
                                && !memberNames.contains(f.owner);
                        if ((f.getOpcode() == Opcodes.GETSTATIC
                                || f.getOpcode() == Opcodes.PUTSTATIC) && cross) {
                            return false;
                        }
                        // 对留在簇外的 nest 成员做私有字段访问：改名后 nest
                        // 不再闭合，会 IllegalAccessError，整簇放弃
                        if (cross && mates != null && mates.contains(f.owner)) {
                            Set<String> pf = privateFields.get(f.owner);
                            if (pf != null && pf.contains(f.name + ' ' + f.desc)) {
                                return false;
                            }
                        }
                    } else if (in instanceof MethodInsnNode) {
                        MethodInsnNode m = (MethodInsnNode) in;
                        if (!m.owner.equals(cn.name) && !memberNames.contains(m.owner)
                                && mates != null && mates.contains(m.owner)) {
                            Set<String> pm = privateMethods.get(m.owner);
                            if (pm != null && pm.contains(m.name + ' ' + m.desc)) {
                                return false;
                            }
                        }
                    }
                }
            }
        }
        return true;
    }

    /** 静态、非 native/abstract、非 &lt;clinit&gt;、描述符可桥接。 */
    static boolean methodEligible(MethodNode mn) {
        int a = mn.access;
        if ((a & Opcodes.ACC_STATIC) == 0) {
            return false;
        }
        if ((a & (Opcodes.ACC_NATIVE | Opcodes.ACC_ABSTRACT)) != 0) {
            return false;
        }
        if (mn.name.equals("<clinit>")) {
            return false;
        }
        return descBridgeable(mn.desc);
    }

    /**
     * 描述符桥接规则：基本类型只允许 Z/B/C/S/I/J/F/D；其余（任意对象、数组）
     * 统一按 jobject 透传；返回允许 V。这些覆盖了正常 Java 源码的全部产物。
     */
    static boolean descBridgeable(String desc) {
        int i = desc.indexOf(')');
        if (i < 0 || !desc.startsWith("(")) {
            return false;
        }
        int p = 1;
        while (p < i) {
            while (p < i && desc.charAt(p) == '[') {
                p++;
            }
            if (p >= i) {
                return false;
            }
            char c = desc.charAt(p);
            if (c == 'L') {
                int semi = desc.indexOf(';', p);
                if (semi < 0 || semi > i) {
                    return false;
                }
                p = semi + 1;
            } else {
                if ("ZBCSIJFD".indexOf(c) < 0) {
                    return false;
                }
                p++;
            }
        }
        char r = desc.charAt(i + 1);
        if (r == 'V' || "ZBCSIJFD".indexOf(r) >= 0) {
            return true;
        }
        if (r == 'L' || r == '[') {
            return true;
        }
        return false;
    }

    /** 返回类型分类：V / I（含 ZBCS）/ J / F / D / L（对象与数组）。 */
    public static char returnKind(String desc) {
        char r = desc.charAt(desc.indexOf(')') + 1);
        if (r == 'V') {
            return 'V';
        }
        if (r == 'J' || r == 'F' || r == 'D') {
            return r;
        }
        if (r == 'L' || r == '[') {
            return 'L';
        }
        return 'I';
    }

    private static boolean isAscii(String s) {
        for (int i = 0; i < s.length(); i++) {
            if (s.charAt(i) > 127) {
                return false;
            }
        }
        return true;
    }

    private static String find(Map<String, String> parent, String x) {
        String p = parent.get(x);
        if (p == null) {
            return x;
        }
        if (!p.equals(x)) {
            p = find(parent, p);
            parent.put(x, p);
        }
        return p;
    }

    private static void union(Map<String, String> parent, String a, String b) {
        String ra = find(parent, a);
        String rb = find(parent, b);
        if (!ra.equals(rb)) {
            parent.put(ra, rb);
        }
    }

    // ==================================================================
    // Shell 化
    // ==================================================================

    /**
     * 基于含诱饵假方法的完整节点生成一个全新的 shell 节点（原节点不动，
     * 失败回退零污染）：抽取方法转 native、&lt;clinit&gt; 换成桥接加载。
     *
     * @param hollow 全空心模式（伪代码假类）：删除全部字段、构造器与实例方法，
     *               shell 只剩 native 静态声明 + boot clinit。假类在 shell
     *               世界永不被实例化，实例逻辑只存在于隐藏 blob。
     */
    public static ClassNode shell(ClassPlan cp, String bootName, Random random,
                                  boolean hollow) {
        ClassNode src = cp.full != null ? cp.full : cp.cn;
        ClassNode cn = new ClassNode(Opcodes.ASM9);
        src.accept(cn);
        Set<String> extractKeys = new HashSet<String>();
        for (String[] k : cp.extract) {
            extractKeys.add(k[0] + ' ' + k[1]);
        }

        int matched = 0;
        for (int idx = 0; idx < cn.methods.size(); idx++) {
            MethodNode mn = cn.methods.get(idx);
            if (!extractKeys.contains(mn.name + ' ' + mn.desc)) {
                continue;
            }
            matched++;
            int access = mn.access | Opcodes.ACC_NATIVE;
            // 同步语义已包含在隐藏方法字节码内，shell native 不再包监控
            access &= ~Opcodes.ACC_SYNCHRONIZED;
            MethodNode nat = new MethodNode(Opcodes.ASM9, access, mn.name, mn.desc,
                    mn.signature,
                    mn.exceptions == null ? null
                            : mn.exceptions.toArray(new String[mn.exceptions.size()]));
            cn.methods.set(idx, nat);
        }
        if (matched != cp.extract.size()) {
            throw new IllegalStateException("j2c shell 化失败：方法匹配数 "
                    + matched + "/" + cp.extract.size() + " @ " + cn.name);
        }

        if (hollow) {
            // 全空心：字段全部移除；除 native 声明外的方法（<init>/实例方法/
            // 未被抽取的静态方法）全部移除，Java 层不留任何假逻辑
            cn.fields.clear();
            for (int idx = cn.methods.size() - 1; idx >= 0; idx--) {
                MethodNode mn = cn.methods.get(idx);
                if ((mn.access & Opcodes.ACC_NATIVE) == 0
                        && !mn.name.equals("<clinit>")) {
                    cn.methods.remove(idx);
                }
            }
        }

        // <clinit> 策略：
        //  - hollow（假类）或无静态字段的真实类：替换为仅 boot.load
        //  - 含保留静态字段的真实类（合成表/编译期常量）：保留原 clinit，
        //    在头部前插 boot.load，shell 侧静态状态正常初始化，与隐藏侧
        //    各自独立且值确定（合成表由枚举序数确定性生成，常量内联）
        boolean keepClinit = !hollow;
        if (keepClinit) {
            keepClinit = false;
            for (FieldNode f : cp.cn.fields) {
                if ((f.access & Opcodes.ACC_STATIC) != 0) {
                    keepClinit = true;
                    break;
                }
            }
        }
        InsnList bootSeq = new InsnList();
        bootSeq.add(new LdcInsnNode(Type.getObjectType(cn.name)));
        bootSeq.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                bootName, "tie", "(Ljava/lang/Class;)V", false));
        if (keepClinit) {
            MethodNode oldClinit = null;
            for (MethodNode mn : cn.methods) {
                if (mn.name.equals("<clinit>")) {
                    oldClinit = mn;
                    break;
                }
            }
            if (oldClinit != null) {
                oldClinit.instructions.insert(bootSeq);
            } else {
                // 仅 ConstantValue 常量字段时 javac 不生成 clinit（常量由
                // VM 按字段属性直接初始化），补一个仅 boot.tie 的即可
                MethodNode clinit = new MethodNode(Opcodes.ASM9,
                        Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC, "<clinit>", "()V",
                        null, null);
                clinit.instructions.add(bootSeq);
                clinit.instructions.add(new InsnNode(Opcodes.RETURN));
                clinit.maxStack = 0;
                clinit.maxLocals = 0;
                cn.methods.add(0, clinit);
            }
        } else {
            for (int idx = 0; idx < cn.methods.size(); idx++) {
                MethodNode mn = cn.methods.get(idx);
                if (mn.name.equals("<clinit>")) {
                    cn.methods.remove(idx);
                    break;
                }
            }
            MethodNode clinit = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC, "<clinit>", "()V",
                    null, null);
            clinit.instructions.add(bootSeq);
            clinit.instructions.add(new InsnNode(Opcodes.RETURN));
            clinit.maxStack = 0;
            clinit.maxLocals = 0;
            cn.methods.add(0, clinit);
        }

        // Java 层伪装：纯 Java 伪工具方法（有界循环/字符串/数组/不透明谓词），
        // 其中夹杂对本类 native 的调用（恒不被执行，但静态上让 native 引用
        // 分散在正常代码里，而不是一堆扎眼的 native 声明）。hollow 假类无
        // 字段，伪方法同样只用参数与局部变量。
        injectShellCamouflage(cn, random);
        return cn;
    }

    // ==================================================================
    // Shell Java 层伪装：伪工具方法 + native 调用穿插
    // ==================================================================

    private static final String[] CAMO_WORDS = {
            "checksum", "foldHash", "normalize", "mixInto", "applyMask",
            "tabAt", "fillTable", "seqValue", "canReuse", "hashOf",
            "parseToken", "appendEscaped", "drainBuffer", "stampBuf",
            "indexRange", "digest16", "retainMask", "coalesce",
            "inflate32", "deflate32", "scanChunk", "mergeStep",
    };
    private static final String[] CAMO_STRINGS = { "-", "x", "v=", "n=", "k" };

    /**
     * 向 shell 注入 6~9 个外观正常的 private static synthetic 工具方法：
     * 有界循环 / StringBuilder / 数组求和 / TABLESWITCH 风格分支 / 不透明
     * 谓词 / 嵌套循环 / long 算术。约 2/3 的方法在算术缝隙中穿插一次对本类
     * native 方法的调用（结果丢弃）——这些方法本身永不被调用，因此零运行时
     * 风险，但静态反编译时 native 引用分散在“正常业务”里。
     */
    private static void injectShellCamouflage(ClassNode cn, Random random) {
        List<String[]> natives = new ArrayList<String[]>();
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
            if ((mn.access & Opcodes.ACC_NATIVE) != 0
                    && (mn.access & Opcodes.ACC_STATIC) != 0) {
                natives.add(new String[] { mn.name, mn.desc });
            }
        }
        if (natives.isEmpty()) {
            return;
        }
        int want = 6 + random.nextInt(4);
        int made = 0;
        int guard = 0;
        while (made < want && guard++ < want * 4) {
            MethodNode mn;
            switch (random.nextInt(7)) {
                case 0:
                    mn = camoStorm(cn, random, natives);
                    break;
                case 1:
                    mn = camoBuilder(cn, random, natives);
                    break;
                case 2:
                    mn = camoArray(cn, random, natives);
                    break;
                case 3:
                    mn = camoChurn(cn, random, natives);
                    break;
                case 4:
                    mn = camoObject(cn, random, natives);
                    break;
                case 5:
                    mn = camoNested(cn, random, natives);
                    break;
                default:
                    mn = camoLong(cn, random, natives);
                    break;
            }
            if (mn == null || !used.add(mn.name)) {
                continue;
            }
            // 随机穿插在成员之间，但 <clinit> 永远置首
            int pos = 1 + random.nextInt(cn.methods.size());
            cn.methods.add(pos, mn);
            made++;
        }
    }

    private static String camoName(Set<String> used, Random random) {
        for (int t = 0; ; t++) {
            String n = CAMO_WORDS[random.nextInt(CAMO_WORDS.length)]
                    + (t == 0 ? "" : String.valueOf(t));
            if (!used.contains(n)) {
                return n;
            }
        }
    }

    private static MethodNode newCamo(Set<String> used, Random random, String desc) {
        return new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                camoName(used, random), desc, null, null);
    }

    /** 以 65% 概率在当前（必须栈空）位置穿插一次本类 native 调用，结果丢弃。 */
    private static void maybeNative(InsnList il, ClassNode cn, Random random,
                                    List<String[]> natives) {
        if (random.nextInt(100) >= 65) {
            return;
        }
        String[] nm = natives.get(random.nextInt(natives.size()));
        invokeNative(il, cn.name, nm);
    }

    /** 按描述符压入“零值”参数调用静态 native，并弹出返回值（永不真正执行）。 */
    private static void invokeNative(InsnList il, String owner, String[] nm) {
        String desc = nm[1];
        int end = desc.indexOf(')');
        int p = 1;
        while (p < end) {
            char c = desc.charAt(p);
            if (c == 'L') {
                il.add(new InsnNode(Opcodes.ACONST_NULL));
                p = desc.indexOf(';', p) + 1;
            } else if (c == '[') {
                while (p < end && desc.charAt(p) == '[') {
                    p++;
                }
                if (desc.charAt(p) == 'L') {
                    p = desc.indexOf(';', p) + 1;
                } else {
                    p++;
                }
                il.add(new InsnNode(Opcodes.ACONST_NULL));
            } else {
                switch (c) {
                    case 'J':
                        il.add(new InsnNode(Opcodes.LCONST_0));
                        break;
                    case 'F':
                        il.add(new InsnNode(Opcodes.FCONST_0));
                        break;
                    case 'D':
                        il.add(new InsnNode(Opcodes.DCONST_0));
                        break;
                    default:
                        il.add(new InsnNode(Opcodes.ICONST_0));
                        break;
                }
                p++;
            }
        }
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, owner, nm[0], desc, false));
        char r = desc.charAt(end + 1);
        if (r != 'V') {
            il.add(new InsnNode((r == 'J' || r == 'D') ? Opcodes.POP2 : Opcodes.POP));
        }
    }

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

    /** (II)I 算术风暴 + 有界循环。 */
    private static MethodNode camoStorm(ClassNode cn, Random random,
                                        List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "(II)I");
        InsnList il = m.instructions;
        pushInt(il, 0x9e00 + random.nextInt(0x100));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        pushInt(il, 3 + random.nextInt(5));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new VarInsnNode(Opcodes.ISTORE, 9));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 10));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 10));
        pushInt(il, 4 + random.nextInt(5));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new VarInsnNode(Opcodes.ILOAD, 10));
        pushInt(il, 3 + random.nextInt(29));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        maybeNative(il, cn, random, natives);
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new VarInsnNode(Opcodes.ILOAD, 10));
        il.add(new InsnNode(Opcodes.IADD));
        pushInt(il, 13 + random.nextInt(40));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ISTORE, 9));
        il.add(new IincInsnNode(10, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** (I)Ljava/lang/String; StringBuilder 有界拼接。 */
    private static MethodNode camoBuilder(ClassNode cn, Random random,
                                          List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "(I)Ljava/lang/String;");
        InsnList il = m.instructions;
        il.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.NEW,
                "java/lang/StringBuilder"));
        il.add(new InsnNode(Opcodes.DUP));
        pushInt(il, 16);
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/StringBuilder", "<init>", "(I)V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, 8));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 9));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new IntInsnNode(Opcodes.BIPUSH, 7));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new InsnNode(Opcodes.ICONST_2));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, 8));
        il.add(new LdcInsnNode(
                CAMO_STRINGS[random.nextInt(CAMO_STRINGS.length)]));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "append",
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;", false));
        il.add(new InsnNode(Opcodes.POP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 8));
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        pushInt(il, random.nextInt(7));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "append",
                "(I)Ljava/lang/StringBuilder;", false));
        il.add(new InsnNode(Opcodes.POP));
        maybeNative(il, cn, random, natives);
        il.add(new IincInsnNode(9, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ALOAD, 8));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "toString",
                "()Ljava/lang/String;", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return m;
    }

    /** ([II)I 有界数组求和。 */
    private static MethodNode camoArray(ClassNode cn, Random random,
                                        List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "([II)I");
        InsnList il = m.instructions;
        LabelNode nonNull = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, nonNull));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(nonNull);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 9));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new InsnNode(Opcodes.ARRAYLENGTH));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        pushInt(il, 12);
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new InsnNode(Opcodes.IALOAD));
        pushInt(il, 3);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        maybeNative(il, cn, random, natives);
        il.add(new IincInsnNode(9, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** ()V 恒真不透明谓词，假路径同样穿插 native 调用。 */
    private static MethodNode camoChurn(ClassNode cn, Random random,
                                        List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "()V");
        InsnList il = m.instructions;
        pushInt(il, 0x1000 + random.nextInt(0x3000));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        LabelNode dead = new LabelNode();
        LabelNode merge = new LabelNode();
        // (v | 1) == 0 恒假：真路径直接落到 merge
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IOR));
        il.add(new JumpInsnNode(Opcodes.IFEQ, dead));
        maybeNative(il, cn, random, natives);
        il.add(new JumpInsnNode(Opcodes.GOTO, merge));
        il.add(dead);
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        pushInt(il, 0x55aa);
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        maybeNative(il, cn, random, natives);
        il.add(merge);
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IOR));
        il.add(new InsnNode(Opcodes.POP));
        il.add(new InsnNode(Opcodes.RETURN));
        return m;
    }

    /** (Ljava/lang/Object;)Z 空值/hash 判断。 */
    private static MethodNode camoObject(ClassNode cn, Random random,
                                         List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "(Ljava/lang/Object;)Z");
        InsnList il = m.instructions;
        LabelNode nonNull = new LabelNode();
        LabelNode zero = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new JumpInsnNode(Opcodes.IFNONNULL, nonNull));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(nonNull);
        maybeNative(il, cn, random, natives);
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, "java/lang/Object",
                "hashCode", "()I", false));
        pushInt(il, 255);
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new JumpInsnNode(Opcodes.IFEQ, zero));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(zero);
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** (III)I 双层有界循环。 */
    private static MethodNode camoNested(ClassNode cn, Random random,
                                         List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "(III)I");
        InsnList il = m.instructions;
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 9));
        LabelNode oi = new LabelNode();
        LabelNode oe = new LabelNode();
        LabelNode ii = new LabelNode();
        LabelNode ie = new LabelNode();
        il.add(oi);
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.ICONST_3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, oe));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 10));
        il.add(ii);
        il.add(new VarInsnNode(Opcodes.ILOAD, 10));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ICONST_3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, ie));
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new VarInsnNode(Opcodes.ILOAD, 9));
        pushInt(il, 7);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 10));
        pushInt(il, 13);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 8));
        maybeNative(il, cn, random, natives);
        il.add(new IincInsnNode(10, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, ii));
        il.add(ie);
        il.add(new IincInsnNode(9, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, oi));
        il.add(oe);
        il.add(new VarInsnNode(Opcodes.ILOAD, 8));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /** (J)J long 算术 + 有界循环。 */
    private static MethodNode camoLong(ClassNode cn, Random random,
                                       List<String[]> natives) {
        Set<String> used = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            used.add(mn.name);
        }
        MethodNode m = newCamo(used, random, "(J)J");
        InsnList il = m.instructions;
        il.add(new VarInsnNode(Opcodes.LLOAD, 0));
        il.add(new LdcInsnNode(Long.valueOf(0x9e3779b97f4a7c15L)));
        il.add(new InsnNode(Opcodes.LXOR));
        il.add(new VarInsnNode(Opcodes.LSTORE, 8));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 10));
        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(loop);
        il.add(new VarInsnNode(Opcodes.ILOAD, 10));
        pushInt(il, 4 + random.nextInt(4));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.LLOAD, 8));
        il.add(new VarInsnNode(Opcodes.LLOAD, 0));
        il.add(new InsnNode(Opcodes.LADD));
        il.add(new LdcInsnNode(Long.valueOf(0x517cc1b727220a95L)));
        il.add(new InsnNode(Opcodes.LMUL));
        il.add(new VarInsnNode(Opcodes.LSTORE, 8));
        maybeNative(il, cn, random, natives);
        il.add(new IincInsnNode(10, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.LLOAD, 8));
        il.add(new InsnNode(Opcodes.LRETURN));
        return m;
    }

    // ==================================================================
    // 隐藏类编码：重映射 + 剥离结构性属性
    // ==================================================================

    /** @return 隐藏类内部名 -> 重写后的字节码 */
    public static Map<String, byte[]> encodeHidden(Plan plan,
                                                   Map<String, byte[]> fullBytes) {
        final Map<String, String> rename = new HashMap<String, String>();
        for (ClassPlan cp : plan.classes.values()) {
            rename.put(cp.cn.name, cp.hiddenName);
        }
        Remapper remapper = new Remapper() {
            @Override
            public String map(String internalName) {
                String h = rename.get(internalName);
                return h != null ? h : internalName;
            }
        };

        Map<String, byte[]> out = new LinkedHashMap<String, byte[]>();
        for (ClassPlan cp : plan.classes.values()) {
            byte[] full = fullBytes.get(cp.cn.name);
            if (full == null) {
                throw new IllegalStateException(
                        "j2c: 缺少完整字节码捕获: " + cp.cn.name);
            }
            ClassReader cr = new ClassReader(full);
            ClassWriter cw = new ClassWriter(0);
            ClassVisitor sink = new ClassVisitor(Opcodes.ASM9, cw) {
                @Override
                public void visitInnerClass(String name, String outerName,
                                            String innerName, int access) {
                    // 隐藏类与 InnerClasses 元数据脱钩
                }

                @Override
                public void visitOuterClass(String owner, String name, String desc) {
                    // 剥 EnclosingMethod
                }

                // 注意：NestHost/NestMembers 必须保留（ClassRemapper 已把名字
                // 改成 $$n 闭合集合），否则 JDK11+ 跨类 private 访问校验失败
            };
            cr.accept(new ClassRemapper(sink, remapper), 0);
            out.put(cp.hiddenName, cw.toByteArray());
        }
        return out;
    }
}
