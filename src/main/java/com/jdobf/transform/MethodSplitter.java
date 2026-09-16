package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.MultiANewArrayInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.lang.reflect.Constructor;
import java.lang.reflect.Member;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;

/**
 * 类拆分与重定向。
 *
 * 开启后，真实类中符合条件的 static 方法会被<b>整体迁移</b>到同包的伪代码类里
 * （每个方法随机挑选一个载体），原方法位置只留下一个等价的转发桩：
 * <pre>
 *   static int gcd(int a,int b){ return Carrier.gcd(a,b); }
 * </pre>
 * 载体伪代码类因此混进了真正的业务逻辑（迁移方法随后与伪代码方法一起被
 * 字符串加密 / 数字混淆 / 控制流平坦化同等处理）；而另有一部分伪代码类
 * 被刻意保留为<b>纯诱饵</b>（一个真方法都拿不到），静态分析无法区分
 * “真藏身处”与“空壳”。
 *
 * 合法性保证（全部在全局改名映射构建<b>之前</b>完成，之后由 GlobalRemapper
 * 统一改名、ClassRemapper 统一改写引用）：
 * <ul>
 *   <li>载体必须与源类同包：包私有/protected（同包部分）天然可访问；</li>
 *   <li>方法体引用到的 jar 内非 public 字段/方法一律提升为 public；</li>
 *   <li>方法体引用到的外部（JDK/第三方）成员通过反射确认是 public，
 *       无法确认则放弃迁移该方法（fail-closed），杜绝 IllegalAccessError；</li>
 *   <li>自递归调用的 owner 改写为载体，避免 桩→本体→桩 无限循环；</li>
 *   <li>native/synchronized/合成/桥接/注解方法、含 invokedynamic 的方法、
 *       接口/注解类的方法不迁移；main、&lt;clinit&gt; 不迁移。</li>
 * </ul>
 */
public final class MethodSplitter {

    private static final int ASM = Opcodes.ASM9;

    /** 一次迁移计划：源类、方法、载体与需要开放访问的成员。 */
    private static final class Move {
        final ClassNode from;
        final MethodNode method;
        final int index;
        final ClassNode carrier;
        final List<MemberRef> widen;

        Move(ClassNode from, MethodNode method, int index,
             ClassNode carrier, List<MemberRef> widen) {
            this.from = from;
            this.method = method;
            this.index = index;
            this.carrier = carrier;
            this.widen = widen;
        }
    }

    private static final class MemberRef {
        final String owner;
        final String name;
        final String desc;
        final boolean isField;

        MemberRef(String owner, String name, String desc, boolean isField) {
            this.owner = owner;
            this.name = name;
            this.desc = desc;
            this.isField = isField;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof MemberRef)) {
                return false;
            }
            MemberRef r = (MemberRef) o;
            return isField == r.isField && owner.equals(r.owner)
                    && name.equals(r.name) && desc.equals(r.desc);
        }

        @Override
        public int hashCode() {
            return owner.hashCode() * 31 + name.hashCode()
                    + (isField ? 1 : 0);
        }
    }

    /** 结果统计。 */
    public static final class Stats {
        public int movedMethods;
        public int carriersUsed;
        public int decoys;
        public int skippedMethods;
    }

    /** 外部类型/成员的反射解析缓存（构建期 JVM 上做，JDK 自身类为主）。 */
    private final Map<String, Class<?>> classCache = new HashMap<String, Class<?>>();

    private final Map<String, ClassNode> nodes;
    private final Set<String> excluded;
    private final Random random;

    private MethodSplitter(Map<String, ClassNode> nodes, Set<String> excluded,
                           Random random) {
        this.nodes = nodes;
        this.excluded = excluded;
        this.random = random;
    }

    /**
     * 执行拆分。
     *
     * @param nodes    全部类节点（已含伪代码类/分发空壳）
     * @param realNames 原始真实类内部名快照（不含注入的伪代码类）
     * @param excluded 被排除（不参与混淆）的类
     * @param carriers 可作为载体的伪代码类内部名（不含分发空壳）
     */
    public static Stats apply(Map<String, ClassNode> nodes,
                              Set<String> realNames, Set<String> excluded,
                              List<String> carriers, Random random) {
        return new MethodSplitter(nodes, excluded, random)
                .run(realNames, carriers);
    }

    private Stats run(Set<String> realNames, List<String> carrierNames) {
        Stats stats = new Stats();

        // 1. 载体池：同包分组；若载体 >=2 随机永久预留一个纯诱饵，
        //    保证“有的假类没有真逻辑”
        Map<String, List<ClassNode>> carriersByPackage =
                new LinkedHashMap<String, List<ClassNode>>();
        for (String name : carrierNames) {
            ClassNode cn = nodes.get(name);
            if (cn == null) {
                continue;
            }
            String pkg = packageOf(name);
            List<ClassNode> list = carriersByPackage.get(pkg);
            if (list == null) {
                list = new ArrayList<ClassNode>();
                carriersByPackage.put(pkg, list);
            }
            list.add(cn);
        }
        for (List<ClassNode> list : carriersByPackage.values()) {
            if (list.size() >= 2) {
                int decoyIdx = random.nextInt(list.size());
                list.remove(decoyIdx);
            }
        }

        // 2. 先扫描生成完整计划（不做任何修改），确认全部合法后再统一落盘
        List<Move> plan = new ArrayList<Move>();
        for (String realName : new TreeSet<String>(realNames)) {
            if (excluded.contains(realName)) {
                continue;
            }
            ClassNode cn = nodes.get(realName);
            if (cn == null || !canDonate(cn)) {
                continue;
            }
            List<ClassNode> samePkg = carriersByPackage.get(packageOf(realName));
            if (samePkg == null || samePkg.isEmpty()) {
                continue;
            }
            List<MethodNode> methods = cn.methods;
            for (int idx = 0; idx < methods.size(); idx++) {
                MethodNode m = methods.get(idx);
                if (!eligible(m)) {
                    continue;
                }
                List<MemberRef> widen = new ArrayList<MemberRef>();
                if (!bodyLegal(cn, m, widen)) {
                    stats.skippedMethods++;
                    continue;
                }
                ClassNode carrier = samePkg.get(random.nextInt(samePkg.size()));
                plan.add(new Move(cn, m, idx, carrier, widen));
            }
        }

        // 3. 统一执行：先开放访问权，再迁移方法、插桩
        Set<String> usedCarriers = new TreeSet<String>();
        for (Move move : plan) {
            for (MemberRef ref : move.widen) {
                widenToPublic(ref);
            }
            moveMethod(move);
            usedCarriers.add(move.carrier.name);
        }

        stats.movedMethods = plan.size();
        stats.carriersUsed = usedCarriers.size();
        // 被预留的 + 随机没被选中的，都是纯诱饵
        stats.decoys = carrierNames.size() - stats.carriersUsed;
        return stats;
    }

    // ------------------------------------------------------------------
    // 资格与合法性
    // ------------------------------------------------------------------

    /** 类是否可以捐出静态方法：不要接口/注解/模块/包说明。 */
    private boolean canDonate(ClassNode cn) {
        int flags = cn.access;
        if ((flags & Opcodes.ACC_INTERFACE) != 0
                || (flags & Opcodes.ACC_ANNOTATION) != 0) {
            return false;
        }
        String simple = cn.name.substring(cn.name.lastIndexOf('/') + 1);
        return !simple.equals("package-info") && !simple.equals("module-info");
    }

    /** 方法本身是否具备迁移资格。 */
    private static boolean eligible(MethodNode m) {
        if ((m.access & Opcodes.ACC_STATIC) == 0) {
            return false;
        }
        if ((m.access & (Opcodes.ACC_NATIVE | Opcodes.ACC_ABSTRACT
                | Opcodes.ACC_SYNCHRONIZED | Opcodes.ACC_BRIDGE
                | Opcodes.ACC_SYNTHETIC)) != 0) {
            return false;
        }
        if (m.name.equals("<clinit>") || m.name.equals("<init>")) {
            return false;
        }
        if (m.name.equals("main")
                && (m.desc.equals("([Ljava/lang/String;)V") || m.desc.equals("()V"))) {
            return false;
        }
        // 带注解的方法保留原位（框架反射按原类查询）
        if (m.visibleAnnotations != null || m.invisibleAnnotations != null
                || m.visibleTypeAnnotations != null
                || m.invisibleTypeAnnotations != null
                || m.visibleParameterAnnotations != null
                || m.invisibleParameterAnnotations != null
                || m.annotationDefault != null) {
            return false;
        }
        return true;
    }

    /**
     * 扫描方法体，确认迁移后从载体类访问全部类型/成员合法；
     * 同时收集需要提升为 public 的 jar 内成员。
     */
    private boolean bodyLegal(ClassNode owner, MethodNode m, List<MemberRef> widen) {
        // 描述符中的对象类型必须对载体（同包、非子类）可见
        for (Type t : Type.getArgumentTypes(m.desc)) {
            if (!typeLegal(owner, t, widen)) {
                return false;
            }
        }
        if (!typeLegal(owner, Type.getReturnType(m.desc), widen)) {
            return false;
        }
        if (m.tryCatchBlocks != null) {
            for (TryCatchBlockNode tcb : m.tryCatchBlocks) {
                if (tcb.type != null && !typeInternalLegal(owner, tcb.type)) {
                    return false;
                }
            }
        }
        for (AbstractInsnNode ins : m.instructions.toArray()) {
            if (ins instanceof InvokeDynamicInsnNode) {
                return false; // lambda/makeConcat：句柄与合成方法耦合，保守跳过
            }
            if (ins instanceof MethodInsnNode) {
                MethodInsnNode min = (MethodInsnNode) ins;
                if (!memberLegal(owner, min.owner, min.name, min.desc,
                        false, widen)) {
                    return false;
                }
            } else if (ins instanceof FieldInsnNode) {
                FieldInsnNode fin = (FieldInsnNode) ins;
                if (!memberLegal(owner, fin.owner, fin.name, fin.desc,
                        true, widen)) {
                    return false;
                }
            } else if (ins instanceof TypeInsnNode) {
                if (!typeInternalLegal(owner, ((TypeInsnNode) ins).desc)) {
                    return false;
                }
            } else if (ins instanceof MultiANewArrayInsnNode) {
                if (!typeInternalLegal(owner,
                        ((MultiANewArrayInsnNode) ins).desc)) {
                    return false;
                }
            } else if (ins instanceof LdcInsnNode) {
                Object cst = ((LdcInsnNode) ins).cst;
                if (cst instanceof Type) {
                    if (!typeLegal(owner, (Type) cst, widen)) {
                        return false;
                    }
                } else if (cst instanceof org.objectweb.asm.Handle) {
                    return false; // 极少见的方法句柄常量，保守跳过
                } else if (cst.getClass().getName()
                        .equals("java.lang.invoke.ConstantDynamic")) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * 类型对“同包、非子类”的载体是否可见：
     * jar 内类要求 public 或同包；外部类反射确认 public。
     */
    private boolean typeLegal(ClassNode owner, Type t, List<MemberRef> widen) {
        if (t == null) {
            return true;
        }
        if (t.getSort() == Type.ARRAY) {
            return typeLegal(owner, t.getElementType(), widen);
        }
        if (t.getSort() != Type.OBJECT) {
            return true;
        }
        return typeInternalLegal(owner, t.getInternalName());
    }

    private boolean typeInternalLegal(ClassNode owner, String internal) {
        if (internal == null || internal.indexOf('[') == 0) {
            return true;
        }
        ClassNode cn = nodes.get(internal);
        if (cn != null) {
            if ((cn.access & Opcodes.ACC_PUBLIC) != 0) {
                return true;
            }
            return packageOf(cn.name).equals(packageOf(owner.name));
        }
        Class<?> c = reflectClass(internal);
        return c != null && Modifier.isPublic(c.getModifiers());
    }

    /**
     * 成员对载体是否可访问。jar 内成员：不可访问则登记为待开放（public）；
     * 外部成员：必须本来就是 public（载体不是其子类，protected 不可用）。
     */
    private boolean memberLegal(ClassNode owner, String memberOwner, String name,
                                String desc, boolean field,
                                List<MemberRef> widen) {
        if (memberOwner == null) {
            return false;
        }
        if (memberOwner.startsWith("[")) {
            return true; // 数组 clone/length 等
        }
        if (nodes.containsKey(memberOwner)) {
            int access;
            if (field) {
                FieldNode f = findField(memberOwner, name);
                if (f == null) {
                    return false;
                }
                access = f.access;
            } else {
                MethodNode mn = findMethod(memberOwner, name, desc);
                if (mn == null) {
                    // 声明在 jar 类的外部父类：按外部规则反射判定
                    return externalMemberPublic(memberOwner, name, desc, field);
                }
                access = mn.access;
            }
            if ((access & Opcodes.ACC_PUBLIC) != 0) {
                return true;
            }
            boolean samePackage = packageOf(memberOwner).equals(packageOf(owner.name));
            if (samePackage && (access & Opcodes.ACC_PRIVATE) == 0) {
                // 包私有 / 同包 protected：载体与源类同包，天然可访问
                return true;
            }
            if (excluded.contains(memberOwner)) {
                // 排除类字节码原样拷贝，private/跨包 protected 无法开放，放弃迁移
                return false;
            }
            // 其余情况（private，或跨包 protected）：开放为 public
            MemberRef ref = new MemberRef(memberOwner, name, desc, field);
            if (!widen.contains(ref)) {
                widen.add(ref);
            }
            return true;
        }
        return externalMemberPublic(memberOwner, name, desc, field);
    }

    // ------------------------------------------------------------------
    // 迁移执行
    // ------------------------------------------------------------------

    private void moveMethod(Move move) {
        ClassNode from = move.from;
        ClassNode carrier = move.carrier;
        MethodNode m = move.method;

        // 桩必须沿用原方法名与访问标志（私有桩仍私有，调用方零感知）
        final String originalName = m.name;
        final int originalAccess = m.access;

        // 自递归调用改指载体，避免 桩->本体->桩 无限递归
        for (AbstractInsnNode ins : m.instructions.toArray()) {
            if (ins instanceof MethodInsnNode) {
                MethodInsnNode min = (MethodInsnNode) ins;
                if (min.owner.equals(from.name)
                        && min.name.equals(m.name) && min.desc.equals(m.desc)) {
                    min.owner = carrier.name;
                }
            }
        }

        // 载体中的方法名冲突（不同源类可能有同名同描述符静态方法）
        String newName = m.name;
        int serial = 0;
        while (hasMethod(carrier, newName, m.desc)) {
            newName = m.name + "$" + serial++;
        }
        m.name = newName;
        m.access = (m.access & ~(Opcodes.ACC_PRIVATE | Opcodes.ACC_PROTECTED))
                | Opcodes.ACC_PUBLIC;

        MethodNode stub = buildStub(originalName, originalAccess, m, carrier);
        from.methods.set(move.index, stub);
        carrier.methods.add(m);
    }

    /** 原方法位置的转发桩：入参原样加载 -> INVOKESTATIC 载体 -> 原样返回。 */
    private MethodNode buildStub(String name, int access, MethodNode moved,
                                 ClassNode carrier) {
        MethodNode stub = new MethodNode(ASM, access, name, moved.desc,
                moved.signature, moved.exceptions == null
                        ? null : moved.exceptions.toArray(new String[0]));
        Type[] args = Type.getArgumentTypes(moved.desc);
        int slot = 0;
        for (Type t : args) {
            stub.instructions.add(new VarInsnNode(t.getOpcode(Opcodes.ILOAD), slot));
            slot += t.getSize();
        }
        stub.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                carrier.name, moved.name, moved.desc, false));
        Type ret = Type.getReturnType(moved.desc);
        stub.instructions.add(new org.objectweb.asm.tree.InsnNode(
                ret.getOpcode(Opcodes.IRETURN)));
        stub.visitMaxs(0, 0);
        return stub;
    }

    // ------------------------------------------------------------------
    // 访问权开放
    // ------------------------------------------------------------------

    private void widenToPublic(MemberRef ref) {
        if (ref.isField) {
            FieldNode f = findField(ref.owner, ref.name);
            if (f != null) {
                f.access = (f.access & ~(Opcodes.ACC_PRIVATE | Opcodes.ACC_PROTECTED))
                        | Opcodes.ACC_PUBLIC;
            }
        } else {
            MethodNode mn = findMethod(ref.owner, ref.name, ref.desc);
            if (mn != null) {
                mn.access = (mn.access & ~(Opcodes.ACC_PRIVATE | Opcodes.ACC_PROTECTED))
                        | Opcodes.ACC_PUBLIC;
            }
        }
    }

    // ------------------------------------------------------------------
    // 查找（沿 jar 内继承链）
    // ------------------------------------------------------------------

    private MethodNode findMethod(String owner, String name, String desc) {
        String cur = owner;
        Set<String> seen = new TreeSet<String>();
        while (cur != null && seen.add(cur)) {
            ClassNode cn = nodes.get(cur);
            if (cn == null) {
                return null;
            }
            for (MethodNode mn : cn.methods) {
                if (mn.name.equals(name) && mn.desc.equals(desc)) {
                    return mn;
                }
            }
            cur = cn.superName;
        }
        return null;
    }

    private FieldNode findField(String owner, String name) {
        String cur = owner;
        Set<String> seen = new TreeSet<String>();
        while (cur != null && seen.add(cur)) {
            ClassNode cn = nodes.get(cur);
            if (cn == null) {
                return null;
            }
            for (FieldNode fn : cn.fields) {
                if (fn.name.equals(name)) {
                    return fn;
                }
            }
            cur = cn.superName;
        }
        return null;
    }

    private static boolean hasMethod(ClassNode cn, String name, String desc) {
        for (MethodNode mn : cn.methods) {
            if (mn.name.equals(name) && mn.desc.equals(desc)) {
                return true;
            }
        }
        return false;
    }

    // ------------------------------------------------------------------
    // 外部类型/成员反射（fail-closed：拿不准就不可迁移）
    // ------------------------------------------------------------------

    private Class<?> reflectClass(String internal) {
        if (classCache.containsKey(internal)) {
            return classCache.get(internal); // 允许缓存 null（解析失败）
        }
        String binary = internal.replace('/', '.');
        Class<?> c;
        try {
            c = Class.forName(binary, false, getClass().getClassLoader());
        } catch (Throwable t) {
            c = null;
        }
        classCache.put(internal, c);
        return c;
    }

    private boolean externalMemberPublic(String owner, String name, String desc,
                                         boolean field) {
        Class<?> c = reflectClass(owner);
        if (c == null || !Modifier.isPublic(c.getModifiers())) {
            return false;
        }
        try {
            Member found;
            if (field) {
                found = findReflectField(c, name);
            } else if (name.equals("<init>")) {
                Constructor<?>[] ctors = c.getDeclaredConstructors();
                found = null;
                for (Constructor<?> ct : ctors) {
                    if (desc.equals(Type.getConstructorDescriptor(ct))) {
                        found = ct;
                        break;
                    }
                }
            } else {
                found = findReflectMethod(c, name, desc);
            }
            if (found == null) {
                return false;
            }
            if (!Modifier.isPublic(found.getModifiers())) {
                return false;
            }
            Class<?> decl = found.getDeclaringClass();
            return Modifier.isPublic(decl.getModifiers());
        } catch (Throwable t) {
            return false;
        }
    }

    private Member findReflectField(Class<?> c, String name) {
        Class<?> cur = c;
        while (cur != null) {
            try {
                return cur.getDeclaredField(name);
            } catch (NoSuchFieldException e) {
                cur = cur.getSuperclass();
            }
        }
        return null;
    }

    private Member findReflectMethod(Class<?> c, String name, String desc) {
        Class<?> cur = c;
        while (cur != null) {
            for (java.lang.reflect.Method mth : cur.getDeclaredMethods()) {
                if (mth.getName().equals(name)
                        && Type.getMethodDescriptor(mth).equals(desc)) {
                    return mth;
                }
            }
            cur = cur.getSuperclass();
        }
        return null;
    }

    private static String packageOf(String internal) {
        int slash = internal.lastIndexOf('/');
        return slash > 0 ? internal.substring(0, slash) : "";
    }
}
