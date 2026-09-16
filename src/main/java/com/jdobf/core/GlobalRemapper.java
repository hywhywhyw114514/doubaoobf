package com.jdobf.core;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.commons.Remapper;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.MethodNode;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * 全局重命名映射。
 *
 * 第一遍：扫描所有 ClassNode，按继承体系给 类 / 方法组 / 字段 分配新名字；
 * 第二遍：ClassRemapper 依据本类改写所有引用（指令、描述符、注解、内部类表、
 * invokedynamic 句柄、nest 等全部由 ASM 统一处理）。
 */
public class GlobalRemapper extends Remapper {

    private final ObfConfig cfg;
    private final Hierarchy hierarchy;
    private final NameGenerator names;

    /** 旧内部名 -> 新内部名 */
    private final Map<String, String> classMap = new HashMap<String, String>();
    /** 旧包 -> 新包 */
    private final Map<String, String> packageMap = new HashMap<String, String>();
    /** 方法组键(rootOwner + "." + name + desc) -> 新名 */
    private final Map<String, String> methodNewName = new HashMap<String, String>();
    /** 字段键(owner + "." + name + desc) -> 新名 */
    private final Map<String, String> fieldNewName = new HashMap<String, String>();

    // 统计
    public int renamedClassCount;
    public int renamedMethodCount;
    public int renamedFieldCount;

    private final Set<String> assigned = new HashSet<String>();
    private final Set<String> inProgress = new HashSet<String>();
    /**
     * 被锁定的方法组：被排除类实现/重写了这些组时，整组不能改名，
     * 否则被排除类里保留原名的实现将与改名后的接口/父类断链。
     */
    private final Set<String> lockedMethodGroups = new HashSet<String>();

    /**
     * 必须使用 ASCII 简单名的类（内部名）：MANIFEST 入口类、
     * META-INF/services 的接口与实现类等——它们的名字会出现在纯文本资源里。
     * 仅在 BRAINDEAD 风格下有意义，普通类照常使用 caobi 组合符号名。
     */
    private final Set<String> asciiSafeClasses;

    public GlobalRemapper(ObfConfig cfg, Hierarchy hierarchy, NameGenerator names) {
        this(cfg, hierarchy, names, Collections.<String>emptySet());
    }

    public GlobalRemapper(ObfConfig cfg, Hierarchy hierarchy, NameGenerator names,
                          Set<String> asciiSafeClasses) {
        this.cfg = cfg;
        this.hierarchy = hierarchy;
        this.names = names;
        this.asciiSafeClasses = asciiSafeClasses != null
                ? asciiSafeClasses : Collections.<String>emptySet();
    }

    public Map<String, String> classMap() {
        return classMap;
    }

    /**
     * 导出人类可读的重命名映射表。
     * 方法键中的 owner 为方法组根类（旧内部名），字段键的 owner 为声明类（旧内部名）。
     */
    public void writeMapping(Appendable out) throws java.io.IOException {
        out.append("# Doubao Obfuscator mapping\n");
        out.append("# 格式: com/foo/Bar -> o/a\n\n");
        out.append("# ===== classes (旧内部名 -> 新内部名) =====\n");
        for (String key : new TreeSet<String>(classMap.keySet())) {
            out.append(key).append(" -> ").append(classMap.get(key)).append('\n');
        }
        out.append("\n# ===== methods (根类.方法名描述符 -> 新名) =====\n");
        for (String key : new TreeSet<String>(methodNewName.keySet())) {
            out.append(key).append(" -> ").append(methodNewName.get(key)).append('\n');
        }
        out.append("\n# ===== fields (声明类.字段名:类型) =====\n");
        for (String key : new TreeSet<String>(fieldNewName.keySet())) {
            out.append(key).append(" -> ").append(fieldNewName.get(key)).append('\n');
        }
    }

    /** 新内部名 -> 旧内部名 */
    public String reverseMap(String newInternalName) {
        for (Map.Entry<String, String> e : classMap.entrySet()) {
            if (e.getValue().equals(newInternalName)) {
                return e.getKey();
            }
        }
        return newInternalName;
    }

    /** 以点分隔的二进制类名映射（用于 manifest / services） */
    public String mapBinaryName(String binaryName) {
        String trimmed = binaryName.trim();
        String internal = trimmed.replace('.', '/');
        return map(internal).replace('/', '.');
    }

    // ------------------------------------------------------------------
    // 第一遍：建立映射
    // ------------------------------------------------------------------

    public void build(Collection<ClassNode> all) {
        buildClassMap(all);
        buildLockedGroups(all);
        // 确定性的处理顺序，便于排查与复现
        List<String> order = new ArrayList<String>(classNamesSorted(all));
        for (String c : order) {
            assignMembers(c);
        }
        renamedClassCount = classMap.size();
        renamedMethodCount = methodNewName.size();
        renamedFieldCount = fieldNewName.size();
    }

    private Set<String> classNamesSorted(Collection<ClassNode> all) {
        Set<String> s = new TreeSet<String>();
        for (ClassNode n : all) {
            s.add(n.name);
        }
        return s;
    }

    private boolean renameableClass(ClassNode n) {
        if (hierarchy.isExcluded(n.name)) {
            return false;
        }
        int slash = n.name.lastIndexOf('/');
        String simple = slash >= 0 ? n.name.substring(slash + 1) : n.name;
        if (simple.equals("package-info") || simple.equals("module-info")) {
            return false;
        }
        return true;
    }

    private void buildClassMap(Collection<ClassNode> all) {
        // 每个新包内已占用的简单名
        Map<String, Set<String>> usedByPackage = new HashMap<String, Set<String>>();
        // BRAINDEAD 风格下所有新包共享根级命名空间，叶子名必须全局唯一
        Set<String> usedPackageLeaves = new HashSet<String>();
        TreeSet<String> sorted = new TreeSet<String>();
        for (ClassNode n : all) {
            sorted.add(n.name);
        }
        for (String name : sorted) {
            ClassNode n = hierarchy.node(name);
            if (n == null || !renameableClass(n)) {
                continue;
            }
            int slash = name.lastIndexOf('/');
            String pkg = slash >= 0 ? name.substring(0, slash) : "";
            String simple = slash >= 0 ? name.substring(slash + 1) : name;

            String newPkg = pkg;
            if (cfg.renamePackages && !pkg.isEmpty()) {
                String mapped = packageMap.get(pkg);
                if (mapped == null) {
                    if (names.style() == NameGenerator.Style.BRAINDEAD) {
                        // 示例风格：根级两位小写字母包（sb 风格）
                        String leaf;
                        do {
                            leaf = names.nextPackageLeaf();
                        } while (!usedPackageLeaves.add(leaf));
                        mapped = leaf;
                    } else {
                        mapped = "o/" + names.next();
                    }
                    packageMap.put(pkg, mapped);
                }
                newPkg = mapped;
            }
            String newSimple = simple;
            if (cfg.renameClasses) {
                Set<String> used = usedByPackage.get(newPkg);
                if (used == null) {
                    used = new HashSet<String>();
                    usedByPackage.put(newPkg, used);
                }
                // 先放入该包内所有“保留原名”的类，避免冲突
                if (used.isEmpty()) {
                    seedUsedNames(all, newPkg, pkg, used);
                }
                newSimple = uniqueClassName(used, asciiSafeClasses.contains(name));
            }
            String newFull = newPkg.isEmpty() ? newSimple : newPkg + "/" + newSimple;
            if (!newFull.equals(name)) {
                classMap.put(name, newFull);
            }
        }
    }

    /**
     * 在指定已用名集合内取一个唯一的新类简单名。
     * BRAINDEAD 风格下 ASCII 敏感类（入口/服务类）使用 I/l/1 纯 ASCII 名，
     * 其余类使用 caobi 组合符号名。
     */
    private String uniqueClassName(Set<String> used, boolean asciiSafe) {
        String candidate;
        for (int tries = 0; tries < 64; tries++) {
            if (names.style() == NameGenerator.Style.BRAINDEAD) {
                candidate = asciiSafe ? names.nextAsciiClassName() : names.nextClassName();
            } else {
                candidate = names.next();
            }
            if (used.add(candidate)) {
                return candidate;
            }
        }
        // 理论上不会到达：随机空间极大；计数器名兜底保证唯一且不卡死
        do {
            candidate = names.fallbackName();
        } while (!used.add(candidate));
        return candidate;
    }

    /**
     * 新包中已经存在的名字：
     *  - 包不重命名时：同包保留原名的类
     *  - 包重命名时：所有源包都会映射到唯一新包，因此只需自身包内保留类
     */
    private void seedUsedNames(Collection<ClassNode> all, String newPkg, String oldPkg, Set<String> used) {
        for (ClassNode other : all) {
            int slash = other.name.lastIndexOf('/');
            String otherPkg = slash >= 0 ? other.name.substring(0, slash) : "";
            String otherSimple = slash >= 0 ? other.name.substring(slash + 1) : other.name;
            boolean sameTarget;
            if (cfg.renamePackages) {
                sameTarget = otherPkg.equals(oldPkg);
            } else {
                sameTarget = otherPkg.equals(newPkg);
            }
            if (sameTarget && (!cfg.renameClasses || !renameableClass(other))) {
                used.add(otherSimple);
            }
        }
    }

    /**
     * 扫描被排除类声明的虚方法，凡是其根在可改名 jar 类中的方法组，整组锁定。
     */
    private void buildLockedGroups(Collection<ClassNode> all) {
        for (ClassNode cn : all) {
            if (!hierarchy.isExcluded(cn.name)) {
                continue;
            }
            for (MethodNode m : cn.methods) {
                if (m.name.equals("<init>") || m.name.equals("<clinit>")) {
                    continue;
                }
                if ((m.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) != 0) {
                    continue;
                }
                String root = hierarchy.resolveMethodRoot(cn.name, m.name, m.desc);
                if (root != null && !hierarchy.isExcluded(root)) {
                    lockedMethodGroups.add(methodKey(root, m.name, m.desc));
                }
            }
        }
    }

    // ----------------------------- 成员分配 -----------------------------

    private void assignMembers(String className) {
        if (assigned.contains(className) || inProgress.contains(className)) {
            return;
        }
        ClassNode n = hierarchy.node(className);
        if (n == null || hierarchy.isExcluded(className)) {
            assigned.add(className);
            return;
        }
        inProgress.add(className);
        if (n.superName != null) {
            assignMembers(n.superName);
        }
        if (n.interfaces != null) {
            for (String i : n.interfaces) {
                assignMembers(i);
            }
        }

        if (cfg.renameMethods) {
            assignMethods(className, n);
        }
        if (cfg.renameFields) {
            assignFields(className, n);
        }

        inProgress.remove(className);
        assigned.add(className);
    }

    private boolean isSpecialClass(ClassNode n, int flag) {
        return (n.access & flag) != 0;
    }

    private boolean canRenameMethod(ClassNode owner, MethodNode m, String root) {
        if (root == null) {
            return false; // 继承/实现自外部或被排除类
        }
        if (m.name.equals("<init>") || m.name.equals("<clinit>")) {
            return false;
        }
        if ((m.access & Opcodes.ACC_NATIVE) != 0) {
            return false; // JNI 入口
        }
        if ((m.access & Opcodes.ACC_ABSTRACT) != 0 && root == null) {
            return false;
        }
        // 程序入口不可改名：
        //  - 经典入口 static void main(String[])
        //  - Java 25 JEP 512 实例 main：void main()、void main(String[])
        //    以及 static void main()，启动器按名字 "main" 查找
        if (m.name.equals("main")
                && (m.desc.equals("([Ljava/lang/String;)V") || m.desc.equals("()V"))) {
            return false;
        }
        if (isSpecialClass(owner, Opcodes.ACC_ANNOTATION)
                || isSpecialClass(owner, Opcodes.ACC_RECORD)) {
            return false; // 注解属性名 / record 组件方法依赖反射
        }
        if (isSpecialClass(owner, Opcodes.ACC_ENUM)) {
            String enumDesc = Type.getObjectType(owner.name).getDescriptor();
            if (m.name.equals("values") && m.desc.equals("()[" + enumDesc)) {
                return false;
            }
            if (m.name.equals("valueOf") && m.desc.equals("(Ljava/lang/String;)" + enumDesc)) {
                return false;
            }
        }
        return true;
    }

    private boolean canRenameField(ClassNode owner, FieldNode f) {
        if (f.name.equals("serialVersionUID")) {
            return false;
        }
        if ((f.access & Opcodes.ACC_ENUM) != 0) {
            return false;
        }
        if (isSpecialClass(owner, Opcodes.ACC_ENUM)
                || isSpecialClass(owner, Opcodes.ACC_ANNOTATION)
                || isSpecialClass(owner, Opcodes.ACC_RECORD)) {
            return false;
        }
        if (cfg.keepSerializableFields
                && (f.access & Opcodes.ACC_STATIC) == 0
                && (f.access & Opcodes.ACC_TRANSIENT) == 0
                && hierarchy.isSerializable(owner.name)) {
            return false;
        }
        return true;
    }

    private String methodKey(String root, String name, String desc) {
        return root + "." + name + desc;
    }

    private String fieldKey(String owner, String name, String desc) {
        return owner + "." + name + desc;
    }

    /** 查询某个已声明方法的最终名字（映射表中没有则原名） */
    private String finalMethodName(String owner, MethodNode m) {
        String root = hierarchy.resolveMethodRoot(owner, m.name, m.desc);
        if (root == null) {
            return m.name;
        }
        String nn = methodNewName.get(methodKey(root, m.name, m.desc));
        return nn != null ? nn : m.name;
    }

    private String finalFieldName(String owner, FieldNode f) {
        String realOwner = hierarchy.resolveFieldOwner(owner, f.name, f.desc);
        if (realOwner == null) {
            return f.name;
        }
        String nn = fieldNewName.get(fieldKey(realOwner, f.name, f.desc));
        return nn != null ? nn : f.name;
    }

    private Set<String> collectInheritedMethodPairs(ClassNode n) {
        Set<String> used = new HashSet<String>();
        Set<String> supers = hierarchy.allSupertypes(n.name);
        for (String s : supers) {
            if (s.equals(n.name)) {
                continue;
            }
            ClassNode sn = hierarchy.node(s);
            boolean boundary = sn == null || hierarchy.isExcluded(s);
            if (!boundary) {
                for (MethodNode m : sn.methods) {
                    if ((m.access & Opcodes.ACC_PRIVATE) != 0) {
                        continue;
                    }
                    used.add(finalMethodName(s, m) + " " + mapMethodDesc(m.desc));
                }
            } else if (sn != null) {
                for (MethodNode m : sn.methods) {
                    if ((m.access & Opcodes.ACC_PRIVATE) != 0) {
                        continue;
                    }
                    used.add(m.name + " " + mapMethodDesc(m.desc));
                }
            } else {
                Class<?> c = hierarchy.reflect(s);
                if (c != null) {
                    for (java.lang.reflect.Method m : c.getDeclaredMethods()) {
                        if (Modifier.isPrivate(m.getModifiers())) {
                            continue;
                        }
                        used.add(m.getName() + " " + mapMethodDesc(Type.getMethodDescriptor(m)));
                    }
                }
            }
        }
        return used;
    }

    private Set<String> collectInheritedFieldPairs(ClassNode n) {
        Set<String> used = new HashSet<String>();
        Set<String> supers = hierarchy.allSupertypes(n.name);
        for (String s : supers) {
            if (s.equals(n.name)) {
                continue;
            }
            ClassNode sn = hierarchy.node(s);
            boolean boundary = sn == null || hierarchy.isExcluded(s);
            if (!boundary) {
                for (FieldNode f : sn.fields) {
                    used.add(finalFieldName(s, f) + " " + mapType(f.desc));
                }
            } else if (sn != null) {
                for (FieldNode f : sn.fields) {
                    used.add(f.name + " " + mapType(f.desc));
                }
            } else {
                Class<?> c = hierarchy.reflect(s);
                if (c != null) {
                    for (java.lang.reflect.Field f : c.getDeclaredFields()) {
                        used.add(f.getName() + " " + mapType(Type.getDescriptor(f.getType())));
                    }
                }
            }
        }
        return used;
    }

    private void assignMethods(String className, ClassNode n) {
        Set<String> used = collectInheritedMethodPairs(n);
        // 自身已有方法的最终名占位
        List<String> pendingKeys = new ArrayList<String>();
        for (MethodNode m : n.methods) {
            String root = hierarchy.resolveMethodRoot(className, m.name, m.desc);
            String finalName;
            if (root != null && canRenameMethod(n, m, root)
                    && !lockedMethodGroups.contains(methodKey(root, m.name, m.desc))) {
                String key = methodKey(root, m.name, m.desc);
                String already = methodNewName.get(key);
                if (already != null) {
                    finalName = already;
                } else {
                    pendingKeys.add(key);
                    finalName = m.name; // 先占位，随后统一分配
                }
            } else {
                finalName = m.name;
            }
            used.add(finalName + " " + mapMethodDesc(m.desc));
        }
        for (String key : pendingKeys) {
            String desc = key.substring(key.indexOf('('));
            methodNewName.put(key, uniqueMemberName(used, desc));
        }
    }

    private void assignFields(String className, ClassNode n) {
        Set<String> used = collectInheritedFieldPairs(n);
        List<FieldNode> pending = new ArrayList<FieldNode>();
        for (FieldNode f : n.fields) {
            if (canRenameField(n, f)
                    && !fieldNewName.containsKey(fieldKey(className, f.name, f.desc))) {
                pending.add(f);
            }
            // 原名占位，避免新名字与保留成员冲突
            used.add(f.name + " " + mapType(f.desc));
        }
        for (FieldNode f : pending) {
            String mappedDesc = mapType(f.desc);
            fieldNewName.put(fieldKey(className, f.name, f.desc),
                    uniqueMemberName(used, mappedDesc));
        }
    }

    /** 在“名字+空格+描述符”的已用集合内分配唯一成员名，撞名重试，计数器兜底。 */
    private String uniqueMemberName(Set<String> used, String desc) {
        String candidate;
        for (int tries = 0; tries < 64; tries++) {
            candidate = names.next();
            if (used.add(candidate + " " + desc)) {
                return candidate;
            }
        }
        do {
            candidate = names.fallbackName();
        } while (!used.add(candidate + " " + desc));
        return candidate;
    }

    // ------------------------------------------------------------------
    // 第二遍：Remapper 查询
    // ------------------------------------------------------------------

    @Override
    public String map(String internalName) {
        if (internalName == null) {
            return null;
        }
        String m = classMap.get(internalName);
        return m != null ? m : internalName;
    }

    @Override
    public String mapMethodName(String owner, String name, String descriptor) {
        if (owner == null || name.equals("<init>") || name.equals("<clinit>")) {
            return name;
        }
        if (hierarchy.isExcluded(owner)) {
            return name;
        }
        String root = hierarchy.resolveMethodRoot(owner, name, descriptor);
        if (root == null) {
            return name;
        }
        String nn = methodNewName.get(methodKey(root, name, descriptor));
        return nn != null ? nn : name;
    }

    @Override
    public String mapFieldName(String owner, String name, String descriptor) {
        if (owner == null) {
            return name;
        }
        if (hierarchy.isExcluded(owner)) {
            return name;
        }
        String realOwner = hierarchy.resolveFieldOwner(owner, name, descriptor);
        if (realOwner == null) {
            return name;
        }
        String nn = fieldNewName.get(fieldKey(realOwner, name, descriptor));
        return nn != null ? nn : name;
    }
}
