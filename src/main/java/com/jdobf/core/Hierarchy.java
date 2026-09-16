package com.jdobf.core;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.MethodNode;

import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * 类层次信息中心。
 *
 * 对于 jar 内部的类使用 ASM ClassNode 解析；
 * 对于外部依赖（JDK / 第三方库）回退到反射，
 * 这样 COMPUTE_FRAMES 与重命名分组都能拿到完整的继承关系。
 */
public class Hierarchy {

    public static final int ASM = Opcodes.ASM9;
    /** 解析到 jar 外部（或被排除的类，视为不可改名的边界） */
    public static final String EXTERNAL = null;

    private final Map<String, ClassNode> nodes;
    private final Set<String> excluded;
    private final ClassLoader loader;

    private final Map<String, Class<?>> reflectCache = new HashMap<String, Class<?>>();
    /** “反射找不到该类”的专用哨兵（绝不能用 Object.class，否则会污染缓存） */
    private static final class MissingMarker {
    }
    private static final Class<?> MISSING = MissingMarker.class;

    public Hierarchy(Map<String, ClassNode> nodes, Set<String> excluded) {
        this.nodes = nodes;
        this.excluded = excluded;
        this.loader = Hierarchy.class.getClassLoader();
    }

    public ClassNode node(String internalName) {
        return nodes.get(internalName);
    }

    public boolean isExcluded(String internalName) {
        return excluded.contains(internalName);
    }

    // ------------------------------------------------------------------
    // 反射回退
    // ------------------------------------------------------------------

    /** 反射加载外部类，失败返回 null（含数组/基本类型数组） */
    public Class<?> reflect(String internalName) {
        if (internalName == null) {
            return null;
        }
        Class<?> cached = reflectCache.get(internalName);
        if (cached == MISSING) {
            return null;
        }
        if (cached != null) {
            return cached;
        }
        Class<?> c;
        try {
            String binary = internalName.replace('/', '.');
            c = Class.forName(binary, false, loader);
        } catch (Throwable t) {
            c = null;
        }
        reflectCache.put(internalName, c == null ? MISSING : c);
        return c;
    }

    /** 父类内部名，java/lang/Object 与无父类的接口返回 null */
    public String superName(String internalName) {
        ClassNode n = nodes.get(internalName);
        if (n != null) {
            return n.superName;
        }
        Class<?> c = reflect(internalName);
        if (c == null) {
            return "java/lang/Object".equals(internalName) ? null : "java/lang/Object";
        }
        Class<?> s = c.getSuperclass();
        return s == null ? null : Type.getInternalName(s);
    }

    public boolean isInterface(String internalName) {
        ClassNode n = nodes.get(internalName);
        if (n != null) {
            return (n.access & Opcodes.ACC_INTERFACE) != 0;
        }
        Class<?> c = reflect(internalName);
        return c != null && c.isInterface();
    }

    public List<String> interfacesOf(String internalName) {
        List<String> result = new ArrayList<String>();
        ClassNode n = nodes.get(internalName);
        if (n != null) {
            if (n.interfaces != null) {
                result.addAll(n.interfaces);
            }
            return result;
        }
        Class<?> c = reflect(internalName);
        if (c != null) {
            for (Class<?> i : c.getInterfaces()) {
                result.add(Type.getInternalName(i));
            }
        }
        return result;
    }

    /** BFS 收集全部父类型（含自身），jar 节点或反射 */
    public Set<String> allSupertypes(String internalName) {
        Set<String> visited = new HashSet<String>();
        Deque<String> queue = new ArrayDeque<String>();
        queue.add(internalName);
        while (!queue.isEmpty()) {
            String c = queue.poll();
            if (c == null || !visited.add(c)) {
                continue;
            }
            String s = superName(c);
            if (s != null) {
                queue.add(s);
            }
            queue.addAll(interfacesOf(c));
        }
        return visited;
    }

    public boolean isAssignableFrom(String to, String from) {
        if (to.equals(from)) {
            return true;
        }
        if ("java/lang/Object".equals(to) && !from.startsWith("[")) {
            return true;
        }
        // 数组类型用反射判定
        if (to.startsWith("[") || from.startsWith("[")) {
            if (to.equals(from)) {
                return true;
            }
            Class<?> ct = reflect(to);
            Class<?> cf = reflect(from);
            if (ct != null && cf != null) {
                return ct.isAssignableFrom(cf);
            }
            return "java/lang/Object".equals(to)
                    || "java/lang/Cloneable".equals(to)
                    || "java/io/Serializable".equals(to);
        }
        return allSupertypes(from).contains(to);
    }

    // ------------------------------------------------------------------
    // 成员声明解析（重命名分组用）
    // ------------------------------------------------------------------

    private boolean nodeDeclaresMethod(ClassNode n, String name, String desc, boolean includePrivate) {
        for (MethodNode m : n.methods) {
            if (m.name.equals(name) && m.desc.equals(desc)) {
                if (!includePrivate && (m.access & Opcodes.ACC_PRIVATE) != 0) {
                    continue;
                }
                return true;
            }
        }
        return false;
    }

    private boolean reflectDeclaresMethod(String owner, String name, String desc) {
        Class<?> c = reflect(owner);
        if (c == null) {
            // 无法解析的外部类：保守起见视为“可能声明”，不改名更安全
            return true;
        }
        for (java.lang.reflect.Method m : c.getDeclaredMethods()) {
            if (Modifier.isPrivate(m.getModifiers())) {
                continue;
            }
            if (m.getName().equals(name) && Type.getMethodDescriptor(m).equals(desc)) {
                return true;
            }
        }
        // 构造器不属于继承/重写体系，不需要走到这里
        return false;
    }

    private boolean boundaryDeclaresMethod(String owner, String name, String desc, boolean includePrivate) {
        ClassNode n = nodes.get(owner);
        if (n != null) {
            // 被排除的 jar 类：按结构检查
            return nodeDeclaresMethod(n, name, desc, includePrivate);
        }
        return reflectDeclaresMethod(owner, name, desc);
    }

    private boolean nodeDeclaresField(ClassNode n, String name, String desc) {
        for (FieldNode f : n.fields) {
            if (f.name.equals(name) && f.desc.equals(desc)) {
                return true;
            }
        }
        return false;
    }

    private boolean reflectDeclaresField(String owner, String name, String desc) {
        Class<?> c = reflect(owner);
        if (c == null) {
            return true; // 无法解析时保持保守
        }
        for (java.lang.reflect.Field f : c.getDeclaredFields()) {
            if (f.getName().equals(name) && Type.getDescriptor(f.getType()).equals(desc)) {
                return true;
            }
        }
        return false;
    }

    /**
     * 解析方法的“根声明”。
     *
     * 关键：虚方法必须先沿父类/接口链查找——本类声明的方法很可能是在
     * 重写外部接口（如 Runnable.run），若本地命中就直接返回会导致
     * 实现类方法被改名而接口方法保留，运行时 AbstractMethodError。
     *
     * 返回可改名的 jar 内部 owner；若继承/实现自外部或被排除的类则返回 {@link #EXTERNAL}。
     */
    public String resolveMethodRoot(String owner, String name, String desc) {
        ClassNode self = nodes.get(owner);
        if (self != null && !excluded.contains(owner)) {
            // private / static 不参与虚分派，本地声明即根
            for (MethodNode m : self.methods) {
                if (m.name.equals(name) && m.desc.equals(desc)
                        && ((m.access & (Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC)) != 0)) {
                    return owner;
                }
            }
        }

        String jarCandidate = null;
        Set<String> visited = new HashSet<String>();
        Deque<String> queue = new ArrayDeque<String>();
        if (self != null) {
            if (self.superName != null) {
                queue.add(self.superName);
            }
            queue.addAll(interfacesOf(owner));
        }
        while (!queue.isEmpty()) {
            String c = queue.poll();
            if (c == null || !visited.add(c)) {
                continue;
            }
            ClassNode n = nodes.get(c);
            boolean boundary = n == null || excluded.contains(c);
            if (!boundary) {
                if (nodeDeclaresMethod(n, name, desc, false)) {
                    // 递归确认该 jar 祖先自己是否也在重写外部方法
                    String deeper = resolveMethodRoot(c, name, desc);
                    if (deeper == EXTERNAL) {
                        return EXTERNAL;
                    }
                    if (jarCandidate == null) {
                        jarCandidate = deeper;
                    }
                }
            } else {
                if (boundaryDeclaresMethod(c, name, desc, false)) {
                    return EXTERNAL;
                }
            }
            String s = superName(c);
            if (s != null) {
                queue.add(s);
            }
            queue.addAll(interfacesOf(c));
        }
        return jarCandidate != null ? jarCandidate : owner;
    }

    /**
     * 解析字段的声明 owner。
     * 字段虽然不参与重写，但子类访问继承字段时字节码 owner 可能写的是子类，
     * 因此需要沿继承链找到真正的声明类。
     */
    public String resolveFieldOwner(String owner, String name, String desc) {
        Set<String> visited = new HashSet<String>();
        Deque<String> queue = new ArrayDeque<String>();
        queue.add(owner);
        while (!queue.isEmpty()) {
            String c = queue.poll();
            if (c == null || !visited.add(c)) {
                continue;
            }
            ClassNode n = nodes.get(c);
            boolean boundary = n == null || excluded.contains(c);
            if (!boundary) {
                if (nodeDeclaresField(n, name, desc)) {
                    return c;
                }
            } else {
                boolean declared = n != null
                        ? nodeDeclaresField(n, name, desc)
                        : reflectDeclaresField(c, name, desc);
                if (declared) {
                    return EXTERNAL;
                }
            }
            String s = superName(c);
            if (s != null) {
                queue.add(s);
            }
            queue.addAll(interfacesOf(c));
        }
        return owner;
    }

    /** 是否直接或间接实现了 Serializable / Externalizable */
    public boolean isSerializable(String owner) {
        Set<String> visited = new HashSet<String>();
        Deque<String> queue = new ArrayDeque<String>();
        queue.add(owner);
        while (!queue.isEmpty()) {
            String c = queue.poll();
            if (c == null || !visited.add(c)) {
                continue;
            }
            if ("java/io/Serializable".equals(c) || "java/io/Externalizable".equals(c)) {
                return true;
            }
            ClassNode n = nodes.get(c);
            if (n == null && !excluded.contains(c)) {
                Class<?> cls = reflect(c);
                if (cls != null) {
                    if (java.io.Serializable.class.isAssignableFrom(cls)) {
                        return true;
                    }
                    continue;
                }
            }
            String s = superName(c);
            if (s != null) {
                queue.add(s);
            }
            queue.addAll(interfacesOf(c));
        }
        return false;
    }

    // ------------------------------------------------------------------
    // COMPUTE_FRAMES 支持
    // ------------------------------------------------------------------

    /**
     * 两个引用类型的公共父类，供 ClassWriter.getCommonSuperClass 使用。
     */
    public String getCommonSuperClass(String type1, String type2) {
        if (type1.equals(type2)) {
            return type1;
        }
        // 数组类型
        if (type1.startsWith("[") || type2.startsWith("[")) {
            if (type1.equals(type2)) {
                return type1;
            }
            // 两边都是引用类型数组：取元素公共父类再包成数组
            if (type1.startsWith("[L") && type2.startsWith("[L")) {
                String e1 = type1.substring(1);
                String e2 = type2.substring(1);
                return "[" + getCommonSuperClass(e1, e2);
            }
            Class<?> c1 = reflect(type1);
            Class<?> c2 = reflect(type2);
            if (c1 != null && c2 != null) {
                if (c1.isAssignableFrom(c2)) {
                    return type1;
                }
                if (c2.isAssignableFrom(c1)) {
                    return type2;
                }
            }
            return "java/lang/Object";
        }
        if (isAssignableFrom(type1, type2)) {
            return type1;
        }
        if (isAssignableFrom(type2, type1)) {
            return type2;
        }
        // 沿 type1 继承链找第一个也是 type2 父类型的类
        String c = type1;
        while (c != null) {
            if (!isInterface(c) && isAssignableFrom(c, type2)) {
                return c;
            }
            c = superName(c);
        }
        return "java/lang/Object";
    }
}
