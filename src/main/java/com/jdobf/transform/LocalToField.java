package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SimpleVerifier;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

/**
 * 局部变量字段化（"局部变量改全局"）：
 *
 * 把非递归实例方法（含全部构造器）的非参数局部变量槽，每构建随机挑选一批
 * 提升为类的 private synthetic 实例字段。方法内对该槽的 load/store 全部
 * 改写为 GETFIELD/PUTFIELD，反编译后干净的局部变量表消失，方法状态散落到
 * 大量随机命名字段中。
 *
 * 安全性：
 *  - 只处理实例方法：每对象一份字段，天然规避静态方法的多线程串扰；
 *  - 通过类内调用图 Tarjan SCC 排除一切"执行期可重入自身"的方法（递归链/
 *    互调环），避免嵌套调用踩坏字段；构造器豁免（对象构造期不共享，
 *    this() 链中各构造器使用各自唯一字段）；
 *  - 槽类型用 SimpleVerifier 数据流分析，所有帧上类型必须唯一且已初始化，
 *    避免合并类型导致使用点校验失败；
 *  - 构造器只改写 super/this 调用之后的访问；
 *  - 含显式 synchronized 块（monitor 指令）的方法跳过；
 *  - 选择概率与每槽决定均随机，每构建结果不同。
 */
public final class LocalToField {

    private static final int MAX_FIELDS_PER_CLASS = 48;

    /** 合成 MethodNode（未写 visitMaxs）做帧分析时的保守栈深，避免放大到 65535。 */
    private static final int SYNTH_STACK_BOUND = 512;

    private LocalToField() {
    }

    /**
     * 用给定边界跑 SimpleVerifier 帧分析。边界不足（合成方法的极端构造）时
     * 自动回退 65535 重试；仍失败返回 null。分析期间临时改写 mn.maxStack/
     * maxLocals，分析后不恢复：真实类边界即原值，合成类写出时由
     * COMPUTE_FRAMES 重算，后续各 pass 也都会自行放大边界后再分析。
     */
    private static Frame<BasicValue>[] analyzeFrames(ClassNode cn, MethodNode mn,
            SimpleVerifier verifier, int localsBound, int stackBound) {
        mn.maxStack = stackBound;
        mn.maxLocals = localsBound;
        try {
            return new Analyzer<BasicValue>(verifier).analyze(cn.name, mn);
        } catch (Throwable first) {
            if (stackBound == 65535 && localsBound == 65535) {
                return null;
            }
            try {
                mn.maxStack = 65535;
                mn.maxLocals = 65535;
                return new Analyzer<BasicValue>(verifier).analyze(cn.name, mn);
            } catch (Throwable second) {
                return null;
            }
        }
    }

    public static int apply(ClassNode cn, Random random, ClassLoader typeLoader) {
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE)) != 0) {
            return 0;
        }
        Set<String> used = new HashSet<String>();
        for (MethodNode m : cn.methods) {
            used.add(m.name + m.desc);
        }
        for (FieldNode f : cn.fields) {
            used.add(f.name);
        }
        Set<String> reentrant = findReentrantMethods(cn);

        int budget = MAX_FIELDS_PER_CLASS;
        int promoted = 0;
        for (MethodNode mn : cn.methods) {
            if (budget <= 0) {
                break;
            }
            if (!eligible(mn, reentrant)) {
                continue;
            }
            int n = promoteMethod(cn, mn, random, typeLoader, used, budget);
            promoted += n;
            budget -= n;
        }
        return promoted;
    }

    private static boolean eligible(MethodNode mn, Set<String> reentrant) {
        if (mn.instructions == null || mn.instructions.size() == 0) {
            return false;
        }
        if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE | Opcodes.ACC_STATIC)) != 0) {
            return false;
        }
        if (!mn.name.equals("<init>") && reentrant.contains(mn.name + mn.desc)) {
            return false;
        }
        for (AbstractInsnNode n : mn.instructions.toArray()) {
            int op = n.getOpcode();
            if (op == Opcodes.MONITORENTER || op == Opcodes.MONITOREXIT) {
                return false;
            }
        }
        return true;
    }

    // ------------------------------------------------------------------
    // 类内实例方法调用图：求所有处于环上的方法（执行期可重入自身）
    // ------------------------------------------------------------------

    private static Set<String> findReentrantMethods(ClassNode cn) {
        Set<String> nodes = new HashSet<String>();
        for (MethodNode mn : cn.methods) {
            if ((mn.access & (Opcodes.ACC_STATIC | Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) == 0
                    && !mn.name.equals("<init>") && !mn.name.equals("<clinit>")) {
                nodes.add(mn.name + mn.desc);
            }
        }
        Map<String, List<String>> adj = new HashMap<String, List<String>>();
        for (MethodNode mn : cn.methods) {
            if (mn.name.equals("<init>") || (mn.access & Opcodes.ACC_STATIC) != 0) {
                continue;
            }
            String from = mn.name + mn.desc;
            List<String> outs = new ArrayList<String>();
            for (AbstractInsnNode n : mn.instructions.toArray()) {
                if (n instanceof MethodInsnNode) {
                    MethodInsnNode min = (MethodInsnNode) n;
                    int op = n.getOpcode();
                    if ((op == Opcodes.INVOKEVIRTUAL || op == Opcodes.INVOKESPECIAL
                            || op == Opcodes.INVOKEINTERFACE)
                            && min.owner.equals(cn.name)) {
                        String to = min.name + min.desc;
                        if (nodes.contains(to)) {
                            outs.add(to);
                        }
                    }
                }
            }
            adj.put(from, outs);
        }
        // Tarjan SCC
        Tarjan t = new Tarjan(adj);
        Set<String> onCycle = new HashSet<String>();
        for (List<String> comp : t.run()) {
            if (comp.size() > 1) {
                onCycle.addAll(comp);
            } else {
                String only = comp.get(0);
                if (adj.containsKey(only) && adj.get(only).contains(only)) {
                    onCycle.add(only);
                }
            }
        }
        return onCycle;
    }

    private static final class Tarjan {
        final Map<String, List<String>> adj;
        final Map<String, Integer> idx = new HashMap<String, Integer>();
        final Map<String, Integer> low = new HashMap<String, Integer>();
        final Deque<String> stack = new ArrayDeque<String>();
        final Set<String> onStack = new HashSet<String>();
        final List<List<String>> comps = new ArrayList<List<String>>();
        int counter;

        Tarjan(Map<String, List<String>> adj) {
            this.adj = adj;
        }

        List<List<String>> run() {
            for (String v : adj.keySet()) {
                if (!idx.containsKey(v)) {
                    strong(v);
                }
            }
            return comps;
        }

        private void strong(String v) {
            idx.put(v, Integer.valueOf(counter));
            low.put(v, Integer.valueOf(counter));
            counter++;
            stack.push(v);
            onStack.add(v);
            List<String> outs = adj.get(v);
            if (outs != null) {
                for (String w : outs) {
                    if (!adj.containsKey(w)) {
                        continue;
                    }
                    if (!idx.containsKey(w)) {
                        strong(w);
                        low.put(v, Math.min(low.get(v).intValue(), low.get(w).intValue()));
                    } else if (onStack.contains(w)) {
                        low.put(v, Math.min(low.get(v).intValue(), idx.get(w).intValue()));
                    }
                }
            }
            if (low.get(v).intValue() == idx.get(v).intValue()) {
                List<String> comp = new ArrayList<String>();
                String w;
                do {
                    w = stack.pop();
                    onStack.remove(w);
                    comp.add(w);
                } while (!w.equals(v));
                comps.add(comp);
            }
        }
    }

    // ------------------------------------------------------------------
    // 单方法提升
    // ------------------------------------------------------------------

    private static int promoteMethod(ClassNode cn, MethodNode mn, Random random,
                                      ClassLoader typeLoader, Set<String> used, int budget) {
        boolean isInit = mn.name.equals("<init>");
        int barrierIndex = -1;
        AbstractInsnNode[] insns = mn.instructions.toArray();
        if (isInit) {
            for (int i = 0; i < insns.length; i++) {
                AbstractInsnNode n = insns[i];
                if (n.getOpcode() == Opcodes.INVOKESPECIAL && n instanceof MethodInsnNode
                        && ((MethodInsnNode) n).name.equals("<init>")
                        && (isInit && ((MethodInsnNode) n).owner.equals(cn.name)
                            || ((MethodInsnNode) n).owner.equals(cn.superName))) {
                    barrierIndex = i;
                    break;
                }
            }
            if (barrierIndex < 0) {
                return 0;
            }
        }

        List<Type> argTypes = new ArrayList<Type>(Arrays.asList(Type.getArgumentTypes(mn.desc)));
        int firstLocal = 1;
        for (Type t : argTypes) {
            firstLocal += t.getSize();
        }

        SimpleVerifier verifier = new SimpleVerifier(
                Opcodes.ASM9,
                Type.getObjectType(cn.name),
                Type.getObjectType(cn.superName == null ? "java/lang/Object" : cn.superName),
                new ArrayList<Type>(),
                (cn.access & Opcodes.ACC_INTERFACE) != 0) {
            private static final long serialVersionUID = 1L;

            @Override
            protected Class<?> getClass(final Type t) {
                try {
                    return super.getClass(t);
                } catch (RuntimeException e) {
                    return Object.class;
                }
            }
        };
        verifier.setClassLoader(typeLoader);

        // 分析边界：
        //  - javac 编出的真实类自带正确 maxStack/maxLocals，直接使用，
        //    ASM 每帧只分配实际大小的 Value[]，分析极快；
        //  - DeadClassFactory 等用 ASM 直接搭出来的合成 MethodNode 从不调用
        //    visitMaxs（maxs=0，全靠写出时 COMPUTE_FRAMES 兜底）。若把帧数组
        //    放大到 65535，每个可达帧都惰性分配 256KB 槽数组，200 个伪代码类
        //    ×十几个方法会产生数 GB 垃圾、把混淆拖慢一个数量级。
        //    因此先按"实际出现过的局部槽 + 固定保守栈深"给合成方法一个紧凑
        //    边界分析；万一边界仍不够（极端构造）再回退 65535 重试，保证正确。
        int observedMaxSlot = 0;
        for (AbstractInsnNode n : insns) {
            if (n instanceof VarInsnNode) {
                VarInsnNode v = (VarInsnNode) n;
                int w = (v.getOpcode() == Opcodes.LLOAD || v.getOpcode() == Opcodes.DLOAD
                        || v.getOpcode() == Opcodes.LSTORE || v.getOpcode() == Opcodes.DSTORE) ? 2 : 1;
                observedMaxSlot = Math.max(observedMaxSlot, v.var + w);
            } else if (n instanceof IincInsnNode) {
                observedMaxSlot = Math.max(observedMaxSlot, ((IincInsnNode) n).var + 1);
            }
        }
        int declaredLocals = mn.maxLocals;
        int declaredStack = mn.maxStack;
        int analysisLocals = declaredLocals > 0
                ? Math.max(declaredLocals, observedMaxSlot)
                : Math.max(observedMaxSlot, 8);
        int analysisStack = declaredStack > 0 ? declaredStack : SYNTH_STACK_BOUND;

        Frame<BasicValue>[] frames = analyzeFrames(cn, mn, verifier,
                analysisLocals, analysisStack);
        if (frames == null) {
            return 0;
        }
        int maxSlot = observedMaxSlot;
        // 收集每个候选槽的"定型类型"
        Map<Integer, Type> settled = new HashMap<Integer, Type>();
        Set<Integer> rejected = new HashSet<Integer>();
        for (int fi = 0; fi < frames.length; fi++) {
            Frame<BasicValue> f = frames[fi];
            if (f == null) {
                continue;
            }
            int scanLimit = Math.min(f.getLocals(), maxSlot);
            for (int slot = firstLocal; slot < scanLimit; slot++) {
                if (rejected.contains(slot)) {
                    continue;
                }
                BasicValue bv = f.getLocal(slot);
                if (bv == null) {
                    continue; // null 常量流，通配
                }
                Type t = bv.getType();
                if (t == null) {
                    // 定义点之前的帧上该槽为 TOP（未初始化），属正常现象：
                    // 只有在已经定型之后再遇到 TOP（不同路径定义状态不一致），
                    // 才判定为不安全并拒绝。否则忽略，等待后续帧上的定型。
                    if (settled.containsKey(slot)) {
                        rejected.add(slot);
                        settled.remove(slot);
                    }
                    continue;
                }
                Type prev = settled.get(slot);
                if (prev == null) {
                    settled.put(slot, t);
                } else if (!prev.equals(t)) {
                    rejected.add(slot);
                    settled.remove(slot);
                }
            }
        }
        // 长/双精度的次槽永远是 TOP，天然在 rejected；主槽描述符为 J/D 正常提升
        List<Integer> candidates = new ArrayList<Integer>();
        for (Map.Entry<Integer, Type> e : settled.entrySet()) {
            int slot = e.getKey().intValue();
            if (slot < maxSlot && !rejected.contains(slot)) {
                Type t = e.getValue();
                int sort = t.getSort();
                if (sort == Type.INT || sort == Type.FLOAT || sort == Type.LONG
                        || sort == Type.DOUBLE || sort == Type.OBJECT
                        || sort == Type.ARRAY) {
                    candidates.add(slot);
                }
            }
        }
        if (candidates.isEmpty()) {
            return 0;
        }

        // 每构建随机：洗牌 + 独立概率，提升数量不确定
        java.util.Collections.shuffle(candidates, random);
        double keepChance = 0.62 + random.nextDouble() * 0.33;
        Map<Integer, FieldNode> chosen = new HashMap<Integer, FieldNode>();
        for (Integer slotObj : candidates) {
            if (chosen.size() >= budget) {
                break;
            }
            if (random.nextDouble() > keepChance) {
                continue;
            }
            int slot = slotObj.intValue();
            Type t = settled.get(slot);
            String name = uniqueName(used, random);
            used.add(name);
            FieldNode f = new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_SYNTHETIC | Opcodes.ACC_TRANSIENT,
                    name, t.getDescriptor(), null, null);
            int pos = cn.fields.isEmpty() ? 0 : random.nextInt(cn.fields.size() + 1);
            cn.fields.add(pos, f);
            chosen.put(Integer.valueOf(slot), f);
        }
        if (chosen.isEmpty()) {
            return 0;
        }

        // 改写 barrier 之后的变量访问
        for (int i = 0; i < insns.length; i++) {
            if (isInit && i <= barrierIndex) {
                continue;
            }
            AbstractInsnNode n = insns[i];
            if (n instanceof VarInsnNode) {
                VarInsnNode v = (VarInsnNode) n;
                FieldNode f = chosen.get(Integer.valueOf(v.var));
                if (f == null) {
                    continue;
                }
                int op = v.getOpcode();
                int cat = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                        || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                boolean load;
                switch (op) {
                    case Opcodes.ILOAD: case Opcodes.FLOAD: case Opcodes.ALOAD:
                    case Opcodes.LLOAD: case Opcodes.DLOAD:
                        load = true;
                        break;
                    case Opcodes.ISTORE: case Opcodes.FSTORE: case Opcodes.ASTORE:
                    case Opcodes.LSTORE: case Opcodes.DSTORE:
                        load = false;
                        break;
                    default:
                        continue;
                }
                InsnList rep = new InsnList();
                if (load) {
                    rep.add(new VarInsnNode(Opcodes.ALOAD, 0));
                    rep.add(new org.objectweb.asm.tree.FieldInsnNode(
                            Opcodes.GETFIELD, cn.name, f.name, f.desc));
                } else if (cat == 1) {
                    // 栈顶 v  ->  [this, v]  -> PUTFIELD
                    rep.add(new VarInsnNode(Opcodes.ALOAD, 0));
                    rep.add(new InsnNode(Opcodes.SWAP));
                    rep.add(new org.objectweb.asm.tree.FieldInsnNode(
                            Opcodes.PUTFIELD, cn.name, f.name, f.desc));
                } else {
                    // 栈顶 v(2) -> ALOAD0 -> DUP_X2 -> POP -> [this, v] -> PUTFIELD
                    rep.add(new VarInsnNode(Opcodes.ALOAD, 0));
                    rep.add(new InsnNode(Opcodes.DUP_X2));
                    rep.add(new InsnNode(Opcodes.POP));
                    rep.add(new org.objectweb.asm.tree.FieldInsnNode(
                            Opcodes.PUTFIELD, cn.name, f.name, f.desc));
                }
                mn.instructions.insertBefore(n, rep);
                mn.instructions.remove(n);
            } else if (n instanceof IincInsnNode) {
                IincInsnNode inc = (IincInsnNode) n;
                FieldNode f = chosen.get(Integer.valueOf(inc.var));
                if (f == null) {
                    continue;
                }
                InsnList rep = new InsnList();
                rep.add(new VarInsnNode(Opcodes.ALOAD, 0));
                rep.add(new org.objectweb.asm.tree.FieldInsnNode(
                        Opcodes.GETFIELD, cn.name, f.name, f.desc));
                pushInt(rep, inc.incr);
                rep.add(new InsnNode(Opcodes.IADD));
                rep.add(new VarInsnNode(Opcodes.ALOAD, 0));
                rep.add(new InsnNode(Opcodes.SWAP));
                rep.add(new org.objectweb.asm.tree.FieldInsnNode(
                        Opcodes.PUTFIELD, cn.name, f.name, f.desc));
                mn.instructions.insertBefore(n, rep);
                mn.instructions.remove(n);
            }
        }
        // 改写后不再恢复 maxStack/maxLocals：写出时 COMPUTE_FRAMES 会整体重算
        return chosen.size();
    }

    private static String uniqueName(Set<String> used, Random random) {
        String name;
        do {
            int len = 6 + random.nextInt(5);
            StringBuilder sb = new StringBuilder(len);
            for (int i = 0; i < len; i++) {
                sb.append((char) ('a' + random.nextInt(26)));
            }
            name = sb.toString();
        } while (used.contains(name));
        return name;
    }

    private static void pushInt(InsnList il, int v) {
        if (v >= -1 && v <= 5) {
            il.add(new InsnNode(Opcodes.ICONST_0 + v));
        } else if (v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE) {
            il.add(new org.objectweb.asm.tree.IntInsnNode(Opcodes.BIPUSH, v));
        } else if (v >= Short.MIN_VALUE && v <= Short.MAX_VALUE) {
            il.add(new org.objectweb.asm.tree.IntInsnNode(Opcodes.SIPUSH, v));
        } else {
            il.add(new org.objectweb.asm.tree.LdcInsnNode(Integer.valueOf(v)));
        }
    }
}
