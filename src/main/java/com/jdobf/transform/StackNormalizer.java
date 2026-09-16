package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FrameNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SimpleVerifier;

import java.util.ArrayList;
import java.util.List;

/**
 * 栈归并归一化：把“跳转目标标签处操作数栈非空”的控制流（javac 为三目表达式、
 * 字符串拼接、短路求值等生成的 {@code GOTO L; L: ASTORE} 形态）改写成经过
 * 合成局部变量暂存的空栈汇合，使方法满足 switch 状态机平坦化的前提
 * （每个基本块入口栈必须为空）。
 *
 * 对每个入栈深度 d&gt;0 的标签位置 L：
 * <pre>
 *   GOTO L（栈上有 d 个值）        ASTORE/STORE 暂存；GOTO L'
 *   顺序落入 L（栈上有 d 个值） -> STORE 暂存；GOTO L'
 *   L: 消费栈值                    L': LOAD 还原 d 个值；L: 消费
 * </pre>
 *
 * 值的精确类型取自原始字节码的 SimpleVerifier 帧。出现无法处理的形态
 * （条件跳转/switch 直接落在非空栈标签上）则放弃，返回 false，调用方
 * 跳过该方法的平坦化。
 */
public final class StackNormalizer {

    private StackNormalizer() {
    }

    /** 归一化成功返回 true（方法可能已被改写）；无法处理时返回 false（方法不变）。 */
    public static boolean normalize(ClassNode cn, MethodNode mn, ClassLoader typeLoader) {
        AbstractInsnNode[] insns = mn.instructions.toArray();

        int savedMaxStack = mn.maxStack;
        int savedMaxLocals = mn.maxLocals;
        // 紧边界帧分析（实际槽位 + 保守栈深，不足自动回退上限重试），
        // 避免 65535×65535 帧数组在伪代码类/大方法上产生数 GB 短命对象
        Frame<BasicValue>[] frames = Analysis.verify(cn, mn, typeLoader);
        if (frames == null) {
            return false;
        }

        // 1. 找出所有入栈非空的标签位置；连续标签（中间仅有帧/行号伪节点）
        //    共享同一位置帧，合成一组
        List<List<LabelNode>> groups = new ArrayList<List<LabelNode>>();
        List<Integer> groupAt = new ArrayList<Integer>();
        LabelNode prevRealLabel = null;
        int lastGroupEnd = -2;
        for (int i = 0; i < insns.length; i++) {
            if (!(insns[i] instanceof LabelNode)) {
                continue;
            }
            LabelNode lab = (LabelNode) insns[i];
            Frame<BasicValue> f = frames[i];
            if (f == null || f.getStackSize() == 0) {
                prevRealLabel = lab;
                continue;
            }
            // 任何非 GOTO 跳转或 switch 直接落到非空栈标签：放弃
            for (AbstractInsnNode n : insns) {
                if (n instanceof JumpInsnNode) {
                    JumpInsnNode j = (JumpInsnNode) n;
                    if (j.getOpcode() != Opcodes.GOTO && j.label == lab) {
                        return abort(mn, savedMaxStack, savedMaxLocals);
                    }
                } else if (n instanceof TableSwitchInsnNode) {
                    TableSwitchInsnNode t = (TableSwitchInsnNode) n;
                    if (t.dflt == lab || t.labels.contains(lab)) {
                        return abort(mn, savedMaxStack, savedMaxLocals);
                    }
                } else if (n instanceof org.objectweb.asm.tree.LookupSwitchInsnNode) {
                    org.objectweb.asm.tree.LookupSwitchInsnNode t =
                            (org.objectweb.asm.tree.LookupSwitchInsnNode) n;
                    if (t.dflt == lab || t.labels.contains(lab)) {
                        return abort(mn, savedMaxStack, savedMaxLocals);
                    }
                }
            }
            // 与上一个非空栈标签之间只隔伪节点/其它标签，则同属一组
            boolean adjacent = false;
            if (prevRealLabel != null && !groups.isEmpty() && lastGroupEnd >= 0) {
                AbstractInsnNode p = lab.getPrevious();
                while (p instanceof FrameNode || p instanceof LineNumberNode) {
                    p = p.getPrevious();
                }
                adjacent = p == groups.get(groups.size() - 1)
                        .get(groups.get(groups.size() - 1).size() - 1);
            }
            if (adjacent) {
                groups.get(groups.size() - 1).add(lab);
            } else {
                List<LabelNode> g = new ArrayList<LabelNode>();
                g.add(lab);
                groups.add(g);
                groupAt.add(i);
            }
            lastGroupEnd = i;
            prevRealLabel = lab;
        }
        if (groups.isEmpty()) {
            mn.maxStack = savedMaxStack;
            mn.maxLocals = savedMaxLocals;
            return true;
        }

        // 2. 逐位置改写
        int nextSlot = initialSlot(mn);
        for (AbstractInsnNode n : insns) {
            int op = n.getOpcode();
            if (n instanceof org.objectweb.asm.tree.VarInsnNode) {
                int size = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                        || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                nextSlot = Math.max(nextSlot, ((VarInsnNode) n).var + size);
            }
        }

        for (int gi = 0; gi < groups.size(); gi++) {
            List<LabelNode> g = groups.get(gi);
            int at = groupAt.get(gi);
            Frame<BasicValue> f = frames[at];
            int depth = f.getStackSize();

            // 栈值类型（底 -> 顶）与暂存槽
            int[] slots = new int[depth];
            Type[] types = new Type[depth];
            for (int k = 0; k < depth; k++) {
                Type t = f.getStack(k).getType();
                if (t == null) {
                    t = Type.getObjectType("java/lang/Object");
                }
                types[k] = t;
                slots[k] = nextSlot;
                nextSlot += t.getSize();
            }
            if (nextSlot > 65535) {
                mn.maxStack = savedMaxStack;
                mn.maxLocals = savedMaxLocals;
                return false;
            }

            LabelNode norm = new LabelNode();

            // 顺序落入：若本组第一个标签的物理前驱不是无条件终止指令，
            // 先插入“暂存 + GOTO norm”（必须保证它在 norm 还原段之前）
            AbstractInsnNode before = g.get(0).getPrevious();
            while (before instanceof LabelNode || before instanceof FrameNode
                    || before instanceof LineNumberNode) {
                before = before.getPrevious();
            }
            if (before != null && !isUnconditionalBarrier(before.getOpcode())) {
                InsnList guard = buildStores(types, slots);
                guard.add(new JumpInsnNode(Opcodes.GOTO, norm));
                mn.instructions.insertBefore(g.get(0), guard);
            }

            // 所有跳到本组标签的 GOTO：跳转前把栈值存入暂存槽，目标改为 norm
            for (AbstractInsnNode n : mn.instructions.toArray()) {
                if (!(n instanceof JumpInsnNode) || n.getOpcode() != Opcodes.GOTO) {
                    continue;
                }
                JumpInsnNode j = (JumpInsnNode) n;
                if (!g.contains(j.label)) {
                    continue;
                }
                InsnList stores = buildStores(types, slots);
                mn.instructions.insertBefore(j, stores);
                j.label = norm;
            }

            // norm: 按底->顶顺序还原栈值，然后顺序进入原标签
            InsnList loads = new InsnList();
            loads.add(norm);
            for (int k = 0; k < depth; k++) {
                appendLoad(loads, types[k], slots[k]);
            }
            mn.instructions.insertBefore(g.get(0), loads);
        }

        mn.localVariables = null;
        mn.visibleLocalVariableAnnotations = null;
        mn.invisibleLocalVariableAnnotations = null;
        return true;
    }

    private static boolean abort(MethodNode mn, int savedMaxStack, int savedMaxLocals) {
        mn.maxStack = savedMaxStack;
        mn.maxLocals = savedMaxLocals;
        return false;
    }

    /** 顶 -> 底 依次出栈存入暂存槽。 */
    private static InsnList buildStores(Type[] types, int[] slots) {
        InsnList out = new InsnList();
        for (int k = types.length - 1; k >= 0; k--) {
            out.add(new VarInsnNode(storeOpcode(types[k]), slots[k]));
        }
        return out;
    }

    private static void appendLoad(InsnList out, Type t, int slot) {
        out.add(new VarInsnNode(loadOpcode(t), slot));
        if (t.getSort() == Type.OBJECT || t.getSort() == Type.ARRAY) {
            String name = t.getSort() == Type.ARRAY ? t.getDescriptor() : t.getInternalName();
            if (!name.equals("java/lang/Object")) {
                out.add(new org.objectweb.asm.tree.TypeInsnNode(Opcodes.CHECKCAST, name));
            }
        }
    }

    private static int storeOpcode(Type t) {
        switch (t.getSort()) {
            case Type.LONG:
                return Opcodes.LSTORE;
            case Type.FLOAT:
                return Opcodes.FSTORE;
            case Type.DOUBLE:
                return Opcodes.DSTORE;
            case Type.OBJECT:
            case Type.ARRAY:
                return Opcodes.ASTORE;
            default:
                return Opcodes.ISTORE;
        }
    }

    private static int loadOpcode(Type t) {
        switch (t.getSort()) {
            case Type.LONG:
                return Opcodes.LLOAD;
            case Type.FLOAT:
                return Opcodes.FLOAD;
            case Type.DOUBLE:
                return Opcodes.DLOAD;
            case Type.OBJECT:
            case Type.ARRAY:
                return Opcodes.ALOAD;
            default:
                return Opcodes.ILOAD;
        }
    }

    private static boolean isUnconditionalBarrier(int op) {
        return op == Opcodes.GOTO || op == Opcodes.RETURN || op == Opcodes.ARETURN
                || op == Opcodes.IRETURN || op == Opcodes.LRETURN || op == Opcodes.FRETURN
                || op == Opcodes.DRETURN || op == Opcodes.ATHROW
                || op == Opcodes.TABLESWITCH || op == Opcodes.LOOKUPSWITCH;
    }

    private static int initialSlot(MethodNode mn) {
        int slot = (mn.access & Opcodes.ACC_STATIC) != 0 ? 0 : 1;
        for (Type t : Type.getArgumentTypes(mn.desc)) {
            slot += t.getSize();
        }
        return slot;
    }
}
