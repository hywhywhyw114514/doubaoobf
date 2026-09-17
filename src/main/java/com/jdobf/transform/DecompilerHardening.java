package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * 反编译器抗性增强。
 *
 * <p>这里不生成非法 class，也不依赖 JVM 未定义行为。它把一个恒定选择的
 * 稀疏 LOOKUPSWITCH 和一个不可达异常岛叠加到已经完成的变换上。对 JVM 而言
 * 这只是合法的控制流；对基于结构化 CFG 的反编译器而言，原本的直线入口会
 * 变成多入口、带异常边和死状态的图，通常会触发保守输出或降低还原质量。</p>
 *
 * <p>该阶段刻意跳过构造器、静态初始化器、抽象/native 方法和过大的方法，避免
 * 破坏初始化顺序、异常语义或把方法推过 class-file 工具链的体积护栏。已有
 * 异常表的方法只接受入口扰动，不再追加异常岛。</p>
 */
public final class DecompilerHardening {

    private static final int MAX_METHOD_NODES = 12000;

    private DecompilerHardening() {
    }

    /** 返回实际增强的方法数。passes=1 只加入口扰动，2/3 再增加异常岛层次。 */
    public static int apply(ClassNode cn, Random random, int passes) {
        if (passes <= 0 || (cn.access & (Opcodes.ACC_INTERFACE
                | Opcodes.ACC_ANNOTATION | Opcodes.ACC_MODULE)) != 0) {
            return 0;
        }
        int count = 0;
        for (MethodNode mn : cn.methods) {
            if (!eligible(mn)) {
                continue;
            }
            try {
                if (addOpaqueEntry(mn, random)) {
                    // 已有异常表的方法仍可使用入口扰动；只有没有异常表时才
                    // 追加异常岛，避免改变原异常区间的边界关系。
                    if (passes >= 2 && (mn.tryCatchBlocks == null
                            || mn.tryCatchBlocks.isEmpty())) {
                        addExceptionIsland(mn, passes >= 3 ? 2 : 1);
                    }
                    count++;
                }
            } catch (Throwable ignored) {
                // 单个方法的抗性增强失败时保持该方法原样，外层仍可写出 jar。
            }
        }
        return count;
    }

    private static boolean eligible(MethodNode mn) {
        if (mn.instructions == null || mn.instructions.size() == 0
                || mn.instructions.size() > MAX_METHOD_NODES) {
            return false;
        }
        if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
            return false;
        }
        if ("<init>".equals(mn.name) || "<clinit>".equals(mn.name)) {
            return false;
        }
        return true;
    }

    private static boolean addOpaqueEntry(MethodNode mn, Random random) {
        AbstractInsnNode anchor = mn.instructions.getFirst();
        while (anchor != null && (anchor.getType() == AbstractInsnNode.LABEL
                || anchor.getType() == AbstractInsnNode.LINE
                || anchor.getType() == AbstractInsnNode.FRAME)) {
            anchor = anchor.getNext();
        }
        if (anchor == null) {
            return false;
        }

        int slot = nextLocal(mn);
        int seed = random.nextInt();
        LabelNode join = new LabelNode();
        LabelNode dflt = new LabelNode();
        LabelNode[] dead = { new LabelNode(), new LabelNode(), new LabelNode() };
        InsnList il = new InsnList();

        // switch 的 default/case 都跳到 join，随后自然落入原始首指令。
        pushInt(il, seed);
        il.add(new VarInsnNode(Opcodes.ISTORE, slot));
        il.add(new VarInsnNode(Opcodes.ILOAD, slot));
        il.add(new VarInsnNode(Opcodes.ILOAD, slot));
        il.add(new InsnNode(Opcodes.IXOR)); // 运行时恒为 0，但不直接出现常量 0
        il.add(new LookupSwitchInsnNode(dflt, new int[] { 0, 1, 2, 3 },
                new LabelNode[] { join, dead[0], dead[1], dead[2] }));

        for (int i = 0; i < dead.length; i++) {
            il.add(dead[i]);
            // 死路带有独立的算术和回跳，三个节点组成不可达环。
            // 选择器恒为 0，因此该环永远不会执行；但它保留了一个
            // 合法的循环 CFG，避免反编译器把所有 case 当作简单汇合块。
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            pushInt(il, random.nextInt(31) - 15);
            il.add(new InsnNode(i == 0 ? Opcodes.IXOR
                    : (i == 1 ? Opcodes.IADD : Opcodes.ISUB)));
            il.add(new VarInsnNode(Opcodes.ISTORE, slot));
            il.add(new JumpInsnNode(Opcodes.GOTO, dead[(i + 1) % dead.length]));
        }
        il.add(dflt);
        il.add(new JumpInsnNode(Opcodes.GOTO, join));
        il.add(join);
        mn.instructions.insertBefore(anchor, il);
        return true;
    }

    private static void addExceptionIsland(MethodNode mn, int layers) {
        int slot = nextLocal(mn);
        LabelNode start = new LabelNode();
        LabelNode end = new LabelNode();
        LabelNode after = new LabelNode();
        InsnList island = new InsnList();
        island.add(start);
        island.add(new InsnNode(Opcodes.NOP));
        island.add(end);
        island.add(new JumpInsnNode(Opcodes.GOTO, after));
        List<LabelNode> handlers = new ArrayList<LabelNode>();
        for (int i = 0; i < Math.max(1, Math.min(2, layers)); i++) {
            LabelNode handler = new LabelNode();
            handlers.add(handler);
            island.add(handler);
            island.add(new VarInsnNode(Opcodes.ASTORE, slot + i));
            island.add(new VarInsnNode(Opcodes.ALOAD, slot + i));
            island.add(new InsnNode(Opcodes.ATHROW));
        }
        island.add(after);
        // 添加到方法尾部；原方法的 return/throw 会使其成为正常不可达区域。
        // NOP 区间本身不产生异常，多个重叠 handler 只增加合法异常边，
        // 任意理论异常仍原样回抛，不吞掉或改变业务异常。
        mn.instructions.add(island);
        if (mn.tryCatchBlocks == null) {
            mn.tryCatchBlocks = new ArrayList<TryCatchBlockNode>();
        }
        for (LabelNode handler : handlers) {
            mn.tryCatchBlocks.add(new TryCatchBlockNode(start, end, handler,
                    "java/lang/Throwable"));
        }
    }

    private static int nextLocal(MethodNode mn) {
        // 先按描述符计入参数槽。仅扫描 VarInsnNode 会漏掉“只返回参数”
        // 这类方法，进而把参数槽误当成垃圾槽并覆盖业务输入。
        int max = ((mn.access & Opcodes.ACC_STATIC) == 0) ? 1 : 0;
        for (Type arg : Type.getArgumentTypes(mn.desc)) {
            max += arg.getSize();
        }
        for (AbstractInsnNode n : mn.instructions.toArray()) {
            if (n instanceof VarInsnNode) {
                VarInsnNode v = (VarInsnNode) n;
                int width = (v.getOpcode() == Opcodes.LLOAD || v.getOpcode() == Opcodes.DLOAD
                        || v.getOpcode() == Opcodes.LSTORE || v.getOpcode() == Opcodes.DSTORE) ? 2 : 1;
                max = Math.max(max, v.var + width);
            } else if (n instanceof IincInsnNode) {
                max = Math.max(max, ((IincInsnNode) n).var + 1);
            }
        }
        return max;
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
}
