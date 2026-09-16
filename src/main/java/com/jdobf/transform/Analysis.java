package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SimpleVerifier;

import java.util.ArrayList;
import java.util.List;

/**
 * 帧分析统一入口：紧边界 + 一次性上限回退。
 *
 * ASM 的 {@link Analyzer} 按 MethodNode.maxLocals/maxStack 为<b>每个可达指令</b>
 * 分配一帧，Frame 构造时立即 new Value[locals+stack]。早期各 pass 一律把这两个
 * 值撑到 65535，单帧即约 512KB：DeadClassFactory 合成方法 maxs=0/0、
 * LocalVariableLifting 成功后也把 maxs 永久留在 65535，于是 200 个伪代码类
 * 与平坦化后的巨型方法会产生数 GB 短命数组，混淆长期“卡在 0”。
 *
 * 本工具按指令流实际出现过的局部槽 + 保守栈深给出紧凑边界（真实类自带的正确
 * maxs 直接采用），分析后原样还原 maxs；边界不足引发的任何异常再用 65535
 * 重试一次（真实校验错误在重试下同样失败，返回 null）。
 */
public final class Analysis {

    /** 合成方法（maxs=0/0 或被前序 pass 放大）的默认栈深上界。 */
    public static final int SYNTH_STACK_BOUND = 512;
    /** 紧边界栈深下限，防止声明值过小（变换后方法体变大）导致无谓重试。 */
    private static final int STACK_MIN = 16;
    /** 紧边界栈深上限：正常业务/平坦化代码栈深远小于此。 */
    private static final int STACK_MAX = 4096;
    private static final int HARD_LIMIT = 65535;

    private Analysis() {
    }

    /** 扫描指令流得到实际使用过的最大局部槽位（含 cat2 宽度）。 */
    public static int observedMaxSlot(MethodNode mn) {
        int max = 0;
        for (AbstractInsnNode n : mn.instructions.toArray()) {
            if (n instanceof VarInsnNode) {
                int op = n.getOpcode();
                int w = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                        || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                max = Math.max(max, ((VarInsnNode) n).var + w);
            } else if (n instanceof IincInsnNode) {
                max = Math.max(max, ((IincInsnNode) n).var + 1);
            }
        }
        return max;
    }

    /** BasicInterpreter 紧边界分析；失败（含边界不足）返回 null，maxs 原样还原。 */
    public static Frame<BasicValue>[] basic(MethodNode mn) {
        int savedStack = mn.maxStack;
        int savedLocals = mn.maxLocals;
        try {
            int[] bounds = tightBounds(mn);
            mn.maxStack = bounds[0];
            mn.maxLocals = bounds[1];
            try {
                return new Analyzer<BasicValue>(new BasicInterpreter()).analyze(null, mn);
            } catch (Throwable first) {
                if (bounds[0] == HARD_LIMIT && bounds[1] == HARD_LIMIT) {
                    return null;
                }
                mn.maxStack = HARD_LIMIT;
                mn.maxLocals = HARD_LIMIT;
                try {
                    return new Analyzer<BasicValue>(new BasicInterpreter()).analyze(null, mn);
                } catch (Throwable second) {
                    return null;
                }
            }
        } finally {
            mn.maxStack = savedStack;
            mn.maxLocals = savedLocals;
        }
    }

    /**
     * SimpleVerifier 紧边界分析。owner 可为 null（栈中性检查场景）；
     * typeLoader 用于解析 jar 内类型，可为 null。失败返回 null，maxs 原样还原。
     */
    public static Frame<BasicValue>[] verify(ClassNode cn, MethodNode mn,
                                              ClassLoader typeLoader) {
        SimpleVerifier verifier = null;
        if (cn != null) {
            List<org.objectweb.asm.Type> interfaces =
                    new ArrayList<org.objectweb.asm.Type>();
            if (cn.interfaces != null) {
                for (String itf : cn.interfaces) {
                    interfaces.add(org.objectweb.asm.Type.getObjectType(itf));
                }
            }
            final boolean isInterface = (cn.access & Opcodes.ACC_INTERFACE) != 0;
            verifier = new SimpleVerifier(
                    Opcodes.ASM9,
                    org.objectweb.asm.Type.getObjectType(cn.name),
                    cn.superName != null
                            ? org.objectweb.asm.Type.getObjectType(cn.superName)
                            : org.objectweb.asm.Type.getObjectType("java/lang/Object"),
                    interfaces, isInterface) {
                private static final long serialVersionUID = 1L;

                @Override
                protected Class<?> getClass(final org.objectweb.asm.Type t) {
                    try {
                        return super.getClass(t);
                    } catch (RuntimeException e) {
                        return Object.class;
                    }
                }
            };
            if (typeLoader != null) {
                verifier.setClassLoader(typeLoader);
            }
        }
        int savedStack = mn.maxStack;
        int savedLocals = mn.maxLocals;
        try {
            int[] bounds = tightBounds(mn);
            mn.maxStack = bounds[0];
            mn.maxLocals = bounds[1];
            try {
                return new Analyzer<BasicValue>(
                        verifier != null ? verifier : new BasicInterpreter())
                        .analyze(cn != null ? cn.name : null, mn);
            } catch (Throwable first) {
                if (bounds[0] == HARD_LIMIT && bounds[1] == HARD_LIMIT) {
                    return null;
                }
                mn.maxStack = HARD_LIMIT;
                mn.maxLocals = HARD_LIMIT;
                try {
                    return new Analyzer<BasicValue>(
                            verifier != null ? verifier : new BasicInterpreter())
                            .analyze(cn != null ? cn.name : null, mn);
                } catch (Throwable second) {
                    return null;
                }
            }
        } finally {
            mn.maxStack = savedStack;
            mn.maxLocals = savedLocals;
        }
    }

    /**
     * 计算紧凑分析边界 [stack, locals]：
     * locals 取声明值（若可信）与实际槽位扫描的较大值；stack 用声明值，
     * 合成/被放大的方法（0 或 65535）退化为保守常量。
     */
    private static int[] tightBounds(MethodNode mn) {
        int observed = observedMaxSlot(mn);
        int locals;
        if (mn.maxLocals > 0 && mn.maxLocals < HARD_LIMIT) {
            locals = Math.max(mn.maxLocals, observed);
        } else {
            locals = Math.max(observed, 8);
        }
        int stack;
        if (mn.maxStack > 0 && mn.maxStack < HARD_LIMIT) {
            stack = Math.max(Math.min(mn.maxStack, STACK_MAX), STACK_MIN);
        } else {
            stack = SYNTH_STACK_BOUND;
        }
        return new int[] { stack, locals };
    }
}
