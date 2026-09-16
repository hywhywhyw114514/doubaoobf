package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.SimpleVerifier;

import java.util.ArrayList;
import java.util.List;

/**
 * 局部变量提升：把方法的全部局部变量槽位搬到一个 Object[] 数组中，
 * 每次读取都 CHECKCAST/拆箱为精确类型，每次写入都装箱后 AASTORE。
 *
 * 这是 switch 状态机平坦化的前置步骤：平坦化后所有基本块都在同一个
 * dispatch 标签处汇合，若局部变量在部分前驱路径上未赋值，JVM 验证器会把
 * 类型合并成 TOP（未初始化）导致 VerifyError；提升后所有槽位在 dispatch
 * 处恒为 Object（数组元素），块内读出处再按原始栈帧的精确类型还原，
 * 从而通过类型校验。
 *
 * 精确类型来自对原始字节码运行 SimpleVerifier 数据流分析；任何分析失败
 * （缺失依赖等）则放弃提升，调用方应跳过该方法的平坦化。
 */
public final class LocalVariableLifting {

    private LocalVariableLifting() {
    }

    /**
     * 提升成功返回 true。
     *
     * @param arrSlotOut  [0] 输出承载数组的局部变量槽位
     * @param prologueOut [0] 输出必须在方法最开头（状态机初始化之前）执行的
     *                    “建数组 + 参数装箱”指令；由调用方负责放置
     */
    public static boolean lift(ClassNode cn, MethodNode mn, ClassLoader typeLoader,
                               int[] arrSlotOut, InsnList[] prologueOut) {
        if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0
                || mn.instructions.size() == 0) {
            return false;
        }

        AbstractInsnNode[] insns = mn.instructions.toArray();

        // 1. 原始字节码数据流分析，获取每条指令处各局部变量的精确类型。
        //    紧边界帧（实际槽位 + 保守栈深，不足自动回退上限重试）：
        //    成功后不再把 maxs 永久留在 65535，后续 pass 与最终写出都更快。
        boolean isStatic = (mn.access & Opcodes.ACC_STATIC) != 0;
        Type thisType = isStatic ? null : Type.getObjectType(cn.name);
        Frame<BasicValue>[] frames = Analysis.verify(cn, mn, typeLoader);
        if (frames == null) {
            return false;
        }

        // 2. 统计槽位上界，确定数组槽
        int maxSlot = isStatic ? 0 : 1;
        for (Type t : Type.getArgumentTypes(mn.desc)) {
            maxSlot += t.getSize();
        }
        int varAccess = 0;
        for (AbstractInsnNode n : insns) {
            if (n instanceof VarInsnNode) {
                VarInsnNode v = (VarInsnNode) n;
                int size = (v.getOpcode() == Opcodes.LLOAD || v.getOpcode() == Opcodes.DLOAD
                        || v.getOpcode() == Opcodes.LSTORE || v.getOpcode() == Opcodes.DSTORE) ? 2 : 1;
                maxSlot = Math.max(maxSlot, v.var + size);
                varAccess++;
            } else if (n instanceof IincInsnNode) {
                maxSlot = Math.max(maxSlot, ((IincInsnNode) n).var + 1);
                varAccess++;
            }
        }
        int arrSlot = maxSlot;
        int arraySize = Math.max(1, maxSlot);

        // 粗略 64KB 方法体预算（提升后每次变量访问约 14 字节）
        long estimate = (long) insns.length * 3L + (long) varAccess * 14L + 64L;
        if (estimate > 56000L) {
            return false;
        }

        // 3. 改写全部变量访问（在原指令列表上逐条替换）
        for (int idx = 0; idx < insns.length; idx++) {
            AbstractInsnNode n = insns[idx];
            if (n instanceof VarInsnNode) {
                VarInsnNode v = (VarInsnNode) n;
                if (v.var >= maxSlot) {
                    continue;
                }
                InsnList repl = rewriteVarAccess(v, frames[idx], arrSlot);
                if (repl == null) {
                    return false;
                }
                mn.instructions.insertBefore(v, repl);
                mn.instructions.remove(v);
            } else if (n instanceof IincInsnNode) {
                IincInsnNode inc = (IincInsnNode) n;
                if (inc.var >= maxSlot) {
                    continue;
                }
                mn.instructions.insertBefore(inc, rewriteIinc(inc, arrSlot));
                mn.instructions.remove(inc);
            }
        }

        // 4. 方法开头：new Object[size] 并把参数（含 this）装箱存入
        InsnList prologue = new InsnList();
        pushInt(prologue, arraySize);
        prologue.add(new TypeInsnNode(Opcodes.ANEWARRAY, "java/lang/Object"));
        prologue.add(new VarInsnNode(Opcodes.ASTORE, arrSlot));

        int slot = 0;
        if (thisType != null) {
            appendBoxedPut(prologue, arrSlot, slot, thisType);
            slot++;
        }
        for (Type t : Type.getArgumentTypes(mn.desc)) {
            appendBoxedPut(prologue, arrSlot, slot, t);
            slot += t.getSize();
        }
        // 序言交由调用方放置：平坦化时必须位于状态机初始化之前，否则 dispatch
        // 汇合帧里数组槽位是 TOP，所有 case 读数组都 VerifyError
        prologueOut[0] = prologue;

        // 旧调试属性失效
        mn.localVariables = null;
        mn.visibleLocalVariableAnnotations = null;
        mn.invisibleLocalVariableAnnotations = null;

        arrSlotOut[0] = arrSlot;
        return true;
    }

    /**
     * 生成：arr[var] = boxed(原槽位值)；值从原槽位读出，arr/index 先入栈，box 在栈顶就地完成。
     *
     * 注意：boolean/byte/char/short/int 在字节码层同为 int 运算，方法体的
     * ISTORE/ILOAD 改写一律按 Integer 装箱，且同一槽位可能被这些类型跨作用域
     * 复用，因此序言也必须统一装箱为 Integer，否则运行期会出现
     * Boolean/Byte/Short → Integer 的 ClassCastException。
     */
    private static void appendBoxedPut(InsnList out, int arrSlot, int var, Type t) {
        out.add(new VarInsnNode(Opcodes.ALOAD, arrSlot));
        pushInt(out, var);
        int loadOp;
        Type boxType;
        switch (t.getSort()) {
            case Type.BOOLEAN:
            case Type.BYTE:
            case Type.CHAR:
            case Type.SHORT:
            case Type.INT:
                loadOp = Opcodes.ILOAD;
                boxType = Type.INT_TYPE;
                break;
            case Type.LONG:
                loadOp = Opcodes.LLOAD;
                boxType = Type.LONG_TYPE;
                break;
            case Type.FLOAT:
                loadOp = Opcodes.FLOAD;
                boxType = Type.FLOAT_TYPE;
                break;
            case Type.DOUBLE:
                loadOp = Opcodes.DLOAD;
                boxType = Type.DOUBLE_TYPE;
                break;
            default:
                loadOp = Opcodes.ALOAD;
                boxType = t;
        }
        out.add(new VarInsnNode(loadOp, var));
        box(out, boxType);
        out.add(new InsnNode(Opcodes.AASTORE));
    }

    /**
     * 变量访问改写。
     * LOAD：ALOAD arr; push idx; AALOAD; CHECKCAST/拆箱。
     * STORE：值在栈顶就地装箱，再把 arr/index 插到其下：
     *   [B] ALOAD arr -> [B,A]; push idx -> [B,A,I];
     *   DUP2_X1 -> [A,I,B,A,I]; POP2 -> [A,I,B]; AASTORE -> []
     * （装箱后 B 恒为 1 类槽引用，long/double 同理）
     */
    private static InsnList rewriteVarAccess(VarInsnNode v, Frame<BasicValue> frame, int arrSlot) {
        int op = v.getOpcode();
        InsnList out = new InsnList();
        if (op >= Opcodes.ILOAD && op <= Opcodes.ALOAD) {
            out.add(new VarInsnNode(Opcodes.ALOAD, arrSlot));
            pushInt(out, v.var);
            out.add(new InsnNode(Opcodes.AALOAD));
            switch (op) {
                case Opcodes.ILOAD:
                    out.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Integer"));
                    out.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                            "java/lang/Integer", "intValue", "()I", false));
                    break;
                case Opcodes.LLOAD:
                    out.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Long"));
                    out.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                            "java/lang/Long", "longValue", "()J", false));
                    break;
                case Opcodes.FLOAD:
                    out.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Float"));
                    out.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                            "java/lang/Float", "floatValue", "()F", false));
                    break;
                case Opcodes.DLOAD:
                    out.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Double"));
                    out.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                            "java/lang/Double", "doubleValue", "()D", false));
                    break;
                case Opcodes.ALOAD: {
                    String internal = refInternalName(frame, v.var);
                    if (internal != null && !internal.equals("java/lang/Object")) {
                        out.add(new TypeInsnNode(Opcodes.CHECKCAST, internal));
                    }
                    break;
                }
                default:
                    return null;
            }
            return out;
        }

        // STORE：引用类型无需装箱；基本类型就地装箱（2 类槽变 1 类槽）
        switch (op) {
            case Opcodes.ISTORE:
                box(out, Type.INT_TYPE);
                break;
            case Opcodes.LSTORE:
                box(out, Type.LONG_TYPE);
                break;
            case Opcodes.FSTORE:
                box(out, Type.FLOAT_TYPE);
                break;
            case Opcodes.DSTORE:
                box(out, Type.DOUBLE_TYPE);
                break;
            case Opcodes.ASTORE:
                break;
            default:
                return null;
        }
        out.add(new VarInsnNode(Opcodes.ALOAD, arrSlot));
        pushInt(out, v.var);
        out.add(new InsnNode(Opcodes.DUP2_X1));
        out.add(new InsnNode(Opcodes.POP2));
        out.add(new InsnNode(Opcodes.AASTORE));
        return out;
    }

    /**
     * IINC var, n：arr/idx 复制后取数计算，严格栈平衡：
     * [A] push idx [A,I] DUP2 [A,I,A,I] AALOAD [A,I,B]
     * checkcast/intValue/+n/valueOf -> [A,I,B2] AASTORE -> []
     */
    private static InsnList rewriteIinc(IincInsnNode inc, int arrSlot) {
        InsnList out = new InsnList();
        out.add(new VarInsnNode(Opcodes.ALOAD, arrSlot));
        pushInt(out, inc.var);
        out.add(new InsnNode(Opcodes.DUP2));
        out.add(new InsnNode(Opcodes.AALOAD));
        out.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Integer"));
        out.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/Integer", "intValue", "()I", false));
        if (inc.incr != 0) {
            pushInt(out, inc.incr);
            out.add(new InsnNode(Opcodes.IADD));
        }
        box(out, Type.INT_TYPE);
        out.add(new InsnNode(Opcodes.AASTORE));
        return out;
    }

    /** 基本类型装箱（引用类型直通）。 */
    private static void box(InsnList out, Type t) {
        switch (t.getSort()) {
            case Type.BOOLEAN:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Boolean", "valueOf", "(Z)Ljava/lang/Boolean;", false));
                break;
            case Type.BYTE:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Byte", "valueOf", "(B)Ljava/lang/Byte;", false));
                break;
            case Type.CHAR:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Character", "valueOf", "(C)Ljava/lang/Character;", false));
                break;
            case Type.SHORT:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Short", "valueOf", "(S)Ljava/lang/Short;", false));
                break;
            case Type.INT:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;", false));
                break;
            case Type.LONG:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Long", "valueOf", "(J)Ljava/lang/Long;", false));
                break;
            case Type.FLOAT:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Float", "valueOf", "(F)Ljava/lang/Float;", false));
                break;
            case Type.DOUBLE:
                out.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/Double", "valueOf", "(D)Ljava/lang/Double;", false));
                break;
            default:
                break;
        }
    }

    private static String refInternalName(Frame<BasicValue> frame, int slot) {
        if (frame == null) {
            return "java/lang/Object";
        }
        BasicValue bv = frame.getLocal(slot);
        if (bv == null) {
            return "java/lang/Object";
        }
        Type t = bv.getType();
        if (t == null) {
            return "java/lang/Object";
        }
        if (t.getSort() == Type.OBJECT) {
            return t.getInternalName();
        }
        if (t.getSort() == Type.ARRAY) {
            return t.getDescriptor();
        }
        return "java/lang/Object";
    }

    static void pushInt(InsnList il, int v) {
        if (v == -1) {
            il.add(new InsnNode(Opcodes.ICONST_M1));
        } else if (v >= 0 && v <= 5) {
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
