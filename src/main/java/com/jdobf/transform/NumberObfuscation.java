package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.util.Random;

/**
 * int 数字常量混淆。
 *
 * 将压栈的整数 v 改写成两个随机整数的 XOR / ADD / SUB，
 * 仅做“一个 int 进、一个 int 出”的栈守恒替换，不改变任何控制流。
 * 构造器中只在 super/this 调用之后处理，规避初始化敏感区。
 */
public final class NumberObfuscation {

    private NumberObfuscation() {
    }

    public static int apply(ClassNode cn, Random random) {
        int count = 0;
        for (MethodNode mn : cn.methods) {
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            boolean allowed = true;
            AbstractInsnNode start = mn.instructions.getFirst();
            if (mn.name.equals("<init>")) {
                // 找到 super()/this() 调用，只替换它之后的指令
                AbstractInsnNode p = mn.instructions.getFirst();
                AbstractInsnNode superCall = null;
                while (p != null) {
                    if (p.getOpcode() == Opcodes.INVOKESPECIAL
                            && p instanceof MethodInsnNode
                            && ((MethodInsnNode) p).name.equals("<init>")) {
                        superCall = p;
                        break;
                    }
                    p = p.getNext();
                }
                if (superCall == null) {
                    allowed = false;
                } else {
                    start = superCall.getNext();
                }
            }
            if (!allowed) {
                continue;
            }
            AbstractInsnNode insn = start;
            while (insn != null) {
                AbstractInsnNode next = insn.getNext();
                Integer value = intConstant(insn);
                if (value != null) {
                    InsnList replacement = encode(value.intValue(), random);
                    mn.instructions.insert(insn, replacement);
                    mn.instructions.remove(insn);
                    count++;
                }
                insn = next;
            }
        }
        return count;
    }

    private static Integer intConstant(AbstractInsnNode insn) {
        int op = insn.getOpcode();
        if (op >= Opcodes.ICONST_M1 && op <= Opcodes.ICONST_5) {
            return Integer.valueOf(op - Opcodes.ICONST_0);
        }
        if (insn instanceof IntInsnNode
                && (op == Opcodes.BIPUSH || op == Opcodes.SIPUSH)) {
            return Integer.valueOf(((IntInsnNode) insn).operand);
        }
        if (insn instanceof LdcInsnNode
                && ((LdcInsnNode) insn).cst instanceof Integer) {
            return (Integer) ((LdcInsnNode) insn).cst;
        }
        return null;
    }

    /** 栈效果等价于把 v 压入栈，但形式为 mask, operand, op */
    private static InsnList encode(int v, Random random) {
        int mask = random.nextInt();
        int mode = random.nextInt(3);
        int operand;
        int opcode;
        switch (mode) {
            case 0: // mask ^ operand = v
                operand = mask ^ v;
                opcode = Opcodes.IXOR;
                break;
            case 1: // mask + operand = v
                operand = v - mask;
                opcode = Opcodes.IADD;
                break;
            default: // mask - operand = v
                operand = mask - v;
                opcode = Opcodes.ISUB;
                break;
        }
        InsnList il = new InsnList();
        il.add(new LdcInsnNode(Integer.valueOf(mask)));
        il.add(new LdcInsnNode(Integer.valueOf(operand)));
        il.add(new InsnNode(opcode));
        return il;
    }
}
