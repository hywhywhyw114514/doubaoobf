package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;

import java.util.Random;

/**
 * 字符串加密。
 *
 * 原理：LDC "xxx" 改为 LDC 密文 + INVOKESTATIC 解密方法。
 * 密文全部由 U+0100..U+01FF 的安全字符构成（绝不可能落入代理对区间），
 * 每个原始 UTF-16 字符拆成高/低两字节再异或单类密钥，保证：
 *   1) 常量池 modified-UTF8 编码一定合法；
 *   2) 解密是纯数组运算，不碰任何局部变量，校验器必然通过。
 */
public final class StringEncryption {

    private StringEncryption() {
    }

    public static int apply(ClassNode cn, Random random) {
        boolean isInterface = (cn.access & Opcodes.ACC_INTERFACE) != 0;
        // 1.8 之前的接口不允许有带代码的静态方法
        if (isInterface && cn.version < Opcodes.V1_8) {
            return 0;
        }
        int key = 1 + random.nextInt(0xFFFE);
        String decryptName = uniqueMethodName(cn, "d");

        int count = 0;
        for (MethodNode mn : cn.methods) {
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            AbstractInsnNode insn = mn.instructions.getFirst();
            while (insn != null) {
                AbstractInsnNode next = insn.getNext();
                if (insn instanceof LdcInsnNode) {
                    Object cst = ((LdcInsnNode) insn).cst;
                    if (cst instanceof String) {
                        String encrypted = encrypt((String) cst, key);
                        InsnList replace = new InsnList();
                        replace.add(new LdcInsnNode(encrypted));
                        replace.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                                cn.name, decryptName,
                                "(Ljava/lang/String;)Ljava/lang/String;", isInterface));
                        mn.instructions.insert(insn, replace);
                        mn.instructions.remove(insn);
                        count++;
                    }
                }
                insn = next;
            }
        }
        if (count > 0) {
            cn.methods.add(buildDecryptor(decryptName, key, isInterface));
        }
        return count;
    }

    private static String uniqueMethodName(ClassNode cn, String prefix) {
        String name;
        int i = 0;
        do {
            name = prefix + (i++ == 0 ? "" : Integer.toString(i));
        } while (existsMethod(cn, name));
        return name;
    }

    private static boolean existsMethod(ClassNode cn, String name) {
        for (MethodNode m : cn.methods) {
            if (m.name.equals(name)) {
                return true;
            }
        }
        return false;
    }

    private static String encrypt(String s, int key) {
        StringBuilder sb = new StringBuilder(s.length() * 2);
        for (int i = 0; i < s.length(); i++) {
            int v = s.charAt(i) ^ key;
            sb.append((char) (0x100 + ((v >> 8) & 0xFF)));
            sb.append((char) (0x100 + (v & 0xFF)));
        }
        return sb.toString();
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

    /**
     * private static String d(String meta) {
     *   char[] chars = new char[meta.length() / 2];
     *   for (int i = 0; i < chars.length; i++) {
     *     int hi = meta.charAt(2*i) - 256;
     *     int lo = meta.charAt(2*i+1) - 256;
     *     chars[i] = (char) (((hi << 8) | lo) ^ KEY);
     *   }
     *   return new String(chars);
     * }
     */
    private static MethodNode buildDecryptor(String name, int key, boolean isInterface) {
        MethodNode d = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                name, "(Ljava/lang/String;)Ljava/lang/String;", null, null);
        InsnList il = d.instructions;

        LabelNode loop = new LabelNode();
        LabelNode end = new LabelNode();

        // char[] chars = new char[meta.length() / 2]
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/String", "length", "()I", false));
        il.add(new InsnNode(Opcodes.ICONST_2));
        il.add(new InsnNode(Opcodes.IDIV));
        il.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_CHAR));
        il.add(new VarInsnNode(Opcodes.ASTORE, 1));
        // int i = 0
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));

        il.add(loop);
        // i < chars.length
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new InsnNode(Opcodes.ARRAYLENGTH));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));

        // chars[i] = (char)(...)
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        // hi
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.ISHL));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/String", "charAt", "(I)C", false));
        pushInt(il, 0x100);
        il.add(new InsnNode(Opcodes.ISUB));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        // lo
        il.add(new VarInsnNode(Opcodes.ALOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.ISHL));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/String", "charAt", "(I)C", false));
        pushInt(il, 0x100);
        il.add(new InsnNode(Opcodes.ISUB));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        pushInt(il, 8);
        il.add(new InsnNode(Opcodes.ISHL));
        il.add(new InsnNode(Opcodes.IOR));
        pushInt(il, key);
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new InsnNode(Opcodes.CASTORE));

        il.add(new org.objectweb.asm.tree.IincInsnNode(2, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, loop));

        il.add(end);
        il.add(new TypeInsnNode(Opcodes.NEW, "java/lang/String"));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new VarInsnNode(Opcodes.ALOAD, 1));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/String", "<init>", "([C)V", false));
        il.add(new InsnNode(Opcodes.ARETURN));
        return d;
    }
}
