package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * 垃圾代码注入：添加永不被外部调用的 private static 方法和 private static 字段。
 *
 * 与早期版本的区别：
 * <ul>
 *   <li><b>随机穿插</b>：垃圾方法/字段不堆叠在类成员末尾，而是逐个随机插入到
 *       真实成员之间的任意位置，成员列表层面无法按位置区分真假。</li>
 *   <li><b>模板多样化</b>：直线运算、if/else 分叉、有限 while 循环、分叉+循环
 *       嵌套、long 运算等多种形态；带跳转的模板会被后续控制流平坦化同样处理，
 *       与真实方法在结构上完全同构。</li>
 *   <li><b>互调</b>：部分垃圾方法调用同类中更早生成的 (II)I 垃圾方法，形成
 *       无环调用图，静态“被调用即有用”的判断失效。</li>
 * </ul>
 *
 * 不往现有真实方法里插任何指令；新方法自身是完整合法、可通过校验的字节码。
 */
public final class JunkCode {

    private static final int ACCESS =
            Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC;

    private JunkCode() {
    }

    public static int apply(ClassNode cn, Random random, int methodCount) {
        if (methodCount <= 0) {
            return 0;
        }
        // 接口 / 注解 / 模块信息不注入（类版本与成员规则限制多，收益低）
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION | Opcodes.ACC_MODULE)) != 0) {
            return 0;
        }
        Set<String> usedNames = new HashSet<String>();
        for (MethodNode m : cn.methods) {
            usedNames.add(m.name);
        }
        for (FieldNode f : cn.fields) {
            usedNames.add(f.name);
        }

        List<String> intIntMethods = new ArrayList<String>();
        int added = 0;
        for (int i = 0; i < methodCount; i++) {
            String name = uniqueName(usedNames, random);
            usedNames.add(name);
            MethodNode m = buildJunkMethod(cn, name, random, intIntMethods);
            // 随机插入到真实/已插入成员之间，而不是统一 append 到末尾
            int pos = cn.methods.isEmpty() ? 0 : random.nextInt(cn.methods.size() + 1);
            cn.methods.add(pos, m);
            if ("(II)I".equals(m.desc)) {
                intIntMethods.add(name);
            }
            added++;
        }

        // 少量垃圾字段，同样随机穿插，类型随机
        int fields = Math.min(methodCount, 3);
        String[] fieldDescs = { "I", "J", "Z", "Ljava/lang/Object;" };
        for (int i = 0; i < fields; i++) {
            String name = uniqueName(usedNames, random);
            usedNames.add(name);
            FieldNode f = new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC
                            | Opcodes.ACC_TRANSIENT,
                    name, fieldDescs[random.nextInt(fieldDescs.length)], null, null);
            int pos = cn.fields.isEmpty() ? 0 : random.nextInt(cn.fields.size() + 1);
            cn.fields.add(pos, f);
        }
        return added;
    }

    // ------------------------------------------------------------------
    // 真实方法环境调用注入（disperseLogic 阶段调用，无需开启屎山）
    // ------------------------------------------------------------------

    private static final int ENV_MAX_PER_METHOD = 12;
    private static final int ENV_METHOD_NODE_CAP = 14000;

    /**
     * 在类内所有真实方法（含构造器 super 后、外提合成方法）的栈空锚点上，
     * 随机插入 {@link #envIntSnippet}。每方法一个专用垃圾槽。
     * 返回插入片段总数。
     */
    public static int injectEnvIntoMethods(ClassNode cn, Random random) {
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE)) != 0) {
            return 0;
        }
        int inserted = 0;
        for (MethodNode mn : cn.methods) {
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
                continue;
            }
            try {
                inserted += injectOne(cn, mn, random);
            } catch (Throwable t) {
                continue;
            }
        }
        return inserted;
    }

    private static int injectOne(ClassNode cn, MethodNode mn, Random random)
            throws Exception {
        AbstractInsnNode[] insns = mn.instructions.toArray();
        if (insns.length >= ENV_METHOD_NODE_CAP) {
            return 0;
        }
        // 含 try-catch 的方法整体放弃：异常 handler 的 locals frame 不被
        // 方法序言支配，垃圾槽在 catch 路径是 top，片段 ILOAD 会 VerifyError
        if (mn.tryCatchBlocks != null && !mn.tryCatchBlocks.isEmpty()) {
            return 0;
        }
        int barrier = -1;
        if (mn.name.equals("<init>")) {
            boolean found = false;
            for (int i = 0; i < insns.length; i++) {
                AbstractInsnNode n = insns[i];
                if (n.getOpcode() == Opcodes.INVOKESPECIAL && n instanceof MethodInsnNode
                        && ((MethodInsnNode) n).name.equals("<init>")) {
                    MethodInsnNode min = (MethodInsnNode) n;
                    if (min.owner.equals(cn.name) || min.owner.equals(cn.superName)) {
                        barrier = i;
                        found = true;
                        break;
                    }
                }
            }
            if (!found) {
                return 0;
            }
        }

        int base = 0;
        for (AbstractInsnNode n : insns) {
            if (n instanceof VarInsnNode) {
                int op = n.getOpcode();
                int width = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                        || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                base = Math.max(base, ((VarInsnNode) n).var + width);
            } else if (n instanceof org.objectweb.asm.tree.IincInsnNode) {
                base = Math.max(base, ((org.objectweb.asm.tree.IincInsnNode) n).var + 1);
            }
        }
        int slot = base;

        // 紧边界帧分析（平坦化后方法体巨大，65535 帧每帧 ~1MB 会吃满 CPU/内存）
        Frame<BasicValue>[] frames = Analysis.basic(mn);
        if (frames == null) {
            return 0;
        }

        List<AbstractInsnNode> anchors = new ArrayList<AbstractInsnNode>();
        for (int i = 0; i < insns.length; i++) {
            if (i <= barrier) {
                continue;
            }
            AbstractInsnNode n = insns[i];
            int type = n.getType();
            if (type == AbstractInsnNode.FRAME || type == AbstractInsnNode.LABEL
                    || type == AbstractInsnNode.LINE) {
                continue;
            }
            Frame<BasicValue> f = frames[i];
            if (f != null && f.getStackSize() == 0) {
                anchors.add(n);
            }
        }
        if (anchors.isEmpty()) {
            return 0;
        }

        AbstractInsnNode prologuePoint = barrier >= 0 ? insns[barrier].getNext()
                : insns[0];
        while (prologuePoint != null) {
            int t = prologuePoint.getType();
            if (t != AbstractInsnNode.LABEL && t != AbstractInsnNode.LINE
                    && t != AbstractInsnNode.FRAME) {
                break;
            }
            prologuePoint = prologuePoint.getNext();
        }
        if (prologuePoint == null) {
            return 0;
        }

        double rate = 0.14 + random.nextDouble() * 0.22;
        List<AbstractInsnNode> picked = new ArrayList<AbstractInsnNode>();
        for (AbstractInsnNode a : anchors) {
            if (picked.size() >= ENV_MAX_PER_METHOD) {
                break;
            }
            if (random.nextDouble() < rate) {
                picked.add(a);
            }
        }
        if (picked.isEmpty()) {
            return 0;
        }
        // 序言必须先于片段插入：首个锚点可能就是 prologuePoint，后插序言
        // 会被 ASM 放到"已插片段"与锚点之间，导致片段里的 ILOAD 先于
        // 自己的 ISTORE 序言执行 -> VerifyError
        InsnList prologue = new InsnList();
        pushInt(prologue, random.nextInt(256));
        prologue.add(new VarInsnNode(Opcodes.ISTORE, slot));
        mn.instructions.insertBefore(prologuePoint, prologue);
        for (int i = picked.size() - 1; i >= 0; i--) {
            AbstractInsnNode a = picked.get(i);
            if (mn.instructions.indexOf(a) < 0) {
                continue;
            }
            mn.instructions.insertBefore(a, envIntSnippet(random, slot));
        }
        return picked.size();
    }

    /** 随机 6-10 位小写字母名（注入发生在重命名之后，名字需自己伪装）。 */
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

    private static MethodNode buildJunkMethod(ClassNode cn, String name, Random random,
                                              List<String> intIntMethods) {
        int t = random.nextInt(7);
        switch (t) {
            case 0:  return templateStraight(cn, name, random, null);
            case 1:  return templateStraight(cn, name, random,
                        intIntMethods.isEmpty() ? null
                                : intIntMethods.get(random.nextInt(intIntMethods.size())));
            case 2:  return templateBranch(name, random);
            case 3:  return templateLoop(name, random);
            case 4:  return templateBranchLoop(name, random);
            case 5:  return templateLong(name, random);
            default: return templateEnv(name, random);
        }
    }

    /**
     * private static int name(int a) {
     *   int t = &lt;环境 API 垃圾片段&gt;;
     *   return t + a;
     * }
     * 假方法也大量出现 Thread/System/Runtime 等真实外部调用，与业务方法同构。
     */
    private static MethodNode templateEnv(String name, Random random) {
        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, "(I)I", null, null);
        InsnList il = m.instructions;
        pushInt(il, random.nextInt(64));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(envIntSnippet(random, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /**
     * 栈中性"环境垃圾"片段：调用 Thread / System / Runtime / Integer /
     * StringBuilder 等真实 JDK API 取一个 int，写入 {@code slot}，再追加
     * 1-3 个算术回写。用于真实方法栈空点与假方法，提高外部调用密度，
     * 让业务调用不再被一片纯 int 算术衬托出来。
     *
     * 前置：栈空；{@code slot} 已被初始化（片段可能先 ILOAD 它）。
     * 后置：栈空；只写 {@code slot}。全部 API 无 checked 异常，
     * JDK 8 编译、8-25 可运行（getId 旧版可用，新版仅 deprecate）。
     */
    public static InsnList envIntSnippet(Random random, int slot) {
        InsnList il = new InsnList();
        // Thread 系列加权（用户点名 thread getId），其余各 1
        int pick = random.nextInt(20);
        if (pick < 5) {
            // Thread.currentThread().getId()（long → int）
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Thread", "getId", "()J", false));
            il.add(new InsnNode(Opcodes.L2I));
        } else if (pick < 8) {
            // Thread.currentThread().getName().hashCode()
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Thread", "getName", "()Ljava/lang/String;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/String", "hashCode", "()I", false));
        } else if (pick < 10) {
            // Thread.currentThread().getPriority()
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Thread", "getPriority", "()I", false));
        } else if (pick < 11) {
            // Thread.currentThread().isAlive()（boolean 当 int）
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Thread", "isAlive", "()Z", false));
        } else if (pick < 12) {
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/System", "nanoTime", "()J", false));
            il.add(new InsnNode(Opcodes.L2I));
        } else if (pick < 13) {
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/System", "currentTimeMillis", "()J", false));
            il.add(new InsnNode(Opcodes.L2I));
        } else if (pick < 14) {
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Runtime", "getRuntime", "()Ljava/lang/Runtime;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Runtime", "availableProcessors", "()I", false));
        } else if (pick < 15) {
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Runtime", "getRuntime", "()Ljava/lang/Runtime;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Runtime", "freeMemory", "()J", false));
            il.add(new InsnNode(Opcodes.L2I));
        } else if (pick < 16) {
            // Integer.bitCount(slot)
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Integer", "bitCount", "(I)I", false));
        } else if (pick < 17) {
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Integer", "numberOfLeadingZeros", "(I)I", false));
        } else if (pick < 18) {
            // Math.abs(slot)
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Math", "abs", "(I)I", false));
        } else if (pick < 19) {
            // String.valueOf(slot).length()
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/String", "valueOf", "(I)Ljava/lang/String;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/String", "length", "()I", false));
        } else {
            // new StringBuilder().append(slot).length()
            il.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuilder"));
            il.add(new InsnNode(Opcodes.DUP));
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                    "java/lang/StringBuilder", "<init>", "()V", false));
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/StringBuilder", "append",
                    "(I)Ljava/lang/StringBuilder;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/StringBuilder", "length", "()I", false));
        }
        il.add(new VarInsnNode(Opcodes.ISTORE, slot));

        int tails = 1 + random.nextInt(3);
        int[] ops = { Opcodes.IADD, Opcodes.ISUB, Opcodes.IXOR, Opcodes.IOR, Opcodes.IAND };
        for (int i = 0; i < tails; i++) {
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            if (random.nextInt(4) == 0) {
                // 自反混合：slot op slot 形式，再回写
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(random.nextBoolean() ? Opcodes.IOR : Opcodes.IAND));
            } else {
                pushInt(il, random.nextInt(4096) - 2048);
                il.add(new InsnNode(ops[random.nextInt(ops.length)]));
            }
            il.add(new VarInsnNode(Opcodes.ISTORE, slot));
        }
        return il;
    }

    /**
     * private static int name(int a, int b) {
     *   int c = (a + b) * K [+ junkFn(a,b)];
     *   return c + a;
     * }
     * 纯直线代码，无跳转。
     */
    private static MethodNode templateStraight(ClassNode cn, String name, Random random,
                                               String callee) {
        int k;
        do {
            k = random.nextInt(1024) + 1;
        } while (k == 1);
        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, "(II)I", null, null);
        InsnList il = m.instructions;
        if (callee != null) {
            il.add(new VarInsnNode(Opcodes.ILOAD, 0));
            il.add(new VarInsnNode(Opcodes.ILOAD, 1));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    cn.name, callee, "(II)I", false));
        } else {
            il.add(new VarInsnNode(Opcodes.ILOAD, 0));
            il.add(new VarInsnNode(Opcodes.ILOAD, 1));
            il.add(new InsnNode(Opcodes.IADD));
        }
        il.add(new LdcInsnNode(Integer.valueOf(k)));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /**
     * private static int name(int a) {
     *   if (a > K) return a * M; else return a + D;
     * }
     * 含一个条件跳转，后续会被平坦化。
     */
    private static MethodNode templateBranch(String name, Random random) {
        int k = random.nextInt(1024) - 512;
        int mm = random.nextInt(16) + 2;
        int d = random.nextInt(1024) - 512;
        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, "(I)I", null, null);
        InsnList il = m.instructions;
        LabelNode els = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        pushInt(il, k);
        il.add(new JumpInsnNode(Opcodes.IF_ICMPLE, els));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        pushInt(il, mm);
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.IRETURN));
        il.add(els);
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        pushInt(il, d);
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /**
     * private static int name(int a, int b) {
     *   int s = 0;
     *   for (int i = a &amp; 7; i > 0; i--) s += b;   // 有界 0..7 次
     *   return s + a;
     * }
     */
    private static MethodNode templateLoop(String name, Random random) {
        int mask = new int[] { 3, 7, 15 }[random.nextInt(3)];
        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, "(II)I", null, null);
        InsnList il = m.instructions;
        LabelNode top = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        pushInt(il, mask);
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(top);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new JumpInsnNode(Opcodes.IFLE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 2));
        il.add(new org.objectweb.asm.tree.IincInsnNode(3, -1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /**
     * private static int name(int a, int b, int c) {
     *   int r = a ^ c;
     *   if (b > 0) r += b * 3; else r -= b;
     *   for (int k = r &amp; 3; k > 0; k--) r = (r << 1) + 1;
     *   return r ^ a;
     * }
     * 分叉 + 循环嵌套。
     */
    private static MethodNode templateBranchLoop(String name, Random random) {
        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, "(III)I", null, null);
        InsnList il = m.instructions;
        LabelNode els = new LabelNode();
        LabelNode join = new LabelNode();
        LabelNode top = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new VarInsnNode(Opcodes.ILOAD, 2));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new JumpInsnNode(Opcodes.IFLE, els));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ICONST_3));
        il.add(new InsnNode(Opcodes.IMUL));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(new JumpInsnNode(Opcodes.GOTO, join));
        il.add(els);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 1));
        il.add(new InsnNode(Opcodes.ISUB));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(join);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.ICONST_3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new VarInsnNode(Opcodes.ISTORE, 4));
        il.add(top);
        il.add(new VarInsnNode(Opcodes.ILOAD, 4));
        il.add(new JumpInsnNode(Opcodes.IFLE, end));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.ISHL));
        il.add(new InsnNode(Opcodes.ICONST_1));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(new org.objectweb.asm.tree.IincInsnNode(4, -1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new VarInsnNode(Opcodes.ILOAD, 0));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    /**
     * private static long name(long a) {
     *   long s = a;
     *   for (int i = 0; i &lt; 4; i++) s = s * 31L + i;
     *   return s ^ 0x55L;
     * }
     */
    private static MethodNode templateLong(String name, Random random) {
        long mul = new long[] { 31L, 33L, 65599L, 131L }[random.nextInt(4)];
        long xor = random.nextLong();
        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, "(J)J", null, null);
        InsnList il = m.instructions;
        LabelNode top = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(new VarInsnNode(Opcodes.LLOAD, 0));
        il.add(new VarInsnNode(Opcodes.LSTORE, 1));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, 3));
        il.add(top);
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.ICONST_4));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.LLOAD, 1));
        il.add(new LdcInsnNode(Long.valueOf(mul)));
        il.add(new InsnNode(Opcodes.LMUL));
        il.add(new VarInsnNode(Opcodes.ILOAD, 3));
        il.add(new InsnNode(Opcodes.I2L));
        il.add(new InsnNode(Opcodes.LADD));
        il.add(new VarInsnNode(Opcodes.LSTORE, 1));
        il.add(new org.objectweb.asm.tree.IincInsnNode(3, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.LLOAD, 1));
        il.add(new LdcInsnNode(Long.valueOf(xor)));
        il.add(new InsnNode(Opcodes.LXOR));
        il.add(new InsnNode(Opcodes.LRETURN));
        return m;
    }

    private static void pushInt(InsnList il, int v) {
        if (v >= -1 && v <= 5) {
            il.add(new InsnNode(Opcodes.ICONST_0 + v));
        } else if (v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE) {
            il.add(new org.objectweb.asm.tree.IntInsnNode(Opcodes.BIPUSH, v));
        } else if (v >= Short.MIN_VALUE && v <= Short.MAX_VALUE) {
            il.add(new org.objectweb.asm.tree.IntInsnNode(Opcodes.SIPUSH, v));
        } else {
            il.add(new LdcInsnNode(Integer.valueOf(v)));
        }
    }
}
