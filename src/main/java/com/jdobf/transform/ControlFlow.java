package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IincInsnNode;
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
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * 控制流混淆：在方法内多个栈空安全点随机插入形态各异的不透明谓词。
 *
 * 与早期"门口三连 x^x + throw null"固定模板不同，每个守卫的每一部分都
 * 在每构建随机抽取，无法用一条特征规则（如"删除两个相同 LDC 后的 IXOR
 * 比较"）通解：
 * <ul>
 *   <li><b>插入位置</b>：数据流分析出的全部栈空锚点中随机选点，守卫分散
 *       在方法体各处，不再堆在入口；构造器严格在 super/this 之后；</li>
 *   <li><b>恒等表达式</b>：8 种模板（LDC/垃圾槽混合的 XOR/SUB/乘 0/
 *       取负相加/多层抵消），随机产出恒 0 或恒 1；</li>
 *   <li><b>分支结构</b>：真路 fall-through 跨过死块，或经 GOTO 到达，
 *       IFEQ/IFNE 极性随机翻转；</li>
 *   <li><b>死块</b>：抛 NPE（null）、new 六种 RuntimeException 之一、
 *       void 方法的假 return，三种随机；</li>
 *   <li>每个方法分配一个垃圾 int 槽（序言随机常量初始化），谓词可引用它，
 *       使反编译结果里出现"真实变量参与"的比较。</li>
 * </ul>
 * 所有 StackMapFrame 由 ClassWriter.COMPUTE_FRAMES 重新计算。
 */
public final class ControlFlow {

    private static final String[] FAKE_EXCEPTIONS = {
            "java/lang/RuntimeException",
            "java/lang/IllegalStateException",
            "java/lang/ArithmeticException",
            "java/lang/IllegalArgumentException",
            "java/lang/NullPointerException",
            "java/lang/NumberFormatException",
            "java/lang/IndexOutOfBoundsException",
            "java/lang/UnsupportedOperationException",
    };

    private ControlFlow() {
    }

    public static int apply(ClassNode cn, Random random, int passes,
                            InterClassWeaver.Network network) {
        if (passes <= 0) {
            return 0;
        }
        int count = 0;
        for (MethodNode mn : cn.methods) {
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
                continue;
            }
            try {
                count += guardMethod(cn, mn, random, passes, network);
            } catch (Throwable t) {
                // 单方法分析失败则跳过，保持原样
                continue;
            }
        }
        return count;
    }

    private static int guardMethod(ClassNode cn, MethodNode mn, Random random, int passes,
                                   InterClassWeaver.Network network)
            throws Exception {
        AbstractInsnNode[] insns = mn.instructions.toArray();
        boolean isInit = mn.name.equals("<init>");

        // <clinit> 不使用跨类网络谓词：静态初始化期触发中继类初始化会引入
        // 类初始化顺序耦合；保留旧的类内谓词即可
        boolean useNetwork = network != null && !mn.name.equals("<clinit>");

        // 含 try-catch / synchronized（隐式异常表）的方法改用 trySafe 模式：
        // 不分配方法级垃圾槽、不插序言（handler 帧的 locals 不被序言支配），
        // 谓词全部为纯栈常量恒等式，栈空锚点上自闭合，任何帧下都可验证
        boolean trySafe = mn.tryCatchBlocks != null && !mn.tryCatchBlocks.isEmpty();
        if (trySafe) {
            useNetwork = false;
        }

        int barrier = -1;
        if (isInit) {
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

        int junkSlot;
        if (trySafe) {
            // 纯栈谓词模式不需要任何局部槽
            junkSlot = -1;
        } else {
            // 垃圾槽：方法实际使用过的最大槽位之上
            int base = 0;
            for (AbstractInsnNode n : insns) {
                if (n instanceof VarInsnNode) {
                    int op = n.getOpcode();
                    int width = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                            || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                    base = Math.max(base, ((VarInsnNode) n).var + width);
                } else if (n instanceof IincInsnNode) {
                    base = Math.max(base, ((IincInsnNode) n).var + 1);
                }
            }
            junkSlot = base;
        }

        // 紧边界帧分析（平坦化后方法体巨大，65535 帧每帧 ~1MB 会吃满 CPU/内存）
        Frame<BasicValue>[] frames = Analysis.basic(mn);
        if (frames == null) {
            return 0;
        }

        List<AbstractInsnNode> anchors = new ArrayList<AbstractInsnNode>();
        // 锚点 -> 该帧上一个真实活动的 int 业务槽（供业务数据消费型谓词使用）
        java.util.Map<AbstractInsnNode, Integer> bizSlots =
                new java.util.IdentityHashMap<AbstractInsnNode, Integer>();
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
                if (useNetwork) {
                    List<Integer> intSlots = new ArrayList<Integer>();
                    for (int s = 0; s < Math.min(f.getLocals(), junkSlot); s++) {
                        if (f.getLocal(s) == BasicValue.INT_VALUE) {
                            intSlots.add(Integer.valueOf(s));
                        }
                    }
                    if (!intSlots.isEmpty()) {
                        Collections.shuffle(intSlots, random);
                        bizSlots.put(n, intSlots.get(0));
                    }
                }
            }
        }
        if (anchors.isEmpty()) {
            return 0;
        }

        if (!trySafe) {
            // 垃圾槽序言（插在方法首指令 / super 后首指令之前）
            AbstractInsnNode prologuePoint = barrier >= 0 ? insns[barrier].getNext()
                    : insns[0];
            while (prologuePoint != null && isPseudo(prologuePoint)) {
                prologuePoint = prologuePoint.getNext();
            }
            if (prologuePoint == null) {
                return 0;
            }
            InsnList prologue = new InsnList();
            int seed = random.nextInt(256) + 1;
            pushInt(prologue, seed);
            prologue.add(new VarInsnNode(Opcodes.ISTORE, junkSlot));
            if (useNetwork) {
                // 多态谓词用 junkSlot+1 做临时变量，先定值；再 sow 保证
                // 本线程调用 mark0/mark1 时 R0 的 ThreadLocal 已非空
                pushInt(prologue, random.nextInt(256) + 1);
                prologue.add(new VarInsnNode(Opcodes.ISTORE, junkSlot + 1));
                prologue.add(new VarInsnNode(Opcodes.ILOAD, junkSlot));
                prologue.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        network.r0, network.mSow, "(I)V", false));
            }
            mn.instructions.insertBefore(prologuePoint, prologue);
        }

        // 随机选点（不重复），倒序插入
        Collections.shuffle(anchors, random);
        // trySafe 方法不能平坦化（异常表跨 case 不连续），谓词是其唯一控制流
        // 保护：全部栈空锚点插满，密度高于普通方法的 passes 抽样
        int want = trySafe ? anchors.size() : Math.min(passes, anchors.size());
        List<AbstractInsnNode> picked = new ArrayList<AbstractInsnNode>(anchors.subList(0, want));
        boolean voidMethod = Type.getMethodType(mn.desc).getReturnType().getSort() == Type.VOID;
        for (int i = picked.size() - 1; i >= 0; i--) {
            AbstractInsnNode anchor = picked.get(i);
            if (mn.instructions.indexOf(anchor) < 0) {
                continue;
            }
            Integer biz = bizSlots.get(anchor);
            int bizSlot = biz == null ? -1 : biz.intValue();
            mn.instructions.insertBefore(anchor,
                    buildGuard(random, junkSlot, voidMethod,
                            useNetwork ? network : null, bizSlot, trySafe));
        }
        return want;
    }

    // ------------------------------------------------------------------
    // 守卫生成
    // ------------------------------------------------------------------

    private static boolean isPseudo(AbstractInsnNode n) {
        int t = n.getType();
        return t == AbstractInsnNode.LABEL || t == AbstractInsnNode.LINE
                || t == AbstractInsnNode.FRAME;
    }

    private static InsnList buildGuard(Random random, int junkSlot, boolean voidMethod,
                                       InterClassWeaver.Network network, int bizSlot,
                                       boolean trySafe) {
        LabelNode real = new LabelNode();
        LabelNode dead = new LabelNode();
        boolean wantOne = random.nextBoolean();
        boolean gotoForm = random.nextBoolean();

        InsnList il = new InsnList();
        if (trySafe) {
            // try/catch/synchronized 方法：纯栈常量恒等谓词，不触碰任何局部
            // 槽（handler 帧下也可验证），形态仍逐守卫随机；60% 概率再前置
            // 1-2 段栈平衡噪声运算，拉开守卫体积与形态差异
            if (random.nextInt(100) < 60) {
                int segs = 1 + random.nextInt(2);
                for (int s = 0; s < segs; s++) {
                    emitStackJunk(il, random);
                }
            }
            emitConstantCond(il, random, wantOne);
        } else if (network != null && bizSlot >= 0 && random.nextInt(100) < 35) {
            network.emitBusinessZero(il, random, bizSlot, wantOne);
        } else if (network != null && random.nextInt(100) < 82) {
            network.emitOpaqueInt(il, random, junkSlot, wantOne);
        } else {
            emitCond(il, random, junkSlot, wantOne);
        }

        if (gotoForm) {
            // F2：cond; <假时跳进 dead>; GOTO real; dead: 死块; real: 原指令
            il.add(new JumpInsnNode(wantOne ? Opcodes.IFEQ : Opcodes.IFNE, dead));
            il.add(new JumpInsnNode(Opcodes.GOTO, real));
            il.add(dead);
            appendDead(il, random, voidMethod);
            il.add(real);
        } else {
            // F1：cond; <真时跳进 real>; dead: 死块; real: 原指令
            // 假路 fall-through 进入终止型死块
            il.add(new JumpInsnNode(wantOne ? Opcodes.IFNE : Opcodes.IFEQ, real));
            il.add(dead);
            appendDead(il, random, voidMethod);
            il.add(real);
        }
        return il;
    }

    /** 输出一段终止型死块（调用方保证前置标签已就位）。供同包交织层复用。 */
    static void appendDead(InsnList il, Random random, boolean voidMethod) {
        int kind = random.nextInt(voidMethod ? 3 : 2);
        switch (kind) {
            case 0:
                il.add(new InsnNode(Opcodes.ACONST_NULL));
                il.add(new InsnNode(Opcodes.ATHROW));
                break;
            case 1: {
                String ex = FAKE_EXCEPTIONS[random.nextInt(FAKE_EXCEPTIONS.length)];
                il.add(new TypeInsnNode(Opcodes.NEW, ex));
                il.add(new InsnNode(Opcodes.DUP));
                il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                        ex, "<init>", "()V", false));
                il.add(new InsnNode(Opcodes.ATHROW));
                break;
            }
            default:
                // void / <init>：假 return，验证器下合法（落在死分支中）
                il.add(new InsnNode(Opcodes.RETURN));
                break;
        }
    }

    /**
     * 向栈顶压入恒等 int：wantOne 为真时值恒为 1，否则恒为 0。
     * 8 种模板，操作数混合随机 LDC 与方法垃圾槽。
     */
    private static void emitCond(InsnList il, Random random, int slot, boolean wantOne) {
        int t = random.nextInt(8);
        int r = random.nextInt();
        int a = random.nextInt();
        int b = random.nextInt();
        switch (t) {
            case 0: // r ^ r
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new InsnNode(Opcodes.IXOR));
                break;
            case 1: // r - r
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new LdcInsnNode(Integer.valueOf(r)));
                il.add(new InsnNode(Opcodes.ISUB));
                break;
            case 2: // s * 0
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.ICONST_0));
                il.add(new InsnNode(Opcodes.IMUL));
                break;
            case 3: // s ^ s
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.IXOR));
                break;
            case 4: // s - s
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.ISUB));
                break;
            case 5: // -s + s
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.INEG));
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.IADD));
                break;
            case 6: // a ^ (a ^ (b ^ b))
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.IXOR));
                break;
            default: // s * -1 + s
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.ICONST_M1));
                il.add(new InsnNode(Opcodes.IMUL));
                il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                il.add(new InsnNode(Opcodes.IADD));
                break;
        }
        if (wantOne) {
            // 0 -> 1，两种随机尾变换
            if (random.nextBoolean()) {
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IADD));
            } else {
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IXOR));
            }
        }
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

    /**
     * 纯栈噪声片段（trySafe 专用）：随机常量间的 int 运算，以 POP 收尾，
     * 栈深 ≤3、栈空进出，不读不写局部槽，可落在任何栈空锚点（含 handler 帧）。
     */
    private static void emitStackJunk(InsnList il, Random random) {
        int a = random.nextInt();
        int b = random.nextInt();
        int c = random.nextInt();
        switch (random.nextInt(4)) {
            case 0:
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IADD));
                il.add(new InsnNode(Opcodes.POP));
                break;
            case 1:
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IMUL));
                il.add(new LdcInsnNode(Integer.valueOf(c)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.POP));
                break;
            case 2:
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new InsnNode(Opcodes.INEG));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.ISUB));
                il.add(new InsnNode(Opcodes.POP));
                break;
            default:
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IAND));
                il.add(new LdcInsnNode(Integer.valueOf(c)));
                il.add(new InsnNode(Opcodes.IOR));
                il.add(new InsnNode(Opcodes.POP));
                break;
        }
    }

    /**
     * 纯栈常量恒等谓词（trySafe 专用）：仅使用随机 LDC 常量与栈上 int 运算，
     * 不读不写任何局部变量槽，栈空锚点上自闭合，因此插在 try 区间内部或
     * catch handler 帧上都合法。栈深 ≤4。
     */
    private static void emitConstantCond(InsnList il, Random random, boolean wantOne) {
        int t = random.nextInt(8);
        int a = random.nextInt();
        int b = random.nextInt();
        int c = random.nextInt();
        switch (t) {
            case 0: // a ^ a
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new InsnNode(Opcodes.IXOR));
                break;
            case 1: // a - a
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new InsnNode(Opcodes.ISUB));
                break;
            case 2: // c * 0
                il.add(new LdcInsnNode(Integer.valueOf(c)));
                il.add(new InsnNode(Opcodes.ICONST_0));
                il.add(new InsnNode(Opcodes.IMUL));
                break;
            case 3: // c & 0
                il.add(new LdcInsnNode(Integer.valueOf(c)));
                il.add(new InsnNode(Opcodes.ICONST_0));
                il.add(new InsnNode(Opcodes.IAND));
                break;
            case 4: // (a ^ b) ^ (a ^ b)
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.IXOR));
                break;
            case 5: // (a | -1) + 1 == 0
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new InsnNode(Opcodes.ICONST_M1));
                il.add(new InsnNode(Opcodes.IOR));
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IADD));
                break;
            case 6: // (b - b) * a
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.ISUB));
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new InsnNode(Opcodes.IMUL));
                break;
            default: // ((a ^ a) ^ (b ^ b)) ^ (c ^ c)，三对自异或逐级抵消为 0
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new LdcInsnNode(Integer.valueOf(a)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new LdcInsnNode(Integer.valueOf(b)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new LdcInsnNode(Integer.valueOf(c)));
                il.add(new LdcInsnNode(Integer.valueOf(c)));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.IXOR));
                break;
        }
        if (wantOne) {
            if (random.nextBoolean()) {
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IOR));
            } else {
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IADD));
            }
        }
    }
}
