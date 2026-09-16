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
import org.objectweb.asm.tree.VarInsnNode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * 数据流强绑定（Data-Flow Binding）。
 *
 * 早期所有混淆层（垃圾片段、环境调用、不透明谓词）都<b>平行</b>于业务逻辑：
 * 删掉它们，业务变量的值一个 bit 都不变，污点/AST 过滤器可一键剥光。
 * 本层直接改写业务字节码本身，让业务值的产出必须经过跨类网络，三类手段：
 *
 * <ol>
 *   <li><b>业务常量动态解密</b>：业务 int 常量 v 在使用点不再以明文压栈，
 *       而是 {@code LDC(v^G0^S); oc(cipher, idx)}。oc 内部
 *       {@code x ^ tbase() ^ tidX() ^ rev(saltTable[idx])}：G0/S 的明文只
 *       存在于别的中继类里（全链加密态），线程 id 在两个类间对消。
 *       返回值就是业务值——删掉调用，栈上少一个 int，字节码直接失效。</li>
 *   <li><b>MBA 指令代换 + 跨类算术路由</b>：IADD/ISUB/IOR/INEG 原地改写为
 *       混合布尔算术（{@code a+b=(a^b)+2*(a&b)} 等），IMUL 与部分加减
 *       经 {@code seal(a)} 全链编码后送末类 qAdd/qMul 解码运算，操作数在
 *       跨类调用间以编码态存在。</li>
 *   <li><b>int 局部变量全程加密</b>：选中的非参数 int 槽以
 *       {@code v ^ (G0 ^ slotSalt)} 密文态常驻局部变量表：每条 ISTORE 前
 *       加密、每条 ILOAD 后解密、IINC 改为"解密-加-加密"。调试器/内存转储
 *       看到的槽位是乱码；密钥含运行时线程因子且工作密钥在别的类组装。</li>
 * </ol>
 *
 * 语义安全：全部变换 int 环内严格恒等（含 MIN_VALUE 溢出边界）；不引入分支
 * 与新 try 区；常量解密/算术代换在 try-catch 方法与构造器 super 之后也允许
 * （替换序列是直线、栈中性、def-before-use 临时槽）；局部加密要求无
 * try-catch、非 &lt;init&gt;/&lt;clinit&gt;、非平坦化产物（含 LOOKUPSWITCH
 * 的方法状态槽不可加密）；槽位类型纯 int 且不与 cat2 槽重叠。JDK8-25。
 */
public final class DataFlowBinder {

    private DataFlowBinder() {
    }

    private static final int METHOD_NODE_CAP = 14000;
    private static final int CONST_RATE = 36;
    private static final int CONST_CAP = 26;
    private static final int MBA_RATE = 48;
    private static final int MBA_CAP = 24;
    private static final int LOCAL_RATE = 55;
    private static final int LOCAL_CAP = 2;

    /**
     * 对类内全部可变换方法做数据流绑定。返回 [常量解密数, MBA 代换数, 加密槽数]。
     */
    public static int[] bind(ClassNode cn, InterClassWeaver.Network net,
                             Random upstream) {
        int[] sum = new int[3];
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE)) != 0) {
            return sum;
        }
        for (MethodNode mn : cn.methods) {
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
                continue;
            }
            if (mn.name.equals("<clinit>")) {
                continue;
            }
            try {
                // 与 weaveOne 相同的每方法独立短流，规避主管线 LCG 深偏移相关
                Random r = new Random(upstream.nextLong() ^ 0x9E3779B97F4A7C15L);
                int[] got = bindOne(cn, mn, net, r);
                sum[0] += got[0];
                sum[1] += got[1];
                sum[2] += got[2];
            } catch (Throwable t) {
                // 单方法失败保持原样，由外层类级回退兜底
                continue;
            }
        }
        return sum;
    }

    private static int[] bindOne(ClassNode cn, MethodNode mn,
                                  InterClassWeaver.Network net, Random r) {
        int[] got = new int[3];
        AbstractInsnNode[] insns = mn.instructions.toArray();
        if (insns.length >= METHOD_NODE_CAP) {
            return got;
        }

        int barrier = -1;
        if (mn.name.equals("<init>")) {
            for (int i = 0; i < insns.length; i++) {
                AbstractInsnNode n = insns[i];
                if (n.getOpcode() == Opcodes.INVOKESPECIAL && n instanceof MethodInsnNode
                        && ((MethodInsnNode) n).name.equals("<init>")) {
                    MethodInsnNode min = (MethodInsnNode) n;
                    if (min.owner.equals(cn.name) || min.owner.equals(cn.superName)) {
                        barrier = i;
                        break;
                    }
                }
            }
            if (barrier < 0) {
                return got;
            }
        }
        boolean hasTry = mn.tryCatchBlocks != null && !mn.tryCatchBlocks.isEmpty();
        boolean isInit = mn.name.equals("<init>");

        // 实际使用过的最大槽位；scratch/scratch+1 做 MBA 临时槽
        int observed = 0;
        boolean hasSwitch = false;
        for (AbstractInsnNode n : insns) {
            if (n instanceof VarInsnNode) {
                int op = n.getOpcode();
                int width = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                        || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                observed = Math.max(observed, ((VarInsnNode) n).var + width);
            } else if (n instanceof IincInsnNode) {
                observed = Math.max(observed, ((IincInsnNode) n).var + 1);
            }
            int op = n.getOpcode();
            if (op == Opcodes.LOOKUPSWITCH || op == Opcodes.TABLESWITCH) {
                hasSwitch = true;
            }
        }
        int scratch = Math.max(observed, 1);

        // ---- 收集原始指令中的常量与算术（snapshot：新插入指令绝不二次处理）----
        List<AbstractInsnNode> consts = new ArrayList<AbstractInsnNode>();
        List<AbstractInsnNode> arith = new ArrayList<AbstractInsnNode>();
        for (int i = 0; i < insns.length; i++) {
            if (i <= barrier) {
                continue;
            }
            AbstractInsnNode n = insns[i];
            if (intConstant(n) != null) {
                consts.add(n);
            } else {
                int op = n.getOpcode();
                if (op == Opcodes.IADD || op == Opcodes.ISUB || op == Opcodes.IMUL
                        || op == Opcodes.IOR || op == Opcodes.INEG) {
                    arith.add(n);
                }
            }
        }
        Collections.shuffle(consts, r);
        Collections.shuffle(arith, r);

        // ---- 层 1a：业务常量 -> 动态解密 ----
        int constBudget = Math.min(CONST_CAP,
                Math.max(1, consts.size() * CONST_RATE / 100));
        int constDone = 0;
        for (AbstractInsnNode n : consts) {
            if (constDone >= constBudget) {
                break;
            }
            if (mn.instructions.indexOf(n) < 0) {
                continue;
            }
            Integer v = intConstant(n);
            if (v == null) {
                continue;
            }
            int k = r.nextInt(net.ocOwners.length);
            int si = r.nextInt(net.ocSalts[k].length);
            int cipher = v.intValue() ^ net.g0 ^ net.ocSalts[k][si];
            InsnList rep = new InsnList();
            rep.add(new LdcInsnNode(Integer.valueOf(cipher)));
            pushInt(rep, si);
            rep.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    net.ocOwners[k], net.ocMethods[k], "(II)I", false));
            mn.instructions.insertBefore(n, rep);
            mn.instructions.remove(n);
            constDone++;
        }
        got[0] = constDone;

        // ---- 层 1b：MBA 代换 / 跨类算术路由 ----
        int mbaBudget = Math.min(MBA_CAP,
                Math.max(1, arith.size() * MBA_RATE / 100));
        int mbaDone = 0;
        for (AbstractInsnNode n : arith) {
            if (mbaDone >= mbaBudget) {
                break;
            }
            if (mn.instructions.indexOf(n) < 0) {
                continue;
            }
            InsnList rep = buildArithmetic(n.getOpcode(), r, scratch, net);
            if (rep == null) {
                continue;
            }
            mn.instructions.insertBefore(n, rep);
            mn.instructions.remove(n);
            mbaDone++;
        }
        got[1] = mbaDone;

        // ---- 层 2：int 局部变量全程加密 ----
        if (!hasTry && !isInit && !hasSwitch) {
            got[2] = encryptLocals(mn, insns, scratch, net, r);
        }
        return got;
    }

    /**
     * 构造一条替换二元/一元 int 算术指令的指令序列。
     * 二元输入栈 {@code ...,a,b}：先 ISTORE 临时槽，再按模板重建；
     * 一元 INEG 输入 {@code ...,a}，只用 scratch。
     */
    private static InsnList buildArithmetic(int op, Random r, int scratch,
                                             InterClassWeaver.Network net) {
        InsnList il = new InsnList();
        int a = scratch;
        int b = scratch + 1;
        boolean unary = op == Opcodes.INEG;
        if (unary) {
            // 消耗 a
            il.add(new VarInsnNode(Opcodes.ISTORE, a));
        } else {
            // 栈 ...,a,b：先弹 b 再弹 a
            il.add(new VarInsnNode(Opcodes.ISTORE, b));
            il.add(new VarInsnNode(Opcodes.ISTORE, a));
        }
        switch (op) {
            case Opcodes.IADD:
                if (r.nextInt(100) < 32) {
                    // seal(a) 跨类编码后送末类 qAdd 解码相加
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            net.sealOwner, net.mSeal, "(I)I", false));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            net.qOwner, net.qAdd, "(II)I", false));
                } else if (r.nextBoolean()) {
                    // (a ^ b) + 2 * (a & b)
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new InsnNode(Opcodes.IXOR));
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new InsnNode(Opcodes.IAND));
                    il.add(new InsnNode(Opcodes.ICONST_1));
                    il.add(new InsnNode(Opcodes.ISHL));
                    il.add(new InsnNode(Opcodes.IADD));
                } else {
                    // (a | b) + (a & b)
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new InsnNode(Opcodes.IOR));
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new InsnNode(Opcodes.IAND));
                    il.add(new InsnNode(Opcodes.IADD));
                }
                break;
            case Opcodes.ISUB:
                if (r.nextInt(100) < 32) {
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            net.sealOwner, net.mSeal, "(I)I", false));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            net.qOwner, net.qSub, "(II)I", false));
                } else {
                    // (a ^ b) - 2 * (~a & b)
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new InsnNode(Opcodes.IXOR));
                    il.add(new VarInsnNode(Opcodes.ILOAD, a));
                    il.add(new InsnNode(Opcodes.ICONST_M1));
                    il.add(new InsnNode(Opcodes.IXOR));
                    il.add(new VarInsnNode(Opcodes.ILOAD, b));
                    il.add(new InsnNode(Opcodes.IAND));
                    il.add(new InsnNode(Opcodes.ICONST_1));
                    il.add(new InsnNode(Opcodes.ISHL));
                    il.add(new InsnNode(Opcodes.ISUB));
                }
                break;
            case Opcodes.IMUL:
                // seal(a) -> qMul 解码相乘；32 位溢出语义与 IMUL 完全一致
                il.add(new VarInsnNode(Opcodes.ILOAD, a));
                il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        net.sealOwner, net.mSeal, "(I)I", false));
                il.add(new VarInsnNode(Opcodes.ILOAD, b));
                il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        net.qOwner, net.qMul, "(II)I", false));
                break;
            case Opcodes.IOR:
                // a | b = (a ^ b) + (a & b)
                il.add(new VarInsnNode(Opcodes.ILOAD, a));
                il.add(new VarInsnNode(Opcodes.ILOAD, b));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new VarInsnNode(Opcodes.ILOAD, a));
                il.add(new VarInsnNode(Opcodes.ILOAD, b));
                il.add(new InsnNode(Opcodes.IAND));
                il.add(new InsnNode(Opcodes.IADD));
                break;
            default: // INEG：-a = ~a + 1（MIN_VALUE 边界成立）
                il.add(new VarInsnNode(Opcodes.ILOAD, a));
                il.add(new InsnNode(Opcodes.ICONST_M1));
                il.add(new InsnNode(Opcodes.IXOR));
                il.add(new InsnNode(Opcodes.ICONST_1));
                il.add(new InsnNode(Opcodes.IADD));
                break;
        }
        return il;
    }

    /**
     * 选择 1-2 个非参数纯 int 槽全程加密。
     * 不变量：槽中任何时刻都是密文（所有 ISTORE 前加密、所有 ILOAD 后解密、
     * IINC 改造），异常路径同样保持，故无需帧级支配分析；只要求槽位类型
     * 生命周期内始终是 int 且不与 long/double 槽重叠。
     */
    private static int encryptLocals(MethodNode mn, AbstractInsnNode[] insns,
                                      int scratch, InterClassWeaver.Network net,
                                      Random r) {
        Type[] args = Type.getArgumentTypes(mn.desc);
        int argSlots = (mn.access & Opcodes.ACC_STATIC) != 0 ? 0 : 1;
        for (Type t : args) {
            argSlots += t.getSize();
        }

        int[] kind = new int[Math.max(scratch, 1)]; // 0=未知 1=int 2=其它
        boolean[] cat2 = new boolean[kind.length + 2];
        for (AbstractInsnNode n : insns) {
            if (n instanceof VarInsnNode) {
                VarInsnNode vn = (VarInsnNode) n;
                int op = vn.getOpcode();
                int k;
                boolean wide = false;
                if (op == Opcodes.ILOAD || op == Opcodes.ISTORE) {
                    k = 1;
                } else if (op == Opcodes.LLOAD || op == Opcodes.LSTORE
                        || op == Opcodes.DLOAD || op == Opcodes.DSTORE) {
                    k = 2;
                    wide = true;
                } else {
                    k = 2; // F 槽也按非 int / 不重叠处理
                    if (op == Opcodes.FLOAD || op == Opcodes.FSTORE) {
                        wide = false;
                    }
                }
                markSlot(kind, vn.var, k);
                if (wide) {
                    cat2[vn.var] = true;
                    cat2[vn.var + 1] = true;
                }
            } else if (n instanceof IincInsnNode) {
                markSlot(kind, ((IincInsnNode) n).var, 1);
            }
        }

        List<Integer> candidates = new ArrayList<Integer>();
        for (int s = argSlots; s < scratch; s++) {
            if (kind[s] == 1 && !cat2[s]) {
                candidates.add(Integer.valueOf(s));
            }
        }
        Collections.shuffle(candidates, r);
        int picked = 0;
        for (Integer cand : candidates) {
            if (picked >= LOCAL_CAP) {
                break;
            }
            if (r.nextInt(100) >= LOCAL_RATE) {
                continue;
            }
            int slot = cand.intValue();
            int salt = r.nextInt(0xFFFF) + 1;
            int ei = r.nextInt(net.encOwners.length);
            int di = r.nextInt(net.decOwners.length);
            for (AbstractInsnNode n : insns) {
                if (n instanceof VarInsnNode && ((VarInsnNode) n).var == slot) {
                    int op = n.getOpcode();
                    if (op == Opcodes.ISTORE) {
                        InsnList enc = new InsnList();
                        pushInt(enc, salt);
                        enc.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                                net.encOwners[ei], net.encMethods[ei], "(II)I", false));
                        mn.instructions.insertBefore(n, enc);
                    } else if (op == Opcodes.ILOAD) {
                        InsnList dec = new InsnList();
                        pushInt(dec, salt);
                        dec.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                                net.decOwners[di], net.decMethods[di], "(II)I", false));
                        mn.instructions.insert(n, dec);
                    }
                } else if (n instanceof IincInsnNode
                        && ((IincInsnNode) n).var == slot) {
                    IincInsnNode in = (IincInsnNode) n;
                    InsnList rep = new InsnList();
                    rep.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    pushInt(rep, salt);
                    rep.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            net.decOwners[di], net.decMethods[di], "(II)I", false));
                    pushInt(rep, in.incr);
                    rep.add(new InsnNode(Opcodes.IADD));
                    pushInt(rep, salt);
                    rep.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            net.encOwners[ei], net.encMethods[ei], "(II)I", false));
                    rep.add(new VarInsnNode(Opcodes.ISTORE, slot));
                    mn.instructions.insertBefore(n, rep);
                    mn.instructions.remove(n);
                }
            }
            picked++;
        }
        return picked;
    }

    private static void markSlot(int[] kind, int slot, int k) {
        if (slot < 0 || slot >= kind.length) {
            return;
        }
        if (kind[slot] == 0) {
            kind[slot] = k;
        } else if (kind[slot] != k) {
            kind[slot] = 2;
        }
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
