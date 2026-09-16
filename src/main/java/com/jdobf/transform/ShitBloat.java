package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LineNumberNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.AnalyzerException;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * 屎山脑残混淆（极端体积膨胀）。分两个阶段执行：
 *
 * <h3>阶段一：假方法海（平坦化之前）</h3>
 * 每个类灌入几十个 {@code private static synthetic} 假方法：
 * <ul>
 *   <li><b>小型方法（约 1/3）</b>：4-8 个脑残段落，描述符统一 (II)I，
 *       供阶段二的真实代码片段无环互调；</li>
 *   <li><b>巨型方法（约 2/3）</b>：14-40 个段落，嵌套有界循环、恒假
 *       分叉重汇、TABLESWITCH 假分支链、同伙方法互调、int 数组填充求和、
 *       StringBuilder 拼接 hashCode 等形态随机混排，单方法反编译后几百到
 *       上千行“炸裂内容”；</li>
 *   <li>方法随机穿插进真实成员列表，名字伪装成普通小写词。</li>
 * </ul>
 *
 * <h3>阶段二：真实方法灌屎（平坦化之后）</h3>
 * 对所有真实方法（含未被平坦化的方法、构造器 super 之后）用
 * BasicInterpreter 找栈深度 0 锚点，高密度插入栈严格中性的脑残片段：
 * 算术风暴 / 恒假分叉 / 有界小循环 / 4 路 switch / 调用小型假方法。
 * 片段只写专用垃圾槽，无除法、无空指针、无越界、无异常、不触碰真实栈。
 *
 * <h3>硬护栏</h3>
 * 常量池条目估算不超过 {@value #CP_CAP}（class 文件 u2 上限 65535）；
 * 单方法注入后估算不超过 60KB（方法体 u4 实际无硬限但栈图/工具链按 64KB
 * 保守处理）；接口/注解/模块信息、&lt;clinit&gt; 跳过。
 */
public final class ShitBloat {

    private static final int ACCESS =
            Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC;

    /** 常量池条目保守上限（硬上限 65535）。 */
    private static final int CP_CAP = 56000;
    /** 单方法注入后指令节点数 ×4（宽指令）估算上限。 */
    private static final int METHOD_NODE_CAP = 14500;
    /** 真实方法内片段注入密度（%）。 */
    private static final int INLINE_RATE = 38;
    /** 假方法中“小型（可被真实代码互调）”比例。 */
    private static final int SMALL_RATE = 34;
    /** 每类假方法硬上限。 */
    public static final int MAX_SHIT_METHODS = 400;

    /** 字符串拼接段落共用的字符串池（全类复用，只花少量常量池条目）。 */
    private static final String[] STRING_POOL = {
            "0", "1", "x", "ok", "null", "true", "a", "b", "c",
            "item", "value", "key", "data", "true,", ",false", "v=",
            "idx:", "n=", "tmp", "buf", "::", "->", "{}", "//"
    };

    private ShitBloat() {
    }

    /** 阶段统计：假方法数 / 真实方法片段数，以及假方法身份集合。 */
    public static final class Stats {
        public int fakeMethods;
        public int snippets;
        public final Set<MethodNode> fakes =
                Collections.newSetFromMap(new IdentityHashMap<MethodNode, Boolean>());
        public final List<String> smallNames = new ArrayList<String>();
    }

    // ==================================================================
    // 阶段一：假方法海
    // ==================================================================

    public static Stats floodMethods(ClassNode cn, Random random, int wanted) {
        Stats stats = new Stats();
        if (wanted <= 0) {
            return stats;
        }
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE)) != 0) {
            return stats;
        }
        wanted = Math.min(MAX_SHIT_METHODS, wanted);

        Set<String> usedNames = new HashSet<String>();
        for (MethodNode m : cn.methods) {
            usedNames.add(m.name);
        }
        for (FieldNode f : cn.fields) {
            usedNames.add(f.name);
        }

        CpBudget cp = estimateBaseCp(cn);
        // 字符串池 + StringBuilder 相关方法引用的一次性开销
        cp.add(STRING_POOL.length + 14);

        for (int i = 0; i < wanted; i++) {
            if (!cp.hasRoom(2)) {
                break;
            }
            boolean small = random.nextInt(100) < SMALL_RATE;
            if (!small && !cp.hasRoom(6)) {
                small = true; // 常量池快满时只造小方法
            }
            String name = uniqueName(usedNames, random);
            usedNames.add(name);
            MethodNode m = buildFake(cn, name, random, stats.smallNames, small, cp);
            int pos = cn.methods.isEmpty() ? 0 : random.nextInt(cn.methods.size() + 1);
            cn.methods.add(pos, m);
            stats.fakes.add(m);
            stats.fakeMethods++;
            if ("(II)I".equals(m.desc)) {
                stats.smallNames.add(name);
            }
        }

        // 少量垃圾字段（I/J/Z/[I/Object），同样随机穿插
        if (stats.fakeMethods > 0) {
            String[] fieldDescs = { "I", "J", "Z", "[I", "Ljava/lang/Object;" };
            int fields = Math.min(8, 2 + random.nextInt(4));
            for (int i = 0; i < fields && cp.hasRoom(1); i++) {
                String name = uniqueName(usedNames, random);
                usedNames.add(name);
                FieldNode f = new FieldNode(Opcodes.ASM9,
                        Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC
                                | Opcodes.ACC_TRANSIENT,
                        name, fieldDescs[random.nextInt(fieldDescs.length)], null, null);
                int pos = cn.fields.isEmpty() ? 0 : random.nextInt(cn.fields.size() + 1);
                cn.fields.add(pos, f);
            }
        }
        return stats;
    }

    /**
     * 构造一个假方法。small=true 时固定 (II)I、4-8 个轻量段落；
     * 否则描述符随机、14-40 个重型段落（数组/字符串/深层嵌套）。
     */
    private static MethodNode buildFake(ClassNode cn, String name, Random random,
                                        List<String> smallPool, boolean small,
                                        CpBudget cp) {
        String desc;
        int args;
        if (small) {
            desc = "(II)I";
            args = 2;
        } else {
            int d = random.nextInt(3);
            desc = d == 0 ? "(II)I" : (d == 1 ? "(III)I" : "(I)I");
            args = d == 2 ? 1 : (d == 1 ? 3 : 2);
        }
        int slotCount = small ? 6 : 10 + random.nextInt(5);
        int[] slots = new int[slotCount];
        for (int i = 0; i < slotCount; i++) {
            slots[i] = args + i;
        }
        int arrSlot = args + slotCount;       // 专用 int[] 槽
        int sbSlot = arrSlot + 1;             // 专用 StringBuilder 槽

        MethodNode m = new MethodNode(Opcodes.ASM9, ACCESS, name, desc, null, null);
        InsnList il = m.instructions;

        // 所有 int 槽先确定性初始化（分叉汇合处类型恒为 int）
        for (int s = 0; s < slotCount; s++) {
            int arg = random.nextInt(args);
            il.add(new VarInsnNode(Opcodes.ILOAD, arg));
            emitConst(il, random, cp, true);
            il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
            il.add(new VarInsnNode(Opcodes.ISTORE, slots[s]));
        }

        int sections = small ? 4 + random.nextInt(5) : 14 + random.nextInt(27);
        for (int i = 0; i < sections; i++) {
            int roll = random.nextInt(100);
            if (roll < 34) {
                emitStorm(il, random, slots, cp, small ? 5 + random.nextInt(10)
                        : 8 + random.nextInt(26));
            } else if (roll < 52) {
                emitFork(il, random, slots, cp, small ? 3 + random.nextInt(5)
                        : 5 + random.nextInt(12));
            } else if (roll < 68) {
                emitLoop(il, random, slots, cp, small ? 1 : 1 + random.nextInt(2),
                        small ? 5 : 7);
            } else if (roll < 80) {
                emitSwitchChain(il, random, slots, cp);
            } else if (roll < 90 && !smallPool.isEmpty()) {
                // 无环互调：只调更早出生的小型假方法
                String callee = smallPool.get(random.nextInt(smallPool.size()));
                int a = slots[random.nextInt(slotCount)];
                int b = slots[random.nextInt(slotCount)];
                int d = slots[random.nextInt(slotCount)];
                il.add(new VarInsnNode(Opcodes.ILOAD, a));
                il.add(new VarInsnNode(Opcodes.ILOAD, b));
                il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        cn.name, callee, "(II)I", false));
                il.add(new VarInsnNode(Opcodes.ISTORE, d));
            } else if (roll < 95 && !small) {
                emitArraySection(il, random, slots, arrSlot, cp);
            } else if (!small) {
                emitStringSection(il, random, slots, sbSlot, cp);
            } else {
                emitStorm(il, random, slots, cp, 6 + random.nextInt(8));
            }
            if (!cp.hasRoom(3)) {
                break;
            }
        }

        // 收尾：混合几个槽返回，保证方法形态像真实计算
        int ret = slots[random.nextInt(slotCount)];
        il.add(new VarInsnNode(Opcodes.ILOAD, ret));
        il.add(new VarInsnNode(Opcodes.ILOAD, slots[random.nextInt(slotCount)]));
        il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
        emitConst(il, random, cp, true);
        il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
        il.add(new InsnNode(Opcodes.IRETURN));
        return m;
    }

    // ==================================================================
    // 阶段二：真实方法灌屎
    // ==================================================================

    public static int floodInline(ClassNode cn, Random random, Stats stats) {
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE)) != 0) {
            return 0;
        }
        int total = 0;
        for (MethodNode mn : cn.methods.toArray(new MethodNode[0])) {
            if (stats.fakes.contains(mn)) {
                continue;
            }
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
                continue;
            }
            if (mn.name.equals("<clinit>")) {
                continue;
            }
            // 含 try-catch 的真实方法不内联灌屎（异常表/处理器帧敏感），
            // 假方法海仍然让这类类整体膨胀
            if (mn.tryCatchBlocks != null && !mn.tryCatchBlocks.isEmpty()) {
                continue;
            }
            try {
                total += floodOne(cn, mn, random, stats.smallNames);
            } catch (Throwable t) {
                // 单方法分析失败就不灌，保持原样
                continue;
            }
        }
        stats.snippets += total;
        return total;
    }

    private static int floodOne(ClassNode cn, MethodNode mn, Random random,
                                List<String> smallPool) throws AnalyzerException {
        AbstractInsnNode[] insns = mn.instructions.toArray();
        // 已接近护栏的方法不再灌
        if (insns.length >= METHOD_NODE_CAP - 200) {
            return 0;
        }

        // 构造器：只允许在 super/this 调用之后插入
        int barrier = -1;
        if (mn.name.equals("<init>")) {
            boolean found = false;
            for (int i = 0; i < insns.length; i++) {
                AbstractInsnNode n = insns[i];
                if (n.getOpcode() == Opcodes.INVOKESPECIAL && n instanceof MethodInsnNode
                        && ((MethodInsnNode) n).name.equals("<init>")) {
                    barrier = i;
                    found = true;
                    break;
                }
            }
            if (!found) {
                return 0;
            }
        }

        // 专用垃圾槽：取当前方法实际出现过的最大槽位之上 6 个 int 槽。
        // 不能信任 mn.maxLocals：LocalVariableLifting 平坦化成功后会把它
        // 永久留在 65535（COMPUTE_FRAMES 写出时会重算，但这里不能直接用）。
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
        int j0 = base, j1 = base + 1, j2 = base + 2, j3 = base + 3;
        int jc = base + 4, js = base + 5;
        int[] work = { j0, j1, j2, j3 };

        // 栈深度分析：紧边界帧（平坦化后指令数千条但栈深很小），
        // 不再放大到 65535——每帧 512KB 会让单方法分析吃掉数 GB
        Frame<BasicValue>[] frames = Analysis.basic(mn);
        if (frames == null) {
            return 0;
        }

        List<Integer> anchors = new ArrayList<Integer>();
        for (int i = 0; i < insns.length; i++) {
            AbstractInsnNode n = insns[i];
            int type = n.getType();
            if (type == AbstractInsnNode.FRAME || type == AbstractInsnNode.LABEL
                    || type == AbstractInsnNode.LINE) {
                continue;
            }
            if (i <= barrier) {
                continue;
            }
            Frame<BasicValue> f = frames[i];
            if (f == null || f.getStackSize() != 0) {
                continue;
            }
            anchors.add(Integer.valueOf(i));
        }
        if (anchors.isEmpty()) {
            return 0;
        }

        // 序言（垃圾槽初始化）的插入点：方法首指令 / 构造器 super 后首指令
        AbstractInsnNode prologuePoint = barrier >= 0 ? insns[barrier].getNext()
                : insns[0];
        while (prologuePoint != null && (prologuePoint.getType() == AbstractInsnNode.LABEL
                || prologuePoint.getType() == AbstractInsnNode.LINE
                || prologuePoint.getType() == AbstractInsnNode.FRAME)) {
            prologuePoint = prologuePoint.getNext();
        }
        if (prologuePoint == null) {
            return 0;
        }

        Collections.shuffle(anchors, random);
        int want = anchors.size() * INLINE_RATE / 100;
        int maxByBudget = (METHOD_NODE_CAP - insns.length) / 18;
        want = Math.max(0, Math.min(want, maxByBudget));

        // 选出要插的锚点后，按原方法位置从后往前插（节点引用保持有效）
        List<Integer> picked = new ArrayList<Integer>(anchors.subList(0, want));
        Collections.sort(picked);
        int inserted = 0;
        for (int k = picked.size() - 1; k >= 0; k--) {
            AbstractInsnNode anchor = insns[picked.get(k).intValue()];
            if (anchor == prologuePoint) {
                continue;
            }
            InsnList snip = buildInlineSnippet(cn, random, work, jc, js, smallPool);
            mn.instructions.insertBefore(anchor, snip);
            inserted++;
        }
        if (inserted == 0) {
            return 0;
        }

        // 垃圾槽序言（小常量，零常量池开销），最后插入保证排在所有片段之前
        InsnList prologue = new InsnList();
        int[] inits = { 0, 1, 3, 7, 4, 0 };
        for (int i = 0; i < inits.length; i++) {
            emitSmallConst(prologue, inits[i] + random.nextInt(8));
            prologue.add(new VarInsnNode(Opcodes.ISTORE, base + i));
        }
        mn.instructions.insertBefore(prologuePoint, prologue);
        return inserted;
    }

    /** 一段栈严格中性的脑残片段（只写 work/jc/js 槽）。 */
    private static InsnList buildInlineSnippet(ClassNode cn, Random random, int[] work,
                                               int jc, int js, List<String> smallPool) {
        InsnList il = new InsnList();
        int roll = random.nextInt(100);
        if (roll < 22) {
            // 真实 JDK API 环境垃圾（Thread.getId / nanoTime / Runtime …），
            // 提高外部调用密度，业务调用不再被纯数学包围
            il.add(JunkCode.envIntSnippet(random, work[0]));
            emitStorm(il, random, work, null, 2 + random.nextInt(5));
        } else if (roll < 46) {
            emitStorm(il, random, work, null, 6 + random.nextInt(18));
        } else if (roll < 62) {
            emitFork(il, random, work, null, 4 + random.nextInt(8));
        } else if (roll < 74) {
            emitSingleLoop(il, random, work, jc, 2 + random.nextInt(3));
        } else if (roll < 86) {
            emitMiniSwitch(il, random, work, js);
        } else if (!smallPool.isEmpty()) {
            // 调用小型假方法，结果丢弃进垃圾槽
            String callee = smallPool.get(random.nextInt(smallPool.size()));
            il.add(new VarInsnNode(Opcodes.ILOAD, work[0]));
            il.add(new VarInsnNode(Opcodes.ILOAD, work[1]));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    cn.name, callee, "(II)I", false));
            il.add(new VarInsnNode(Opcodes.ISTORE, work[2]));
            emitStorm(il, random, work, null, 3 + random.nextInt(6));
        } else {
            emitStorm(il, random, work, null, 6 + random.nextInt(14));
        }
        return il;
    }

    // ==================================================================
    // 脑残片段原语（全部纯 int、无除法、无异常）
    // ==================================================================

    private static final int[] ARITH = {
            Opcodes.IADD, Opcodes.ISUB, Opcodes.IMUL, Opcodes.IXOR,
            Opcodes.IOR, Opcodes.IAND
    };
    private static final int[] CMP = {
            Opcodes.IF_ICMPEQ, Opcodes.IF_ICMPNE, Opcodes.IF_ICMPLT,
            Opcodes.IF_ICMPGE, Opcodes.IF_ICMPGT, Opcodes.IF_ICMPLE
    };

    /**
     * 算术风暴：随机“dst = dst OP (槽|常量)”连打 ops 次。
     * cp 为 null 时只发小常量（零常量池开销，供内联片段使用）。
     */
    private static void emitStorm(InsnList il, Random random, int[] slots,
                                  CpBudget cp, int ops) {
        for (int k = 0; k < ops; k++) {
            int dst = slots[random.nextInt(slots.length)];
            il.add(new VarInsnNode(Opcodes.ILOAD, dst));
            if (random.nextInt(100) < 55) {
                il.add(new VarInsnNode(Opcodes.ILOAD, slots[random.nextInt(slots.length)]));
            } else {
                emitConst(il, random, cp, false);
            }
            il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
            if (random.nextInt(100) < 20) {
                // 偶尔再移位/取反，制造更长的无语义链
                emitSmallConst(il, random.nextInt(16));
                il.add(new InsnNode(random.nextBoolean() ? Opcodes.ISHL : Opcodes.IUSHR));
            }
            il.add(new VarInsnNode(Opcodes.ISTORE, dst));
        }
    }

    /** 恒走一边的分叉（两路都写同一目标槽），控制流图炸裂。 */
    private static void emitFork(InsnList il, Random random, int[] slots,
                                 CpBudget cp, int stormOps) {
        int s = slots[random.nextInt(slots.length)];
        int d = slots[random.nextInt(slots.length)];
        LabelNode els = new LabelNode();
        LabelNode join = new LabelNode();
        il.add(new VarInsnNode(Opcodes.ILOAD, s));
        emitSmallConst(il, random.nextInt(2000) - 1000);
        il.add(new JumpInsnNode(CMP[random.nextInt(CMP.length)], els));
        il.add(new VarInsnNode(Opcodes.ILOAD, d));
        emitConst(il, random, cp, false);
        il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
        emitStormPrefix(il, random, slots, cp, stormOps / 2, d);
        il.add(new VarInsnNode(Opcodes.ISTORE, d));
        il.add(new JumpInsnNode(Opcodes.GOTO, join));
        il.add(els);
        il.add(new VarInsnNode(Opcodes.ILOAD, d));
        emitConst(il, random, cp, false);
        il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
        emitStormPrefix(il, random, slots, cp, stormOps - stormOps / 2, d);
        il.add(new VarInsnNode(Opcodes.ISTORE, d));
        il.add(join);
    }

    /** 把 ops 次算术打在“栈顶已有值”之上（用于分叉内，保持 d 语义连贯）。 */
    private static void emitStormPrefix(InsnList il, Random random, int[] slots,
                                        CpBudget cp, int ops, int keep) {
        for (int k = 0; k < ops; k++) {
            if (random.nextInt(100) < 55) {
                il.add(new VarInsnNode(Opcodes.ILOAD, slots[random.nextInt(slots.length)]));
            } else {
                emitConst(il, random, cp, false);
            }
            il.add(new InsnNode(ARITH[random.nextInt(ARITH.length)]));
        }
    }

    /** 1-2 层有界循环（界 2..maxBound），循环体只碰 work 槽，不碰计数器。 */
    private static void emitLoop(InsnList il, Random random, int[] slots,
                                 CpBudget cp, int depth, int maxBound) {
        int c0 = slots[slots.length - 1];
        int c1 = slots[slots.length - 2];
        int[] inner = new int[slots.length - 2];
        System.arraycopy(slots, 0, inner, 0, inner.length);

        emitSmallConst(il, 2 + random.nextInt(maxBound - 1));
        il.add(new VarInsnNode(Opcodes.ISTORE, c0));
        LabelNode top0 = new LabelNode();
        LabelNode end0 = new LabelNode();
        il.add(top0);
        il.add(new VarInsnNode(Opcodes.ILOAD, c0));
        il.add(new JumpInsnNode(Opcodes.IFLE, end0));
        if (depth >= 2) {
            emitSmallConst(il, 2 + random.nextInt(maxBound - 1));
            il.add(new VarInsnNode(Opcodes.ISTORE, c1));
            LabelNode top1 = new LabelNode();
            LabelNode end1 = new LabelNode();
            il.add(top1);
            il.add(new VarInsnNode(Opcodes.ILOAD, c1));
            il.add(new JumpInsnNode(Opcodes.IFLE, end1));
            emitStorm(il, random, inner, cp, 4 + random.nextInt(8));
            il.add(new IincInsnNode(c1, -1));
            il.add(new JumpInsnNode(Opcodes.GOTO, top1));
            il.add(end1);
        }
        emitStorm(il, random, inner, cp, 4 + random.nextInt(10));
        il.add(new IincInsnNode(c0, -1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top0));
        il.add(end0);
    }

    /** 内联用单层小循环（计数器专用 jc，2..4 次）。 */
    private static void emitSingleLoop(InsnList il, Random random, int[] work,
                                       int jc, int bound) {
        emitSmallConst(il, bound);
        il.add(new VarInsnNode(Opcodes.ISTORE, jc));
        LabelNode top = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(top);
        il.add(new VarInsnNode(Opcodes.ILOAD, jc));
        il.add(new JumpInsnNode(Opcodes.IFLE, end));
        emitStorm(il, random, work, null, 3 + random.nextInt(6));
        il.add(new IincInsnNode(jc, -1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top));
        il.add(end);
    }

    /** 假 switch 链：selector = s & mask（mask=3/7），每路一段风暴后汇合。 */
    private static void emitSwitchChain(InsnList il, Random random, int[] slots,
                                        CpBudget cp) {
        int s = slots[random.nextInt(slots.length)];
        int sel = slots[slots.length - 1];
        int cases = random.nextInt(100) < 50 ? 4 : 8;
        int mask = cases - 1;
        il.add(new VarInsnNode(Opcodes.ILOAD, s));
        emitSmallConst(il, mask);
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new VarInsnNode(Opcodes.ISTORE, sel));
        il.add(new VarInsnNode(Opcodes.ILOAD, sel));
        LabelNode dflt = new LabelNode();
        LabelNode join = new LabelNode();
        LabelNode[] labels = new LabelNode[cases];
        for (int i = 0; i < cases; i++) {
            labels[i] = new LabelNode();
        }
        il.add(new TableSwitchInsnNode(0, cases - 1, dflt, labels));
        for (int i = 0; i < cases; i++) {
            il.add(labels[i]);
            emitStorm(il, random, slots, cp, 3 + random.nextInt(8));
            il.add(new JumpInsnNode(Opcodes.GOTO, join));
        }
        il.add(dflt);
        emitStorm(il, random, slots, cp, 3 + random.nextInt(8));
        il.add(join);
    }

    /** 内联用 4 路 mini switch（selector 专用 js）。 */
    private static void emitMiniSwitch(InsnList il, Random random, int[] work, int js) {
        il.add(new VarInsnNode(Opcodes.ILOAD, work[0]));
        il.add(new InsnNode(Opcodes.ICONST_3));
        il.add(new InsnNode(Opcodes.IAND));
        il.add(new VarInsnNode(Opcodes.ISTORE, js));
        il.add(new VarInsnNode(Opcodes.ILOAD, js));
        LabelNode dflt = new LabelNode();
        LabelNode join = new LabelNode();
        LabelNode l0 = new LabelNode();
        LabelNode l1 = new LabelNode();
        LabelNode l2 = new LabelNode();
        LabelNode l3 = new LabelNode();
        il.add(new TableSwitchInsnNode(0, 3, dflt,
                new LabelNode[] { l0, l1, l2, l3 }));
        LabelNode[] labs = { l0, l1, l2, l3, dflt };
        for (LabelNode lab : labs) {
            il.add(lab);
            emitStorm(il, random, work, null, 2 + random.nextInt(5));
            il.add(new JumpInsnNode(Opcodes.GOTO, join));
        }
        il.add(join);
    }

    /**
     * int 数组段落：new int[len]，循环填充垃圾计算，再循环求和写回普通槽。
     * len 4..10，所有下标由循环计数产生，不可能越界。
     */
    private static void emitArraySection(InsnList il, Random random, int[] slots,
                                         int arrSlot, CpBudget cp) {
        int lenS = slots[0];
        int iS = slots[1];
        int sumS = slots[2];
        int[] work = new int[slots.length - 3];
        System.arraycopy(slots, 3, work, 0, work.length);
        int len = 4 + random.nextInt(7);

        emitSmallConst(il, len);
        il.add(new VarInsnNode(Opcodes.ISTORE, lenS));
        il.add(new VarInsnNode(Opcodes.ILOAD, lenS));
        il.add(new IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_INT));
        il.add(new VarInsnNode(Opcodes.ASTORE, arrSlot));

        LabelNode top = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, iS));
        il.add(top);
        il.add(new VarInsnNode(Opcodes.ILOAD, iS));
        il.add(new VarInsnNode(Opcodes.ILOAD, lenS));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, arrSlot));
        il.add(new VarInsnNode(Opcodes.ILOAD, iS));
        int v = work[random.nextInt(work.length)];
        il.add(new VarInsnNode(Opcodes.ILOAD, v));
        il.add(new VarInsnNode(Opcodes.ILOAD, iS));
        il.add(new InsnNode(Opcodes.IMUL));
        emitSmallConst(il, 1 + random.nextInt(255));
        il.add(new InsnNode(Opcodes.IXOR));
        il.add(new InsnNode(Opcodes.IASTORE));
        il.add(new IincInsnNode(iS, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top));
        il.add(end);

        LabelNode top2 = new LabelNode();
        LabelNode end2 = new LabelNode();
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, sumS));
        il.add(new InsnNode(Opcodes.ICONST_0));
        il.add(new VarInsnNode(Opcodes.ISTORE, iS));
        il.add(top2);
        il.add(new VarInsnNode(Opcodes.ILOAD, iS));
        il.add(new VarInsnNode(Opcodes.ILOAD, lenS));
        il.add(new JumpInsnNode(Opcodes.IF_ICMPGE, end2));
        il.add(new VarInsnNode(Opcodes.ILOAD, sumS));
        il.add(new VarInsnNode(Opcodes.ALOAD, arrSlot));
        il.add(new VarInsnNode(Opcodes.ILOAD, iS));
        il.add(new InsnNode(Opcodes.IALOAD));
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, sumS));
        il.add(new IincInsnNode(iS, 1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top2));
        il.add(end2);
        // 数组槽在此之后不再被读取，引用槽保持 int[] 类型，不污染 int 槽
    }

    /**
     * StringBuilder 段落：append 2-5 次池内短串后取 hashCode 喂给 int 槽。
     */
    private static void emitStringSection(InsnList il, Random random, int[] slots,
                                          int sbSlot, CpBudget cp) {
        int dst = slots[random.nextInt(slots.length)];
        int times = 2 + random.nextInt(4);
        int cnt = slots[slots.length - 1];
        il.add(new TypeInsnNode(Opcodes.NEW, "java/lang/StringBuilder"));
        il.add(new InsnNode(Opcodes.DUP));
        il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/StringBuilder", "<init>", "()V", false));
        il.add(new VarInsnNode(Opcodes.ASTORE, sbSlot));
        emitSmallConst(il, times);
        il.add(new VarInsnNode(Opcodes.ISTORE, cnt));
        LabelNode top = new LabelNode();
        LabelNode end = new LabelNode();
        il.add(top);
        il.add(new VarInsnNode(Opcodes.ILOAD, cnt));
        il.add(new JumpInsnNode(Opcodes.IFLE, end));
        il.add(new VarInsnNode(Opcodes.ALOAD, sbSlot));
        il.add(new LdcInsnNode(STRING_POOL[random.nextInt(STRING_POOL.length)]));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "append",
                "(Ljava/lang/String;)Ljava/lang/StringBuilder;", false));
        il.add(new InsnNode(Opcodes.POP));
        il.add(new IincInsnNode(cnt, -1));
        il.add(new JumpInsnNode(Opcodes.GOTO, top));
        il.add(end);
        il.add(new VarInsnNode(Opcodes.ALOAD, sbSlot));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/StringBuilder", "toString", "()Ljava/lang/String;", false));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/String", "hashCode", "()I", false));
        il.add(new VarInsnNode(Opcodes.ISTORE, dst));
    }

    // ==================================================================
    // 常量发射 / 常量池预算 / 命名
    // ==================================================================

    /** 小常量：iconst/bipush/sipush，不产生常量池条目。 */
    private static void emitSmallConst(InsnList il, int v) {
        if (v >= -1 && v <= 5) {
            il.add(new InsnNode(Opcodes.ICONST_0 + v));
        } else if (v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE) {
            il.add(new IntInsnNode(Opcodes.BIPUSH, v));
        } else if (v >= Short.MIN_VALUE && v <= Short.MAX_VALUE) {
            il.add(new IntInsnNode(Opcodes.SIPUSH, v));
        } else {
            il.add(new IntInsnNode(Opcodes.SIPUSH, (short) v));
        }
    }

    /**
     * 随机常量：~70% 走小常量（零常量池开销），其余 LDC 大整数并计入预算；
     * 预算紧张或 cp=null（内联片段）时只发小常量。
     * forceSmall=true（收尾/初始化等热路径）强制小常量。
     */
    private static void emitConst(InsnList il, Random random, CpBudget cp,
                                  boolean forceSmall) {
        if (!forceSmall && cp != null && cp.hasRoom(1) && random.nextInt(100) < 30) {
            il.add(new LdcInsnNode(Integer.valueOf(random.nextInt())));
            cp.add(1);
        } else {
            int v;
            int kind = random.nextInt(3);
            if (kind == 0) {
                v = random.nextInt(64) - 32;
            } else if (kind == 1) {
                v = random.nextInt(4096) - 2048;
            } else {
                v = random.nextInt(65536) - 32768;
            }
            emitSmallConst(il, v);
        }
    }

    /** 保守估算类当前常量池占用（宁多勿少）。 */
    private static CpBudget estimateBaseCp(ClassNode cn) {
        long used = 256L + cn.methods.size() * 2L + cn.fields.size() * 2L;
        for (MethodNode mn : cn.methods) {
            if (mn.instructions == null) {
                continue;
            }
            for (AbstractInsnNode n : mn.instructions.toArray()) {
                int t = n.getType();
                if (t == AbstractInsnNode.LDC_INSN || t == AbstractInsnNode.TYPE_INSN
                        || t == AbstractInsnNode.METHOD_INSN
                        || t == AbstractInsnNode.FIELD_INSN
                        || t == AbstractInsnNode.INVOKE_DYNAMIC_INSN) {
                    used++;
                }
            }
        }
        return new CpBudget(used);
    }

    /** 常量池预算计数器。 */
    private static final class CpBudget {
        long used;

        CpBudget(long used) {
            this.used = used;
        }

        void add(long n) {
            used += n;
        }

        boolean hasRoom(long n) {
            return used + n < CP_CAP;
        }
    }

    private static String uniqueName(Set<String> used, Random random) {
        String name;
        do {
            int len = 8 + random.nextInt(5);
            StringBuilder sb = new StringBuilder(len);
            for (int i = 0; i < len; i++) {
                sb.append((char) ('a' + random.nextInt(26)));
            }
            name = sb.toString();
        } while (used.contains(name));
        return name;
    }
}
