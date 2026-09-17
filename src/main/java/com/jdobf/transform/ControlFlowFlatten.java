package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.LookupSwitchInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TableSwitchInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.Analyzer;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

/**
 * 控制流平坦化（极端形态）：把整个方法重写为“多分发器 + 业务数据密钥化状态”
 * 的状态机，并在真实代码块与转移路径上插入大量不透明垃圾控制流。
 *
 * <ol>
 *   <li><b>语句级二次切碎</b>：局部变量提升为 Object[] 之后，用
 *       BasicInterpreter 找到所有入栈深度为 0 的<b>语句边界</b>（提升后每条
 *       原始语句都以 ALOAD 数组槽开头），高密度再切——一次 new、一次
 *       setTitle、一次 setSize 各占一个独立 case，杜绝“一大坨核心操作塞在
 *       同一个 case 里”。</li>
 *   <li><b>业务数据密钥化状态（数据依赖）</b>：新增 int 上下文槽 ctx，
 *       在方法执行路径上由<b>真实业务值</b>持续喂养（int 运算结果、方法
 *       返回值、解密后的字符串等，见 {@link #insertDataProbes}）。每个状态
 *       只有一个随机 32 位 key；分发时比较 {@code state ^ H(ctx) == key}，
 *       转移时写入 {@code state = key ^ H(ctx)}。H(ctx) 是运行期纯 int
 *       函数。剥离任何一段探针 → ctx 漂移 → 命中错误/不存在的 key →
 *       ACONST_NULL ATHROW，状态转移不再是独立算术（n=-139 那种），
 *       而是与窗口标题解密结果等业务数据强绑定。</li>
 *   <li><b>多份分发器</b>：发射两份完全相同的 LOOKUPSWITCH 分发器，转移随机
 *       回跳其中一个，破坏单一 dispatch 循环模式。</li>
 *   <li><b>桥接状态</b>：随机比例的真实边先进入只做垃圾运算的桥接 case，
 *       再二次分发到目标（偶尔两层），调用关系被稀释成无意义的状态长链。</li>
 *   <li><b>死诱饵状态</b>：若干永不被任何真实边引用的 case，内含有限循环、
 *       分叉、垃圾运算，结尾再“转移”到随机真实状态，真假状态同构。</li>
 *   <li><b>块内垃圾指令</b>：真实 case 入口随机插入纯 int 垃圾运算、分叉重汇
 *       和极短有限循环（只写专用垃圾槽，无副作用、不触碰真实数组/状态/ctx）。</li>
 *   <li><b>不透明谓词分叉</b>：转移边随机被恒真/恒假谓词包裹成两条都到目标
 *       的路径，两条路径分别用“写状态回分发器”和“直接 GOTO case”。</li>
 *   <li><b>直达路由</b>：部分转移不经过分发器，直接 GOTO 目标 case 标签
 *       （所有 case 入口帧完全一致，校验等价）。</li>
 * </ol>
 *
 * 平坦化前先用 {@link StackNormalizer} 归并非空栈汇合，再用
 * {@link LocalVariableLifting} 把局部变量提升为 Object[]，保证所有 case
 * 在分发器处合并为统一帧（Object[] 数组 + int 状态 + 3 个 int 垃圾槽 +
 * int 上下文槽 ctx）。
 *
 * 保守跳过：抽象/native、&lt;init&gt;/&lt;clinit&gt;、try-catch、
 * TABLESWITCH/LOOKUPSWITCH/JSR/RET、无跳转方法、NEW..&lt;init&gt; 区间内
 * 存在标签（未初始化引用不可 aastore）、提升/分析失败、体积预算超限的方法
 * （预算按最悲观结构上限估算）。
 */
public final class ControlFlowFlatten {

    /** 64KB 方法体硬上限下的保守综合预算（所有随机结构取最坏值估算）。 */
    private static final int METHOD_BUDGET = 56000;

    /** 分发器副本数（每份都是全量 LOOKUPSWITCH）。 */
    private static final int DISPATCHERS = 2;
    /** 每方法死诱饵状态数范围。 */
    private static final int DEAD_MIN = 3;
    private static final int DEAD_MAX = 5;
    /** 语句边界切碎后额外切点的接纳比例。 */
    private static final int CUT_RATE = 72;
    /** 单个方法最多植入的数据流探针数（体积/性能护栏）。 */
    private static final int MAX_PROBES = 220;
    /** 候选生产指令中植入探针的比例。 */
    private static final int PROBE_RATE = 30;

    private ControlFlowFlatten() {
    }

    /**
     * 对类内所有可平坦化的方法执行（归一化 → 提升 → 数据流探针 → 语句级切碎
     * → 状态机重写），返回成功平坦化的方法数。
     */
    public static int apply(ClassNode cn, Random random, ClassLoader typeLoader) {
        int count = 0;
        for (MethodNode mn : cn.methods) {
            try {
                if (!eligible(mn)) {
                    continue;
                }
                // 先于一切改写：NEW..<init> 区间内存在标签时，非空栈归一化会把
                // 未初始化引用暂存进局部槽，随后的 Object[] 提升会把它 aastore
                // （JVM 明令禁止），这类方法整体放弃平坦化
                if (hasUninitializedMerge(mn)) {
                    continue;
                }
                if (!StackNormalizer.normalize(cn, mn, typeLoader)) {
                    continue;
                }
                int[] arrSlotOut = new int[] { -1 };
                InsnList[] prologueOut = new InsnList[] { null };
                if (!LocalVariableLifting.lift(cn, mn, typeLoader, arrSlotOut, prologueOut)) {
                    continue;
                }
                int arrSlot = arrSlotOut[0];
                // 槽位布局：arr | x | y | z | tmp | junk×3 | ctx
                Machine mac = new Machine(random);
                mac.xS = arrSlot + 1;
                mac.yS = arrSlot + 2;
                mac.zS = arrSlot + 3;
                mac.tS = arrSlot + 4;
                mac.junkSlots = new int[] { arrSlot + 5, arrSlot + 6, arrSlot + 7 };
                mac.cS = arrSlot + 8;
                // 探针必须在切分之前植入：探针栈中性，不会制造新的 depth-0 点，
                // 因而不会被后续切碎从值生产点上撕开
                insertDataProbes(mn, mac.cS, random);
                Set<AbstractInsnNode> cutAnchors = findCutAnchors(mn, random);
                if (flattenMethod(mn, random, prologueOut[0], mac, cutAnchors)) {
                    count++;
                }
            } catch (Throwable t) {
                // 单方法失败时该方法可能已被部分改写，交由外层逐类 try/catch
                // 回退到基线（仅改名）字节码
                throw new RuntimeException(mn.name + mn.desc + ": " + t, t);
            }
        }
        return count;
    }

    /**
     * 结构性探测：线性扫描指令流，用 LIFO 栈跟踪尚未调用 &lt;init&gt; 的 NEW
     * （处理 {@code new A(new B())} 嵌套）。只要有任何 LabelNode 落在未关闭的
     * NEW..&lt;init&gt; 区间内，说明该标签处的操作数栈上携带着未初始化引用
     * （典型场景：构造参数含三目/短路/switch，javac 在 NEW DUP 与
     * INVOKESPECIAL 之间生成跳转标签）。这种方法不能平坦化：栈归一化会把
     * 未初始化引用 ASTORE 暂存，变量提升再把它 AASTORE 进 Object[]，
     * 触发 “uninitialized not assignable to Object” VerifyError。
     */
    private static boolean hasUninitializedMerge(MethodNode mn) {
        List<String> pendingNew = new ArrayList<String>();
        for (AbstractInsnNode n : mn.instructions.toArray()) {
            int type = n.getType();
            if (type == AbstractInsnNode.TYPE_INSN && n.getOpcode() == Opcodes.NEW) {
                pendingNew.add(((org.objectweb.asm.tree.TypeInsnNode) n).desc);
            } else if (type == AbstractInsnNode.METHOD_INSN
                    && n.getOpcode() == Opcodes.INVOKESPECIAL
                    && ((MethodInsnNode) n).name.equals("<init>")
                    && !pendingNew.isEmpty()) {
                pendingNew.remove(pendingNew.size() - 1);
            } else if (type == AbstractInsnNode.LABEL && !pendingNew.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /** 基于原始（提升前）方法决定是否值得/可以提升并平坦化。 */
    private static boolean eligible(MethodNode mn) {
        if (mn.instructions == null || mn.instructions.size() == 0) {
            return false;
        }
        if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
            return false;
        }
        if (mn.name.equals("<init>") || mn.name.equals("<clinit>")) {
            return false;
        }
        if (mn.tryCatchBlocks != null && !mn.tryCatchBlocks.isEmpty()) {
            return false;
        }
        // StatementOutliner 外提片段的内部标记：极简直线方法，平坦化预处理
        // 会误判，直接跳过（其余 pass 不受此标记影响）
        if ((mn.access & Opcodes.ACC_VARARGS) != 0) {
            return false;
        }
        AbstractInsnNode[] insns = mn.instructions.toArray();
        Set<LabelNode> jumpTargets =
                Collections.newSetFromMap(new java.util.IdentityHashMap<LabelNode, Boolean>());
        int varAccess = 0;
        for (AbstractInsnNode n : insns) {
            int op = n.getOpcode();
            switch (n.getType()) {
                case AbstractInsnNode.JUMP_INSN:
                    if (op == Opcodes.JSR) {
                        return false;
                    }
                    jumpTargets.add(((JumpInsnNode) n).label);
                    break;
                case AbstractInsnNode.TABLESWITCH_INSN: {
                    TableSwitchInsnNode ts = (TableSwitchInsnNode) n;
                    jumpTargets.add(ts.dflt);
                    for (LabelNode l : ts.labels) {
                        jumpTargets.add(l);
                    }
                    break;
                }
                case AbstractInsnNode.LOOKUPSWITCH_INSN: {
                    LookupSwitchInsnNode ls = (LookupSwitchInsnNode) n;
                    jumpTargets.add(ls.dflt);
                    for (LabelNode l : ls.labels) {
                        jumpTargets.add(l);
                    }
                    break;
                }
                case AbstractInsnNode.VAR_INSN:
                    varAccess++;
                    break;
                case AbstractInsnNode.IINC_INSN:
                    varAccess++;
                    break;
                default:
                    if (op == Opcodes.RET) {
                        return false;
                    }
            }
        }
        // 无任何跳转的直线方法（典型：main 顺序调用、getter/setter）同样套上
        // 状态机：切碎锚点按 depth-0 语句边界切块，块间走顺序 commit 边；
        // 即使只有 1 个块（短方法），状态机外壳 + 死诱饵也会彻底改写其形态
        int blockCount = estimateBlockCount(insns, jumpTargets);
        if (blockCount < 1 || blockCount > 6000) {
            return false;
        }
        // 最坏结构估算：提升后长度、语句级切碎点、探针、桥接、死诱饵、双分发器
        int liftedLen = insns.length + varAccess * 4;
        // 直线方法（无任何跳转/switch）切碎后每刀都要配一条顺序 commit 边，
        // 体积随块数线性膨胀（905 条的 main 按 /4 切会逼近 64KB），用 /6
        // 收紧；有跳转方法天然块多块小，保持 /4 高密度切碎
        int cutCap = jumpTargets.isEmpty() ? liftedLen / 6 : liftedLen / 4;
        int expBlocks = blockCount + cutCap;
        int expBridges = (int) ((long) expBlocks * 125L / 100L * 41L / 100L);
        int deads = DEAD_MAX;
        int cases = expBlocks + expBridges + deads;
        long estimate = (long) insns.length * 3L + (long) varAccess * 14L + 200L
                // 两份分发器：双派生互锁守卫（guard 约 40 条/份）
                + (long) DISPATCHERS * 60L
                // + 每状态一个 LOOKUPSWITCH 条目（条目约 8 字节 + 头部）
                + (long) cases * DISPATCHERS * 9L
                // 真实 case：平均块内垃圾 + 三寄存器块内非线性 commit（约 40 条/边）
                + (long) expBlocks * 120L
                // 数据流探针（按字符串探针长度悲观取 24 字节）
                + (long) (insns.length + varAccess * 2) * 8L
                // 桥接 case 与死诱饵（含循环；commit 与 guard 显著变长）
                + (long) expBridges * 150L + (long) deads * 200L;
        return estimate <= METHOD_BUDGET;
    }

    /** 与 flattenMethod 的切分逻辑保持一致的基本块数预估。 */
    private static int estimateBlockCount(AbstractInsnNode[] insns, Set<LabelNode> jumpTargets) {
        int blocks = 0;
        boolean expectLeader = true;
        for (AbstractInsnNode n : insns) {
            int type = n.getType();
            if (type == AbstractInsnNode.FRAME || type == AbstractInsnNode.LINE) {
                continue;
            }
            boolean leader = expectLeader
                    || (type == AbstractInsnNode.LABEL && jumpTargets.contains(n));
            if (leader) {
                blocks++;
            }
            expectLeader = isTerminator(n.getOpcode());
        }
        return blocks;
    }

    /**
     * 提升+探针植入之后分析栈深度，返回“可以额外切成基本块”的指令锚点：
     * 入栈深度为 0 的真实指令（提升后每条原始语句以 ALOAD 数组槽开头，
     * 天然是 depth-0 边界），非标签/伪节点、自身/前驱不是终结指令。
     * 锚点高密度接纳（{@link #CUT_RATE}%），使每个核心操作各占一个 case。
     */
    private static Set<AbstractInsnNode> findCutAnchors(MethodNode mn, Random random) {
        Set<AbstractInsnNode> anchors =
                Collections.newSetFromMap(new java.util.IdentityHashMap<AbstractInsnNode, Boolean>());
        AbstractInsnNode[] insns = mn.instructions.toArray();
        Frame<BasicValue>[] frames = Analysis.basic(mn);
        if (frames == null) {
            return anchors;
        }

        int cap = (insns.length / 4) + 2;
        // 直线方法（无跳转/switch）：切碎刀数收紧到 /6，防块数线性膨胀撑爆 64KB
        boolean straight = true;
        for (AbstractInsnNode z : insns) {
            int t = z.getType();
            if (t == AbstractInsnNode.JUMP_INSN
                    || t == AbstractInsnNode.TABLESWITCH_INSN
                    || t == AbstractInsnNode.LOOKUPSWITCH_INSN) {
                straight = false;
                break;
            }
        }
        if (straight) {
            cap = (insns.length / 6) + 1;
        }
        List<Integer> eligible = new ArrayList<Integer>();
        for (int i = 0; i < insns.length; i++) {
            AbstractInsnNode n = insns[i];
            int type = n.getType();
            if (type == AbstractInsnNode.FRAME || type == AbstractInsnNode.LINE
                    || type == AbstractInsnNode.LABEL) {
                continue;
            }
            if (isTerminator(n.getOpcode())
                    || type == AbstractInsnNode.TABLESWITCH_INSN
                    || type == AbstractInsnNode.LOOKUPSWITCH_INSN) {
                continue;
            }
            Frame<BasicValue> f = frames[i];
            if (f == null || f.getStackSize() != 0) {
                continue;
            }
            AbstractInsnNode prev = n.getPrevious();
            while (prev != null && (prev.getType() == AbstractInsnNode.FRAME
                    || prev.getType() == AbstractInsnNode.LINE
                    || prev.getType() == AbstractInsnNode.LABEL)) {
                prev = prev.getPrevious();
            }
            if (prev == null || isTerminator(prev.getOpcode())
                    || prev.getType() == AbstractInsnNode.TABLESWITCH_INSN
                    || prev.getType() == AbstractInsnNode.LOOKUPSWITCH_INSN) {
                continue;
            }
            eligible.add(i);
        }
        Collections.shuffle(eligible, random);
        int want = Math.min(cap, eligible.size() * CUT_RATE / 100);
        for (int k = 0; k < want; k++) {
            anchors.add(insns[eligible.get(k)]);
        }
        return anchors;
    }

    /**
     * 数据流探针：在真实业务值的生产指令之后，栈中性地 DUP 出该值并把它混入
     * ctx（{@code ctx = (ctx * M + v) ^ X}，M 为奇数）。
     *
     * 钩住的生产点：
     * <ul>
     *   <li>int 二元/一元运算、ARRAYLENGTH、INSTANCEOF——中间计算结果；</li>
     *   <li>返回 int/boolean/... 的方法调用（含 Integer.intValue 拆箱，即被
     *       提升的真实局部变量值）；</li>
     *   <li>int 常量 LDC；</li>
     *   <li>String LDC 与任何返回 String 的调用（含字符串加密的
     *       INVOKESTATIC 解密结果——“窗口标题解密成功后”的真实值）；
     *       String 走 {@code String.valueOf((Object)v).hashCode()}，
     *       null 安全（映射为 "null" 的哈希），不改变业务栈。</li>
     * </ul>
     * 探针不含任何标签/跳转，栈严格中性，可出现在任意栈深度；剥离它会让 ctx
     * 少一次喂养，后续所有 {@code state ^ H(ctx)} 状态全部错位。
     */
    private static void insertDataProbes(MethodNode mn, int ctxSlot, Random random) {
        AbstractInsnNode[] insns = mn.instructions.toArray();
        Frame<BasicValue>[] frames = Analysis.basic(mn);
        if (frames == null) {
            return;
        }

        List<Integer> candidates = new ArrayList<Integer>();
        for (int i = 0; i < insns.length; i++) {
            AbstractInsnNode n = insns[i];
            if (frames[i] == null) {
                continue;
            }
            boolean intProducer = false;
            boolean stringProducer = false;
            int op = n.getOpcode();
            switch (n.getType()) {
                case AbstractInsnNode.INSN:
                    intProducer = op == Opcodes.IADD || op == Opcodes.ISUB
                            || op == Opcodes.IMUL || op == Opcodes.IDIV || op == Opcodes.IREM
                            || op == Opcodes.ISHL || op == Opcodes.ISHR || op == Opcodes.IUSHR
                            || op == Opcodes.IOR || op == Opcodes.IXOR || op == Opcodes.IAND
                            || op == Opcodes.INEG || op == Opcodes.ARRAYLENGTH
                            || op == Opcodes.INSTANCEOF;
                    break;
                case AbstractInsnNode.METHOD_INSN: {
                    Type ret = Type.getReturnType(((MethodInsnNode) n).desc);
                    int sort = ret.getSort();
                    intProducer = sort == Type.BOOLEAN || sort == Type.BYTE
                            || sort == Type.CHAR || sort == Type.SHORT || sort == Type.INT;
                    stringProducer = ret.getSort() == Type.OBJECT
                            && "java/lang/String".equals(ret.getInternalName());
                    break;
                }
                case AbstractInsnNode.LDC_INSN: {
                    Object cst = ((LdcInsnNode) n).cst;
                    intProducer = cst instanceof Integer;
                    stringProducer = cst instanceof String;
                    break;
                }
                default:
                    break;
            }
            if (!intProducer && !stringProducer) {
                continue;
            }
            // 值生产点与下一条真实指令之间夹着标签/帧（跳转目标）时放弃：
            // 该值可能跨边存活，保守处理
            AbstractInsnNode next = n.getNext();
            while (next != null && next.getType() == AbstractInsnNode.LINE) {
                next = next.getNext();
            }
            if (next == null || next.getType() == AbstractInsnNode.LABEL
                    || next.getType() == AbstractInsnNode.FRAME) {
                continue;
            }
            candidates.add(i);
        }
        Collections.shuffle(candidates, random);
        int want = Math.min(MAX_PROBES, candidates.size() * PROBE_RATE / 100);
        int[] picked = new int[want];
        for (int k = 0; k < want; k++) {
            picked[k] = candidates.get(k);
        }
        java.util.Arrays.sort(picked);
        // 从后往前插：先插的节点位于后方，不影响前方节点身份/邻接关系
        for (int k = picked.length - 1; k >= 0; k--) {
            AbstractInsnNode p = insns[picked[k]];
            boolean isString = false;
            if (p.getType() == AbstractInsnNode.METHOD_INSN) {
                isString = "java/lang/String".equals(
                        Type.getReturnType(((MethodInsnNode) p).desc).getInternalName());
            } else if (p.getType() == AbstractInsnNode.LDC_INSN) {
                isString = ((LdcInsnNode) p).cst instanceof String;
            }
            InsnList probe = new InsnList();
            probe.add(new InsnNode(Opcodes.DUP));
            if (isString) {
                // null 安全：String.valueOf((Object) s) 永不返回 null
                probe.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        "java/lang/String", "valueOf",
                        "(Ljava/lang/Object;)Ljava/lang/String;", false));
                probe.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                        "java/lang/String", "hashCode", "()I", false));
            }
            // 栈顶 int v：ctx = (ctx * M + v) ^ X
            int m = random.nextInt(0x10000) | 1;
            int x = random.nextInt();
            probe.add(new VarInsnNode(Opcodes.ILOAD, ctxSlot));
            pushInt(probe, m);
            probe.add(new InsnNode(Opcodes.IMUL));
            probe.add(new InsnNode(Opcodes.IADD));
            pushInt(probe, x);
            probe.add(new InsnNode(Opcodes.IXOR));
            probe.add(new VarInsnNode(Opcodes.ISTORE, ctxSlot));
            mn.instructions.insert(p, probe);
        }
    }

    /**
     * 高强度状态机：三个互相锁定的 int 寄存器 + 业务喂养的 ctx。
     *
     * 每个 case 入口（key=K）恒成立的不变量：
     * <pre>
     *   x = K ^ H0(c) ^ H1(y)
     *   z = (y*P + Q*K) ^ Hz(c)        (P、Q 为奇数，Q 在 2^32 环上可逆)
     * </pre>
     * 分发器用两条<b>独立代数路径</b>各自还原 K 并互锁：
     * <pre>
     *   k1 = x ^ H0(c) ^ H1(y)                  （异或-移位族）
     *   k2 = (z ^ Hz(c) - y*P) * Q^{-1}         （奇数乘法环族）
     *   k1 ^ k2 != 0 → 兜底陷阱；否则 switch(k1)
     * </pre>
     * 块尾转移在<b>块内</b>消费当前 x/y/z/c，经 per-edge 随机常数的
     * rotate/xor/odd-mul 非线性链推进：
     * <pre>
     *   y' = (rotl(x ^ e0, r) + y*ae + be) ^ z ^ Hx(c) ^ (K'*ce + de)
     *   z' = (y'*P + Q*K') ^ Hz(c)
     *   x' = K' ^ H0(c) ^ H1(y')
     * </pre>
     * 不存在 1,2,3 线性状态：switch 里虽仍是 32 位 key，但任何一个块里都
     * 读不到“目标 key 常量直接赋给状态变量”——目标值由当前三寄存器与业务
     * ctx 经非线性运算动态算出；剥离/篡改任一影子寄存器更新，下一次分发
     * k1≠k2 立即跑飞。
     */
    static final class Machine {
        // 槽位（由 apply 按 arr 之后顺序绑定）
        int xS, yS, zS, tS, cS;
        int[] junkSlots;
        LabelNode[] dispatchLabels;
        LabelNode exit;

        final Random rnd;
        // 方法级全局常数（构造时随机）
        final int sH0, m0, b0;
        final int mz, bz;
        final int sHx, mx;
        final int sH1;
        final int P, Q, qInv;

        Machine(Random random) {
            this.rnd = random;
            this.sH0 = 1 + random.nextInt(31);
            this.m0 = random.nextInt() | 1;
            this.b0 = random.nextInt();
            this.mz = random.nextInt() | 1;
            this.bz = random.nextInt();
            this.sHx = 1 + random.nextInt(31);
            this.mx = random.nextInt() | 1;
            this.sH1 = 1 + random.nextInt(31);
            this.P = random.nextInt() | 1;
            this.Q = random.nextInt() | 1;
            this.qInv = java.math.BigInteger.valueOf(this.Q & 0xFFFFFFFFL)
                    .modInverse(java.math.BigInteger.ONE.shiftLeft(32))
                    .intValue();
            selfTest();
        }

        // ---- H 族：消耗栈顶 int，留下一个 int ----
        /** H0(c) = (c ^ (c >>> s)) * m0 + b0 */
        void emitH0(InsnList il) {
            il.add(new InsnNode(Opcodes.DUP));
            pushInt(il, sH0);
            il.add(new InsnNode(Opcodes.IUSHR));
            il.add(new InsnNode(Opcodes.IXOR));
            pushInt(il, m0);
            il.add(new InsnNode(Opcodes.IMUL));
            pushInt(il, b0);
            il.add(new InsnNode(Opcodes.IADD));
        }

        /** Hz(c) = c * mz + bz */
        void emitHz(InsnList il) {
            pushInt(il, mz);
            il.add(new InsnNode(Opcodes.IMUL));
            pushInt(il, bz);
            il.add(new InsnNode(Opcodes.IADD));
        }

        /** Hx(c) = (c ^ (c >>> s)) * mx */
        void emitHx(InsnList il) {
            il.add(new InsnNode(Opcodes.DUP));
            pushInt(il, sHx);
            il.add(new InsnNode(Opcodes.IUSHR));
            il.add(new InsnNode(Opcodes.IXOR));
            pushInt(il, mx);
            il.add(new InsnNode(Opcodes.IMUL));
        }

        /** H1(y) = y ^ (y >>> s) */
        void emitH1(InsnList il) {
            il.add(new InsnNode(Opcodes.DUP));
            pushInt(il, sH1);
            il.add(new InsnNode(Opcodes.IUSHR));
            il.add(new InsnNode(Opcodes.IXOR));
        }

        /** 栈顶 v → rotl(v, r)（r 由 edge 给定，1..31），用专用临时槽中转。 */
        void emitRotl(InsnList il, int r) {
            il.add(new VarInsnNode(Opcodes.ISTORE, tS));
            il.add(new VarInsnNode(Opcodes.ILOAD, tS));
            pushInt(il, r);
            il.add(new InsnNode(Opcodes.ISHL));
            il.add(new VarInsnNode(Opcodes.ILOAD, tS));
            pushInt(il, 32 - r);
            il.add(new InsnNode(Opcodes.IUSHR));
            il.add(new InsnNode(Opcodes.IOR));
        }

        /** 一条边的随机非线性常数。 */
        int[] newEdge() {
            return new int[] {
                    rnd.nextInt(),      // [0] e0
                    rnd.nextInt() | 1,  // [1] ae 奇数
                    rnd.nextInt(),      // [2] be
                    rnd.nextInt() | 1,  // [3] ce 奇数
                    rnd.nextInt(),      // [4] de
                    1 + rnd.nextInt(31) // [5] r 旋转位数
            };
        }

        /**
         * 块内转移：消费当前 x/y/z/c，把三寄存器推进到目标 key=K 的不变量态。
         * 这是“每个基本块在块内动态计算下一状态”的实体。
         */
        void commit(InsnList il, int destKey) {
            int[] e = newEdge();
            // y' = rotl(x ^ e0, r) + y*ae + be ^ z ^ Hx(c) ^ (K*ce + de)
            il.add(new VarInsnNode(Opcodes.ILOAD, xS));
            pushInt(il, e[0]);
            il.add(new InsnNode(Opcodes.IXOR));
            emitRotl(il, e[5]);
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            pushInt(il, e[1]);
            il.add(new InsnNode(Opcodes.IMUL));
            il.add(new InsnNode(Opcodes.IADD));
            pushInt(il, e[2]);
            il.add(new InsnNode(Opcodes.IADD));
            il.add(new VarInsnNode(Opcodes.ILOAD, zS));
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitHx(il);
            il.add(new InsnNode(Opcodes.IXOR));
            pushInt(il, destKey);
            pushInt(il, e[3]);
            il.add(new InsnNode(Opcodes.IMUL));
            pushInt(il, e[4]);
            il.add(new InsnNode(Opcodes.IADD));
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ISTORE, yS));

            // z' = (y'*P + Q*K) ^ Hz(c)
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            pushInt(il, P);
            il.add(new InsnNode(Opcodes.IMUL));
            pushInt(il, Q);
            pushInt(il, destKey);
            il.add(new InsnNode(Opcodes.IMUL));
            il.add(new InsnNode(Opcodes.IADD));
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitHz(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ISTORE, zS));

            // x' = K ^ H0(c) ^ H1(y')
            pushInt(il, destKey);
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitH0(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            emitH1(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ISTORE, xS));
        }

        /** 块尾路由：写三寄存器后回随机分发器。 */
        void commitAndDispatch(InsnList il, int destKey) {
            commit(il, destKey);
            il.add(new JumpInsnNode(Opcodes.GOTO,
                    dispatchLabels[rnd.nextInt(dispatchLabels.length)]));
        }

        /** k1 = x ^ H0(c) ^ H1(y)（栈：[]→[k1]）。 */
        private void emitK1(InsnList il) {
            il.add(new VarInsnNode(Opcodes.ILOAD, xS));
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitH0(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            emitH1(il);
            il.add(new InsnNode(Opcodes.IXOR));
        }

        /** k2 = (z ^ Hz(c) - y*P) * qInv（栈：[]→[k2]）。 */
        private void emitK2(InsnList il) {
            il.add(new VarInsnNode(Opcodes.ILOAD, zS));
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitHz(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            pushInt(il, P);
            il.add(new InsnNode(Opcodes.IMUL));
            il.add(new InsnNode(Opcodes.ISUB));
            pushInt(il, qInv);
            il.add(new InsnNode(Opcodes.IMUL));
        }

        /**
         * 互锁校验：k1 ^ k2 != 0 → exit 陷阱。variant 控制比较形态，
         * 破坏“所有分发器长得一模一样”的特征。
         */
        void emitGuard(InsnList il, int variant) {
            emitK1(il);
            emitK2(il);
            il.add(new InsnNode(Opcodes.IXOR));
            if ((variant & 1) == 0) {
                il.add(new JumpInsnNode(Opcodes.IFNE, exit));
            } else {
                LabelNode ok = new LabelNode();
                il.add(new JumpInsnNode(Opcodes.IFEQ, ok));
                il.add(new JumpInsnNode(Opcodes.GOTO, exit));
                il.add(ok);
            }
        }

        /** 发射一份分发器（互锁校验 + LOOKUPSWITCH）。 */
        void emitDispatcher(InsnList il, int variant, int[] switchKeys,
                            LabelNode[] switchLabels) {
            emitGuard(il, variant);
            emitK1(il);
            il.add(new LookupSwitchInsnNode(exit,
                    switchKeys.clone(), switchLabels.clone()));
        }

        /** 序言：给定 ctxSeed/y0/首 key，建立满足不变量的三寄存器初值。 */
        void emitInit(InsnList il, int ctxSeed, int y0, int firstKey) {
            pushInt(il, ctxSeed);
            il.add(new VarInsnNode(Opcodes.ISTORE, cS));
            pushInt(il, y0);
            il.add(new VarInsnNode(Opcodes.ISTORE, yS));
            // z = (y*P + Q*K) ^ Hz(c)
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            pushInt(il, P);
            il.add(new InsnNode(Opcodes.IMUL));
            pushInt(il, Q);
            pushInt(il, firstKey);
            il.add(new InsnNode(Opcodes.IMUL));
            il.add(new InsnNode(Opcodes.IADD));
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitHz(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ISTORE, zS));
            // x = K ^ H0(c) ^ H1(y)
            pushInt(il, firstKey);
            il.add(new VarInsnNode(Opcodes.ILOAD, cS));
            emitH0(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ILOAD, yS));
            emitH1(il);
            il.add(new InsnNode(Opcodes.IXOR));
            il.add(new VarInsnNode(Opcodes.ISTORE, xS));
        }

        // ---- 纯 Java 参考模型：构造时自检不变量/转移/双派生闭环 ----
        private static int h0(int c, int s, int m, int b) {
            return ((c ^ (c >>> s)) * m) + b;
        }

        private static int hz(int c, int m, int b) {
            return c * m + b;
        }

        private static int hx(int c, int s, int m) {
            return (c ^ (c >>> s)) * m;
        }

        private static int h1(int v, int s) {
            return v ^ (v >>> s);
        }

        private static int rotl(int v, int r) {
            return (v << r) | (v >>> (32 - r));
        }

        private void selfTest() {
            int c = 0x12345678;
            int y = rnd.nextInt();
            int k = rnd.nextInt();
            int z = (y * P + Q * k) ^ hz(c, mz, bz);
            int x = k ^ h0(c, sH0, m0, b0) ^ h1(y, sH1);
            for (int i = 0; i < 400; i++) {
                int k1 = x ^ h0(c, sH0, m0, b0) ^ h1(y, sH1);
                int k2 = ((z ^ hz(c, mz, bz)) - y * P) * qInv;
                if (k1 != k || k2 != k) {
                    throw new IllegalStateException("state machine invariant");
                }
                int kn = rnd.nextInt();
                int e0 = rnd.nextInt(), ae = rnd.nextInt() | 1, be = rnd.nextInt();
                int ce = rnd.nextInt() | 1, de = rnd.nextInt(), rr = 1 + rnd.nextInt(31);
                // 真实执行序：case 入口校验后，体内数据流探针先喂养 ctx，
                // 块尾 commit 读到的是“变异后的 c”——故 c 的演化必须先于转移
                c = (c * (rnd.nextInt() | 1) + rnd.nextInt()) ^ rnd.nextInt();
                // 与 commit() 完全同序
                int yn = rotl(x ^ e0, rr) + y * ae + be;
                yn = yn ^ z ^ hx(c, sHx, mx);
                yn = yn ^ (kn * ce + de);
                int zn = (yn * P + Q * kn) ^ hz(c, mz, bz);
                int xn = kn ^ h0(c, sH0, m0, b0) ^ h1(yn, sH1);
                y = yn; z = zn; x = xn; k = kn;
            }
        }
    }

    /** 扁平化状态机中的一个 case：真实块 / 桥接块 / 死诱饵。 */
    private static final class StateCase {
        final LabelNode label = new LabelNode();
        final int kind; // 0=real 1=bridge 2=dead
        final int block; // real: 基本块下标；否则 -1
        int key;
        InsnList body;

        StateCase(int kind, int block) {
            this.kind = kind;
            this.block = block;
        }
    }

    private static boolean flattenMethod(MethodNode mn, Random random, InsnList liftPrologue,
                                         Machine mac, Set<AbstractInsnNode> cutAnchors) {
        if (mn.instructions == null || mn.instructions.size() == 0) {
            return false;
        }
        AbstractInsnNode[] insns = mn.instructions.toArray();

        // 1. 扫描：收集跳转/switch 目标、确认无违禁指令
        Set<LabelNode> jumpTargets =
                Collections.newSetFromMap(new java.util.IdentityHashMap<LabelNode, Boolean>());
        for (AbstractInsnNode n : insns) {
            int op = n.getOpcode();
            switch (n.getType()) {
                case AbstractInsnNode.JUMP_INSN:
                    if (op == Opcodes.JSR) {
                        return false;
                    }
                    jumpTargets.add(((JumpInsnNode) n).label);
                    break;
                case AbstractInsnNode.TABLESWITCH_INSN: {
                    TableSwitchInsnNode ts = (TableSwitchInsnNode) n;
                    jumpTargets.add(ts.dflt);
                    for (LabelNode l : ts.labels) {
                        jumpTargets.add(l);
                    }
                    break;
                }
                case AbstractInsnNode.LOOKUPSWITCH_INSN: {
                    LookupSwitchInsnNode ls = (LookupSwitchInsnNode) n;
                    jumpTargets.add(ls.dflt);
                    for (LabelNode l : ls.labels) {
                        jumpTargets.add(l);
                    }
                    break;
                }
                default:
                    if (op == Opcodes.RET) {
                        return false;
                    }
            }
        }
        int[] junkSlots = mac.junkSlots;

        // 2. 切分基本块（跳转目标 + 栈 0 切碎锚点都是 leader）
        List<List<AbstractInsnNode>> blocks = new ArrayList<List<AbstractInsnNode>>();
        List<AbstractInsnNode> cur = null;
        boolean expectLeader = true;
        for (AbstractInsnNode n : insns) {
            int type = n.getType();
            if (type == AbstractInsnNode.FRAME || type == AbstractInsnNode.LINE) {
                continue;
            }
            boolean leader = expectLeader
                    || (type == AbstractInsnNode.LABEL && jumpTargets.contains(n))
                    || cutAnchors.contains(n);
            if (cur == null || leader) {
                cur = new ArrayList<AbstractInsnNode>();
                blocks.add(cur);
            }
            cur.add(n);
            expectLeader = isTerminator(n.getOpcode());
        }
        int blockCount = blocks.size();
        if (blockCount < 1 || blockCount > 6000) {
            return false;
        }

        // 3. 标签 -> 所属基本块
        Map<LabelNode, Integer> owner = new HashMap<LabelNode, Integer>();
        for (int i = 0; i < blockCount; i++) {
            for (AbstractInsnNode n : blocks.get(i)) {
                if (n instanceof LabelNode) {
                    owner.put((LabelNode) n, i);
                }
            }
        }

        // 4. 建立真实状态与死诱饵状态（key 全局唯一）
        Set<Integer> usedKeys = new HashSet<Integer>();
        List<StateCase> cases = new ArrayList<StateCase>();
        StateCase[] realCase = new StateCase[blockCount];
        for (int b = 0; b < blockCount; b++) {
            StateCase sc = new StateCase(0, b);
            assignKey(sc, random, usedKeys);
            realCase[b] = sc;
            cases.add(sc);
        }
        int deadCount = DEAD_MIN + random.nextInt(DEAD_MAX - DEAD_MIN + 1);
        List<StateCase> deadCases = new ArrayList<StateCase>();
        for (int d = 0; d < deadCount; d++) {
            StateCase sc = new StateCase(2, -1);
            assignKey(sc, random, usedKeys);
            deadCases.add(sc);
            cases.add(sc);
        }

        LabelNode exit = new LabelNode();
        LabelNode[] dispatchLabels = new LabelNode[DISPATCHERS];
        for (int i = 0; i < DISPATCHERS; i++) {
            dispatchLabels[i] = new LabelNode();
        }
        mac.exit = exit;
        mac.dispatchLabels = dispatchLabels;

        // 桥接数量上限（与 eligible 估算口径一致）
        int bridgeCap = (int) ((long) blockCount * 125L / 100L * 41L / 100L) + 4;
        int[] bridgeMade = { 0 };

        // 5. 先构建真实状态的方法体（创建桥接状态）
        for (int b = 0; b < blockCount; b++) {
            StateCase sc = realCase[b];
            sc.body = buildRealBody(b, blocks.get(b), owner, realCase, blockCount,
                    mac, cases, usedKeys, bridgeMade, bridgeCap);
        }
        // 6. 死诱饵体（有限循环 + 分叉）。部分诱饵互相形成闭环，
        // 其余才指向真实状态；所有这些状态都没有真实边可达，
        // 因而不会改变业务语义，却让 CFG 不再是“死块 -> 真实块”的单层形状。
        for (int d = 0; d < deadCases.size(); d++) {
            StateCase victim;
            if (deadCases.size() > 1 && random.nextInt(100) < 65) {
                victim = deadCases.get((d + 1) % deadCases.size());
            } else {
                victim = realCase[random.nextInt(blockCount)];
            }
            deadCases.get(d).body = buildDeadBody(mac, victim);
        }

        // 7. 物理发射顺序：全部状态同池打乱
        List<Integer> emitOrder = new ArrayList<Integer>();
        for (int i = 0; i < cases.size(); i++) {
            emitOrder.add(i);
        }
        Collections.shuffle(emitOrder, random);

        // 8. LOOKUPSWITCH 的 (key -> case) 表，按 key 升序，两份分发器共用
        int[] switchKeys = new int[cases.size()];
        LabelNode[] switchLabels = new LabelNode[cases.size()];
        List<StateCase> sortedCases = new ArrayList<StateCase>(cases);
        Collections.sort(sortedCases, new java.util.Comparator<StateCase>() {
            @Override
            public int compare(StateCase a, StateCase b) {
                return Integer.compare(a.key, b.key);
            }
        });
        for (int i = 0; i < sortedCases.size(); i++) {
            switchKeys[i] = sortedCases.get(i).key;
            switchLabels[i] = sortedCases.get(i).label;
        }

        InsnList out = new InsnList();
        // 局部变量提升序言（建 Object[]、参数装箱）必须最先执行
        if (liftPrologue != null) {
            out.add(liftPrologue);
        }
        // 垃圾槽初始化（int，保证所有 case 合并帧中垃圾槽已赋值）
        for (int js : junkSlots) {
            pushInt(out, random.nextInt(64) - 32);
            out.add(new VarInsnNode(Opcodes.ISTORE, js));
        }
        // 三寄存器初态（x/y/z 满足首 key 不变量），随后两份互锁分发器
        mac.emitInit(out, random.nextInt(), random.nextInt(), realCase[0].key);
        for (int d = 0; d < DISPATCHERS; d++) {
            out.add(dispatchLabels[d]);
            mac.emitDispatcher(out, d, switchKeys, switchLabels);
        }

        // 9. 发射全部状态
        for (int idx : emitOrder) {
            StateCase sc = cases.get(idx);
            out.add(sc.label);
            out.add(sc.body);
        }

        // 兜底出口（寄存器被剥离/篡改时互锁校验实际可达：直接 NPE 跑飞）
        out.add(exit);
        out.add(new InsnNode(Opcodes.ACONST_NULL));
        out.add(new InsnNode(Opcodes.ATHROW));

        // 后置体量护栏：eligible() 是前置保守估算，这里按实际指令再核一遍，
        // 防 fork/桥接随机波动把 Code 属性撑过 64KB（返回 false 时方法保留
        // 归一化+提升后的语义等价形态，仅不计入平坦化数）
        if (estimateCodeBytes(out) > 60000) {
            return false;
        }

        // 10. 替换方法体；旧局部变量调试属性引用的位置已失效，一并清除
        mn.instructions = out;
        mn.tryCatchBlocks = new ArrayList<org.objectweb.asm.tree.TryCatchBlockNode>();
        mn.localVariables = null;
        mn.visibleLocalVariableAnnotations = null;
        mn.invisibleLocalVariableAnnotations = null;
        return true;
    }

    /**
     * 保守估算 InsnList 落地后的 Code 属性字节数（指令 + 每个标签一份
     * StackMapTable 帧的余量），仅用于 64KB 后置护栏，不追求精确。
     */
    private static int estimateCodeBytes(InsnList il) {
        int total = 0;
        for (AbstractInsnNode n : il.toArray()) {
            switch (n.getType()) {
                case AbstractInsnNode.LABEL:
                    total += 9; // 标签自身 0 字节 + 栈帧约 8 字节余量
                    break;
                case AbstractInsnNode.LINE:
                case AbstractInsnNode.FRAME:
                    break;
                case AbstractInsnNode.INT_INSN:
                    total += 3;
                    break;
                case AbstractInsnNode.VAR_INSN:
                    total += 2;
                    break;
                case AbstractInsnNode.IINC_INSN:
                    total += 3;
                    break;
                case AbstractInsnNode.LDC_INSN:
                    total += 3;
                    break;
                case AbstractInsnNode.JUMP_INSN:
                    total += 8; // 短跳转 3，远跳转 5/8，取悲观值
                    break;
                case AbstractInsnNode.FIELD_INSN:
                case AbstractInsnNode.METHOD_INSN:
                case AbstractInsnNode.TYPE_INSN:
                case AbstractInsnNode.INVOKE_DYNAMIC_INSN:
                    total += 5;
                    break;
                case AbstractInsnNode.MULTIANEWARRAY_INSN:
                    total += 4;
                    break;
                case AbstractInsnNode.TABLESWITCH_INSN: {
                    TableSwitchInsnNode ts = (TableSwitchInsnNode) n;
                    total += 16 + 4 * (ts.max - ts.min + 2);
                    break;
                }
                case AbstractInsnNode.LOOKUPSWITCH_INSN: {
                    LookupSwitchInsnNode ls = (LookupSwitchInsnNode) n;
                    total += 9 + 8 * (ls.keys.size() + 1);
                    break;
                }
                default:
                    total += 1;
            }
        }
        return total;
    }

    /** 随机生成全局唯一的 32 位 key。 */
    private static void assignKey(StateCase sc, Random random, Set<Integer> usedKeys) {
        for (int tries = 0; tries < 128; tries++) {
            int k = random.nextInt();
            if (!usedKeys.contains(k)) {
                sc.key = k;
                usedKeys.add(k);
                return;
            }
        }
        int k = usedKeys.size() + 1;
        while (usedKeys.contains(k)) {
            k++;
        }
        sc.key = k;
        usedKeys.add(k);
    }

    /**
     * 真实基本块 -> case 体：
     * 随机块内垃圾前缀 + 原指令（含数据流探针，终结指令除外）+ 终结语义改写。
     */
    private static InsnList buildRealBody(int b,
                                          List<AbstractInsnNode> body,
                                          Map<LabelNode, Integer> owner,
                                          StateCase[] realCase, int blockCount,
                                          Machine mac,
                                          List<StateCase> allCases,
                                          Set<Integer> usedKeys, int[] bridgeMade,
                                          int bridgeCap) {
        InsnList out = new InsnList();
        Random random = mac.rnd;
        int[] junkSlots = mac.junkSlots;

        // 块内垃圾：35% 概率插入 1-2 段纯 int 垃圾（10% 概率含极短循环）
        if (random.nextInt(100) < 35) {
            int snippets = 1 + random.nextInt(2);
            for (int s = 0; s < snippets; s++) {
                if (random.nextInt(100) < 10) {
                    emitJunkLoop(out, random, junkSlots);
                } else {
                    emitJunkStmt(out, random, junkSlots);
                }
            }
        }

        AbstractInsnNode last = body.get(body.size() - 1);
        int lastOp = last.getOpcode();
        int copyEnd = isTerminator(lastOp) ? body.size() - 1 : body.size();
        for (int i = 0; i < copyEnd; i++) {
            out.add(body.get(i));
        }

        if (lastOp == Opcodes.GOTO) {
            Integer target = owner.get(((JumpInsnNode) last).label);
            if (target == null) {
                throw new IllegalStateException("orphan goto target");
            }
            emitEdge(out, realCase[target], true, mac,
                    allCases, usedKeys, bridgeMade, bridgeCap);
        } else if (lastOp == Opcodes.TABLESWITCH) {
            // 原 switch 留在 case 体内执行（栈中性），但跳转目标全部换成块内
            // 新建桩标签：桩内先 commit 到真实后继再分发，状态机不断链
            TableSwitchInsnNode ts = (TableSwitchInsnNode) last;
            int nLabs = ts.labels.size();
            LabelNode[] stubs = new LabelNode[nLabs + 1];
            for (int i = 0; i <= nLabs; i++) {
                stubs[i] = new LabelNode();
            }
            List<LabelNode> switched = new ArrayList<LabelNode>();
            for (int i = 0; i < nLabs; i++) {
                switched.add(stubs[i]);
            }
            // default 单独传，不进 labels 数组（长度须恰为 max-min+1）
            out.add(new TableSwitchInsnNode(ts.min, ts.max, stubs[nLabs],
                    switched.toArray(new LabelNode[0])));
            for (int i = 0; i < nLabs; i++) {
                Integer t = owner.get(ts.labels.get(i));
                if (t == null) {
                    throw new IllegalStateException("orphan tableswitch target");
                }
                out.add(stubs[i]);
                emitEdge(out, realCase[t], true, mac,
                        allCases, usedKeys, bridgeMade, bridgeCap);
            }
            Integer dt = owner.get(ts.dflt);
            if (dt == null) {
                throw new IllegalStateException("orphan tableswitch default");
            }
            out.add(stubs[nLabs]);
            emitEdge(out, realCase[dt], true, mac,
                    allCases, usedKeys, bridgeMade, bridgeCap);
        } else if (lastOp == Opcodes.LOOKUPSWITCH) {
            // 同上（源码 int switch 稀疏形态 / String switch 的两层 switch 均走此路）
            LookupSwitchInsnNode ls = (LookupSwitchInsnNode) last;
            int nLabs = ls.labels.size();
            LabelNode[] stubs = new LabelNode[nLabs + 1];
            for (int i = 0; i <= nLabs; i++) {
                stubs[i] = new LabelNode();
            }
            List<LabelNode> switched = new ArrayList<LabelNode>();
            for (int i = 0; i < nLabs; i++) {
                switched.add(stubs[i]);
            }
            int[] keys = new int[ls.keys.size()];
            for (int i = 0; i < keys.length; i++) {
                keys[i] = ls.keys.get(i).intValue();
            }
            out.add(new LookupSwitchInsnNode(stubs[nLabs], keys,
                    switched.toArray(new LabelNode[0])));
            for (int i = 0; i < nLabs; i++) {
                Integer t = owner.get(ls.labels.get(i));
                if (t == null) {
                    throw new IllegalStateException("orphan lookupswitch target");
                }
                out.add(stubs[i]);
                emitEdge(out, realCase[t], true, mac,
                        allCases, usedKeys, bridgeMade, bridgeCap);
            }
            Integer dt = owner.get(ls.dflt);
            if (dt == null) {
                throw new IllegalStateException("orphan lookupswitch default");
            }
            out.add(stubs[nLabs]);
            emitEdge(out, realCase[dt], true, mac,
                    allCases, usedKeys, bridgeMade, bridgeCap);
        } else if (isIf(lastOp)) {
            if (b + 1 >= blockCount) {
                throw new IllegalStateException("conditional block without successor");
            }
            Integer trueTarget = owner.get(((JumpInsnNode) last).label);
            if (trueTarget == null) {
                throw new IllegalStateException("orphan if target");
            }
            LabelNode trueLab = new LabelNode();
            out.add(new JumpInsnNode(lastOp, trueLab));
            emitEdge(out, realCase[b + 1], true, mac,
                    allCases, usedKeys, bridgeMade, bridgeCap);
            out.add(trueLab);
            emitEdge(out, realCase[trueTarget], true, mac,
                    allCases, usedKeys, bridgeMade, bridgeCap);
        } else if (isReturn(lastOp)) {
            // 出口指令原样留在 case 内
            out.add(last);
        } else {
            if (b + 1 < blockCount) {
                emitEdge(out, realCase[b + 1], true, mac,
                        allCases, usedKeys, bridgeMade, bridgeCap);
            } else {
                out.add(new JumpInsnNode(Opcodes.GOTO, mac.exit));
            }
        }
        return out;
    }

    /** 死诱饵体：垃圾分叉 + 有限循环 + 指向随机真实状态的转移（永不执行）。 */
    private static InsnList buildDeadBody(Machine mac, StateCase victim) {
        InsnList out = new InsnList();
        Random random = mac.rnd;
        int[] junkSlots = mac.junkSlots;
        int stmts = 2 + random.nextInt(3);
        for (int i = 0; i < stmts; i++) {
            emitJunkStmt(out, random, junkSlots);
        }
        emitJunkLoop(out, random, junkSlots);
        emitJunkStmt(out, random, junkSlots);
        // 结尾的转移只使用简单路由（不再衍生桥接/分叉）
        emitMechanism(out, victim, mac);
        return out;
    }

    /**
     * 发射一条控制流边：随机 0-2 层桥接，外层随机包一层不透明谓词分叉。
     * 两条分叉路径与桥接结尾都最终落在 dest；垃圾语句只写垃圾槽、寄存器
     * 不变量只在结尾的转移里重建，故两条路径都合法收敛到目标态。
     */
    private static void emitEdge(InsnList out, StateCase dest, boolean allowFork,
                                 Machine mac,
                                 List<StateCase> allCases,
                                 Set<Integer> usedKeys, int[] bridgeMade, int bridgeCap) {
        Random random = mac.rnd;
        int[] junkSlots = mac.junkSlots;
        // 桥接链：从后往前构造，first 为本边实际跳转目标
        StateCase first = dest;
        if (bridgeMade[0] < bridgeCap) {
            int roll = random.nextInt(100);
            int depth = roll < 25 ? 1 : (roll < 33 ? 2 : 0);
            depth = Math.min(depth, bridgeCap - bridgeMade[0]);
            StateCase next = dest;
            for (int i = 0; i < depth; i++) {
                StateCase bridge = new StateCase(1, -1);
                assignKey(bridge, random, usedKeys);
                InsnList bb = new InsnList();
                emitJunkStmt(bb, random, junkSlots);
                if (random.nextInt(100) < 30) {
                    emitJunkStmt(bb, random, junkSlots);
                }
                emitMechanism(bb, next, mac);
                bridge.body = bb;
                allCases.add(bridge);
                bridgeMade[0]++;
                next = bridge;
            }
            first = next;
        }

        if (allowFork && random.nextInt(100) < 45) {
            LabelNode fakeLab = new LabelNode();
            emitOpaqueZero(out, random, junkSlots);
            out.add(new JumpInsnNode(Opcodes.IFEQ, fakeLab));
            // 恒为 0 -> 恒跳 fake；真路径永不执行但结构完整
            mac.commitAndDispatch(out, first.key);
            out.add(fakeLab);
            emitJunkStmt(out, random, junkSlots);
            if (random.nextInt(100) < 50) {
                mac.commitAndDispatch(out, first.key);
            } else {
                // 直达 GOTO：本 case 体内探针可能已喂养 ctx，寄存器此刻对的是
                // 旧 c，不能在此互锁校验；case 体不消费 key，下一次 commit
                // 会把三寄存器整体重置到目标不变量，故直达安全
                out.add(new JumpInsnNode(Opcodes.GOTO, first.label));
            }
        } else {
            emitMechanism(out, first, mac);
        }
    }

    /**
     * 单步路由：35% 直接 GOTO 目标 case（不经过分发器；case 体不读 key，
     * 完整性由下一次 commit + 分发器互锁兜底），65% 块内 commit 后回分发器。
     */
    private static void emitMechanism(InsnList out, StateCase dest, Machine mac) {
        if (mac.rnd.nextInt(100) < 35) {
            out.add(new JumpInsnNode(Opcodes.GOTO, dest.label));
        } else {
            mac.commitAndDispatch(out, dest.key);
        }
    }

    /**
     * 在栈顶留下一个恒为 0 的 int（供 IFEQ 使用），形式随机，
     * 全部读取已初始化的垃圾槽，无方法调用/除法/数组访问。
     */
    private static void emitOpaqueZero(InsnList out, Random random, int[] junkSlots) {
        int s = junkSlots[random.nextInt(junkSlots.length)];
        int recipe = random.nextInt(3);
        if (recipe == 0) {
            // (s*s - s) & 1 == 0
            out.add(new VarInsnNode(Opcodes.ILOAD, s));
            out.add(new VarInsnNode(Opcodes.ILOAD, s));
            out.add(new InsnNode(Opcodes.IMUL));
            out.add(new VarInsnNode(Opcodes.ILOAD, s));
            out.add(new InsnNode(Opcodes.ISUB));
            out.add(new InsnNode(Opcodes.ICONST_1));
            out.add(new InsnNode(Opcodes.IAND));
        } else if (recipe == 1) {
            // (s | 1) ^ (s | 1) == 0
            out.add(new VarInsnNode(Opcodes.ILOAD, s));
            out.add(new InsnNode(Opcodes.ICONST_1));
            out.add(new InsnNode(Opcodes.IOR));
            out.add(new VarInsnNode(Opcodes.ILOAD, s));
            out.add(new InsnNode(Opcodes.ICONST_1));
            out.add(new InsnNode(Opcodes.IOR));
            out.add(new InsnNode(Opcodes.IXOR));
        } else {
            // (a + b) - (a + b) == 0
            int a = random.nextInt(48) - 24;
            int b = random.nextInt(48) - 24;
            pushInt(out, a);
            pushInt(out, b);
            out.add(new InsnNode(Opcodes.IADD));
            pushInt(out, a);
            pushInt(out, b);
            out.add(new InsnNode(Opcodes.IADD));
            out.add(new InsnNode(Opcodes.ISUB));
        }
    }

    /**
     * 一条栈平衡的纯 int 垃圾语句，随机形态：
     * 常量赋值 / 算术写回 / 分叉重汇（两条路径写不同垃圾值）。
     * 只写垃圾槽，绝不触碰真实数组槽、状态槽与 ctx 槽。
     */
    private static void emitJunkStmt(InsnList out, Random random, int[] js) {
        int form = random.nextInt(3);
        int dst = js[random.nextInt(js.length)];
        if (form == 0) {
            pushInt(out, random.nextInt(2048) - 1024);
            out.add(new VarInsnNode(Opcodes.ISTORE, dst));
            return;
        }
        if (form == 1) {
            out.add(new VarInsnNode(Opcodes.ILOAD, js[random.nextInt(js.length)]));
            int op;
            int c;
            switch (random.nextInt(7)) {
                case 0: op = Opcodes.IADD; c = random.nextInt(64) - 32; break;
                case 1: op = Opcodes.ISUB; c = random.nextInt(64) - 32; break;
                case 2: op = Opcodes.IMUL; c = random.nextInt(16) + 1; break;
                case 3: op = Opcodes.IXOR; c = random.nextInt(65536); break;
                case 4: op = Opcodes.IAND; c = random.nextInt(65536); break;
                case 5: op = Opcodes.IOR;  c = random.nextInt(65536); break;
                default: op = Opcodes.ISHL; c = random.nextInt(16); break;
            }
            pushInt(out, c);
            out.add(new InsnNode(op));
            out.add(new VarInsnNode(Opcodes.ISTORE, dst));
            return;
        }
        // 分叉重汇：比较结果无关紧要，两个出口都只是往垃圾槽写 int
        LabelNode lab = new LabelNode();
        LabelNode join = new LabelNode();
        out.add(new VarInsnNode(Opcodes.ILOAD, js[random.nextInt(js.length)]));
        pushInt(out, random.nextInt(128) - 64);
        int[] ifs = {
                Opcodes.IF_ICMPEQ, Opcodes.IF_ICMPNE, Opcodes.IF_ICMPLT,
                Opcodes.IF_ICMPGE, Opcodes.IF_ICMPGT, Opcodes.IF_ICMPLE
        };
        out.add(new JumpInsnNode(ifs[random.nextInt(ifs.length)], lab));
        pushInt(out, random.nextInt(2048) - 1024);
        out.add(new VarInsnNode(Opcodes.ISTORE, dst));
        out.add(new JumpInsnNode(Opcodes.GOTO, join));
        out.add(lab);
        pushInt(out, random.nextInt(2048) - 1024);
        out.add(new VarInsnNode(Opcodes.ISTORE, dst));
        out.add(join);
    }

    /**
     * 极短有限循环：j = 2..5; do { 垃圾语句 } while (--j >= 0)。
     * 循环次数上界 6，循环槽固定用最后一个垃圾槽，循环体不写该槽。
     */
    private static void emitJunkLoop(InsnList out, Random random, int[] js) {
        int counter = js[js.length - 1];
        int[] inner = new int[js.length - 1];
        System.arraycopy(js, 0, inner, 0, inner.length);
        pushInt(out, 2 + random.nextInt(4));
        out.add(new VarInsnNode(Opcodes.ISTORE, counter));
        LabelNode top = new LabelNode();
        out.add(top);
        int body = 1 + random.nextInt(2);
        for (int i = 0; i < body; i++) {
            emitJunkStmtFixedSlots(out, random, inner);
        }
        out.add(new IincInsnNode(counter, -1));
        out.add(new VarInsnNode(Opcodes.ILOAD, counter));
        out.add(new JumpInsnNode(Opcodes.IFGE, top));
    }

    /** emitJunkStmt 的“只用指定槽子集”版本（供循环体避开循环计数器）。 */
    private static void emitJunkStmtFixedSlots(InsnList out, Random random, int[] js) {
        if (js.length == 0) {
            return;
        }
        int saved = js[random.nextInt(js.length)];
        int form = random.nextInt(2);
        int dst = js[random.nextInt(js.length)];
        if (form == 0) {
            pushInt(out, random.nextInt(2048) - 1024);
            out.add(new VarInsnNode(Opcodes.ISTORE, dst));
            return;
        }
        out.add(new VarInsnNode(Opcodes.ILOAD, saved));
        pushInt(out, random.nextInt(32) + 1);
        out.add(new InsnNode(random.nextBoolean() ? Opcodes.IMUL : Opcodes.IXOR));
        out.add(new VarInsnNode(Opcodes.ISTORE, dst));
    }

    private static boolean isTerminator(int op) {
        return op == Opcodes.GOTO || isIf(op) || isReturn(op)
                || op == Opcodes.TABLESWITCH || op == Opcodes.LOOKUPSWITCH;
    }

    private static boolean isIf(int op) {
        return (op >= Opcodes.IFEQ && op <= Opcodes.IF_ACMPNE)
                || op == Opcodes.IFNULL || op == Opcodes.IFNONNULL;
    }

    private static boolean isReturn(int op) {
        return op == Opcodes.IRETURN || op == Opcodes.LRETURN || op == Opcodes.FRETURN
                || op == Opcodes.DRETURN || op == Opcodes.ARETURN || op == Opcodes.RETURN
                || op == Opcodes.ATHROW;
    }

    /** 用最短的指令序列把 int 常量压栈。 */
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
