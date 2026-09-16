package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.IincInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.InvokeDynamicInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

/**
 * 跨类代码派分（方法体拆解到其他类）：
 *
 * 控制流平坦化只改变方法<b>内部</b>的形态，反编译后业务调用序列
 * （new X、invoke 业务方法、字段读写）仍集中在原方法里可见。本变换在
 * 改名完成后、逐类变换之前的<b>全局阶段</b>执行：把每个方法在栈深 0
 * 边界切成直线语句片段，随机派发到其他类中新生成的
 * {@code public static synthetic void m(Object[])} 方法里，原位置只留
 * 一次跨类调用 + Object[] 组包/拆包：
 *
 * <pre>
 *   list.add(new Color(...));      Object[] a = { list, ... };
 *   calc(panel, 7);          →     o.a.hq.k(a);
 *   square = panel;                Object[] b = { panel };
 *                                  o.a.mz.x(b); square = (..) b[0];
 * </pre>
 *
 * 派发生成的外提方法随宿主类走完整逐类变换管线（字符串/数字混淆、
 * 垃圾注入、三寄存器状态机平坦化、不透明谓词），与宿主类原生方法
 * 真假同构；原方法被掏空后同样被平坦化。关键逻辑因此被拆碎散落到
 * 数十个类中，单看任何一个类都拼不出原方法。
 *
 * 局部变量桥接：片段读写的局部槽在调用点装箱进 Object[]，外提方法内
 * 通过数组下标读回（按 SimpleVerifier 精确帧插 CHECKCAST/拆箱），
 * 写值经数组返回后拆箱写回原槽，语义完全保持。
 *
 * 安全护栏：只搬栈空中性、无跳转/标签/异常表/monitor/返回的直线片段；
 * 跨类成员访问按包/访问标志校验（private 拒绝，跨包仅 public）；
 * 全部片段先规划校验后统一改字节码，任何异常整体放弃、节点原样。
 */
public final class CrossClassOutliner {

    /** 单个源方法每构建最多派分的片段数。 */
    private static final int MAX_OUT_PER_SOURCE = 28;
    /** 单个宿主类最多接收的外提方法数（控常量池/方法体膨胀）。 */
    private static final int MAX_OUT_PER_HOST = 6;

    private CrossClassOutliner() {
    }

    /** 统计结果。 */
    public static final class Stats {
        public int segments;
        public int sourceMethods;
        public int hosts;
        /** 实际接收了外提方法的宿主内部名（j2c 需据此排除下沉，避免
         *  宿主被整体下沉后方法体内 NEW 出的簇内 $$n 对象跨边界返给
         *  明文侧触发 ClassCastException）。 */
        public Set<String> hostNames = new HashSet<String>();

        @Override
        public String toString() {
            return segments + " 段代码派分到 " + hosts + " 个类（来自 "
                    + sourceMethods + " 个方法）";
        }
    }

    /** 一个已规划待应用的派分片段。 */
    private static final class Segment {
        ClassNode src;
        MethodNode mn;
        Frame<BasicValue>[] frames;
        int start;
        int end;
        AbstractInsnNode[] snapshot;
        /** 进入片段前需要装箱传入的槽（首次访问为读）。 */
        int[] readSlots;
        Type[] readTypes;
        /** 片段内被写、调用后需要取回的槽。 */
        int[] writeSlots;
        Type[] writeTypes;
        /** 用到的最大槽号（数组长度 = maxSlot+1）。 */
        int maxSlot;
        ClassNode host;
        String hostMethod;
        /** 片段是否含 NEW（外提方法体内出现 NEW..<init>，仅统计用）。 */
        boolean hasNew;
    }

    public static Stats apply(Collection<ClassNode> classes, Set<String> sourceSkip,
                              Set<String> hostAllowed, ClassLoader loader, Random random) {
        return apply(classes, sourceSkip, hostAllowed, null, loader, random);
    }

    /**
     * @param sinkSide j2c 即将整体下沉的类内部名集合。非空时启用两侧隔离：
     *                 源类在下沉侧的片段只派发给下沉侧宿主，源类在明文侧的
     *                 片段只派发给明文侧宿主。否则隐藏/明文边界两侧的
     *                 Object[] 装箱对象类型身份不一致（$$n vs shell），
     *                 运行期 checkcast 触发 ClassCastException。
     */
    public static Stats apply(Collection<ClassNode> classes, Set<String> sourceSkip,
                              Set<String> hostAllowed, Set<String> sinkSide,
                              ClassLoader loader, Random random) {
        final Set<String> sink = sinkSide == null
                ? Collections.<String>emptySet() : sinkSide;
        Stats stats = new Stats();
        Map<String, ClassNode> pool = new LinkedHashMap<String, ClassNode>();
        for (ClassNode cn : classes) {
            pool.put(cn.name, cn);
        }
        Set<String> skip = new HashSet<String>();
        if (sourceSkip != null) {
            skip.addAll(sourceSkip);
        }
        Set<String> allowedHosts = hostAllowed == null
                ? Collections.<String>emptySet() : hostAllowed;

        // 宿主池：可自由添加 public static 方法的普通类。伪代码/诱饵/分发壳
        // 类不做源（合成方法体不可靠），但可以做宿主——迁入的是我们自己
        // 构造的方法体，随该类走完整逐类变换，真实逻辑反而藏进诱饵深处
        List<ClassNode> hosts = new ArrayList<ClassNode>();
        for (ClassNode cn : classes) {
            if (canBeHost(cn, skip, allowedHosts)) {
                hosts.add(cn);
            }
        }
        if (hosts.isEmpty()) {
            return stats;
        }
        Map<String, Integer> hostLoad = new HashMap<String, Integer>();
        for (ClassNode h : hosts) {
            hostLoad.put(h.name, Integer.valueOf(0));
        }

        // 每源方法一组片段；frames 缓存在规划期，应用期改写仍要用
        List<Segment> all = new ArrayList<Segment>();
        for (ClassNode cn : new ArrayList<ClassNode>(classes)) {
            if (skip.contains(cn.name)) {
                continue;
            }
            if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                    | Opcodes.ACC_MODULE)) != 0) {
                continue;
            }
            for (MethodNode mn : new ArrayList<MethodNode>(cn.methods)) {
                if (all.size() >= MAX_OUT_PER_HOST * hosts.size()) {
                    break;
                }
                try {
                    planMethod(cn, mn, pool, hosts, hostLoad, sink,
                            loader, random, all);
                } catch (Throwable t) {
                    // 单方法规划失败放弃该方法，不影响其他方法
                    continue;
                }
            }
        }
        if (all.isEmpty()) {
            return stats;
        }

        // 应用：按源方法分组，组内先摘指令再按源码顺序插回调用点
        Map<MethodNode, List<Segment>> byMethod = new LinkedHashMap<MethodNode, List<Segment>>();
        for (Segment seg : all) {
            List<Segment> list = byMethod.get(seg.mn);
            if (list == null) {
                list = new ArrayList<Segment>();
                byMethod.put(seg.mn, list);
            }
            list.add(seg);
        }
        Set<ClassNode> usedHosts = new HashSet<ClassNode>();
        Set<MethodNode> touchedSources = new HashSet<MethodNode>();
        for (Map.Entry<MethodNode, List<Segment>> e : byMethod.entrySet()) {
            applySegments(e.getKey(), e.getValue(), pool, random);
            touchedSources.add(e.getKey());
            for (Segment seg : e.getValue()) {
                usedHosts.add(seg.host);
            }
        }
        // 兜底：外提后立即对全部类做精确帧验证，若外提破坏类型结构，
        // 抛出后由上层放弃本次外提（SimpleVerifier 对 top 槽合并偏宽松，
        // 不构成完整合法性证明，但能拦住帧结构级破坏）
        for (ClassNode cn : classes) {
            for (MethodNode mn0 : cn.methods) {
                try {
                    Analysis.verify(cn, mn0, loader);
                } catch (Throwable t) {
                    throw new RuntimeException("外提后验证失败 "
                            + cn.name + "." + mn0.name + mn0.desc, t);
                }
            }
        }
        stats.segments = all.size();
        stats.sourceMethods = touchedSources.size();
        stats.hosts = usedHosts.size();
        for (ClassNode h : usedHosts) {
            stats.hostNames.add(h.name);
        }
        return stats;
    }

    private static boolean canBeHost(ClassNode cn, Set<String> skip,
                                     Set<String> hostAllowed) {
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE | Opcodes.ACC_ENUM)) != 0) {
            return false;
        }
        if (hostAllowed.contains(cn.name)) {
            // 诱饵/壳类：显式允许做宿主
            return true;
        }
        return !skip.contains(cn.name);
    }

    // ------------------------------------------------------------------
    // 规划
    // ------------------------------------------------------------------

    private static void planMethod(ClassNode cn, MethodNode mn,
                                    Map<String, ClassNode> pool,
                                    List<ClassNode> hosts,
                                    Map<String, Integer> hostLoad,
                                    Set<String> sink,
                                    ClassLoader loader, Random random,
                                    List<Segment> out) throws Exception {
        if (mn.name.equals("<clinit>")) {
            return; // 静态初始化器派分会引入跨类初始化顺序耦合
        }
        if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE
                | Opcodes.ACC_BRIDGE)) != 0) {
            return;
        }
        if (mn.instructions == null || mn.instructions.size() == 0) {
            return;
        }
        // 有异常表（含 synchronized 隐式表）的方法：搬运改变 handler 覆盖语义
        if (mn.tryCatchBlocks != null && !mn.tryCatchBlocks.isEmpty()) {
            return;
        }
        Frame<BasicValue>[] frames = Analysis.verify(cn, mn, loader);
        if (frames == null) {
            return; // 精确类型拿不到就不做（保守于 CHECKCAST 合法性）
        }
        AbstractInsnNode[] insns = mn.instructions.toArray();

        // 构造器：只搬 super/this 调用之后
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
                return;
            }
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
            if (f != null && f.getStackSize() == 0) {
                anchors.add(Integer.valueOf(i));
            }
        }
        if (anchors.size() < 2) {
            return;
        }

        String srcPkg = packageOf(cn.name);
        // 掷骰一次：本方法多大比例候选被派分（每构建不同）。
        // 高区间随机：既保证派分力度，又让各构建形态有差异
        double chance = 0.78d + random.nextDouble() * 0.22d;
        int made = countOut(out, mn);
        for (int a = 0; a + 1 < anchors.size(); a++) {
            if (made >= MAX_OUT_PER_SOURCE) {
                break;
            }
            int s = anchors.get(a).intValue();
            int e = anchors.get(a + 1).intValue();
            if (random.nextDouble() >= chance) {
                continue;
            }
            // 收窄：片段只取连续真实指令串，截止于第一个 LABEL/FRAME（不含）。
            // javac 为每条语句/行号生成无跳转引用的调试 label，而分支目标 label
            // 与 FRAME 意味着其后是多入口基本块；两种情况统一在 label 前切分，
            // LABEL/FRAME/LINE 一律保留在源方法，片段天然单入口、无控制流
            int re = s;
            while (re < e) {
                int tt = insns[re].getType();
                if (tt == AbstractInsnNode.LABEL || tt == AbstractInsnNode.FRAME) {
                    break;
                }
                re++;
            }
            if (re == s) {
                continue;
            }
            // 净栈效应必须为 0：截断点（label/frame 处）的栈深必须与入口一致。
            // 反例：三目 cond ? "in" : "out" 的 "out" 分支，LDC 压栈发生在本片段、
            // 消费用 ASTORE 却在汇合 label 之后；只搬压栈会让调用点路径栈深 0，
            // 汇合帧却声明栈上有值，COMPUTE_FRAMES 合并矛盾路径直接 AIOOBE
            Frame<BasicValue> fEnd = frames[re];
            if (fEnd == null
                    || fEnd.getStackSize() != frames[s].getStackSize()) {
                continue;
            }
            e = re;
            // requireSamePackage：片段内是否含仅同包可访问的成员
            // deny：含 private/跨包非 public 等无法跨类访问的成员
            int accessNeed = scanAccess(insns, s, e, cn, pool);
            if (accessNeed == ACCESS_DENY) {
                continue;
            }
            if (!isWorthMoving(insns, s, e)) {
                continue;
            }

            // 槽位读写分析
            int localBound = Math.max(mn.maxLocals, Analysis.observedMaxSlot(mn));
            int maxSlot = -1;
            boolean[] written = new boolean[localBound];
            boolean[] readBeforeWrite = new boolean[localBound];
            Type[] lastWriteType = new Type[localBound];
            boolean slotOk = true;
            for (int i = s; i < e; i++) {
                AbstractInsnNode n = insns[i];
                if (n instanceof VarInsnNode) {
                    VarInsnNode v = (VarInsnNode) n;
                    int op = v.getOpcode();
                    int width = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                            || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                    if (v.var + width > localBound) {
                        slotOk = false;
                        break;
                    }
                    maxSlot = Math.max(maxSlot, v.var + width - 1);
                    boolean isLoad = op == Opcodes.ILOAD || op == Opcodes.LLOAD
                            || op == Opcodes.FLOAD || op == Opcodes.DLOAD
                            || op == Opcodes.ALOAD;
                    if (isLoad) {
                        if (!written[v.var]) {
                            readBeforeWrite[v.var] = true;
                        }
                    } else {
                        written[v.var] = true;
                        Frame<BasicValue> bf = frames[i];
                        if (bf != null && bf.getStackSize() > 0) {
                            BasicValue top = bf.getStack(bf.getStackSize() - 1);
                            if (top != null && top.getType() != null) {
                                lastWriteType[v.var] = top.getType();
                            }
                        }
                    }
                } else if (n instanceof IincInsnNode) {
                    IincInsnNode inc = (IincInsnNode) n;
                    if (inc.var >= localBound) {
                        slotOk = false;
                        break;
                    }
                    maxSlot = Math.max(maxSlot, inc.var);
                    if (!written[inc.var]) {
                        readBeforeWrite[inc.var] = true;
                    }
                    written[inc.var] = true;
                    lastWriteType[inc.var] = Type.INT_TYPE;
                }
            }
            if (!slotOk) {
                continue;
            }
            // 读槽：先于首次写就被读的槽；写槽：片段内被写的槽
            List<Integer> rs = new ArrayList<Integer>();
            List<Type> rt = new ArrayList<Type>();
            List<Integer> ws = new ArrayList<Integer>();
            List<Type> wt = new ArrayList<Type>();
            Frame<BasicValue> entry = frames[s];
            for (int slot = 0; slot < localBound; slot++) {
                if (readBeforeWrite[slot]) {
                    Type t = localType(entry, slot);
                    if (t == null) {
                        slotOk = false;
                        break;
                    }
                    rs.add(Integer.valueOf(slot));
                    rt.add(t);
                }
                if (written[slot]) {
                    Type t = lastWriteType[slot];
                    if (t == null) {
                        // 取不到精确写类型时退化为入口槽类型（同槽同类型常态）
                        t = localType(entry, slot);
                    }
                    if (t == null) {
                        slotOk = false;
                        break;
                    }
                    ws.add(Integer.valueOf(slot));
                    wt.add(t);
                }
            }
            if (!slotOk) {
                continue;
            }

            ClassNode host = pickHost(hosts, hostLoad, srcPkg, accessNeed,
                    cn.name, sink, random);
            if (host == null) {
                continue;
            }

            Segment seg = new Segment();
            seg.src = cn;
            seg.mn = mn;
            seg.frames = frames;
            seg.start = s;
            seg.end = e;
            seg.snapshot = insns;
            seg.readSlots = toInts(rs);
            seg.readTypes = rt.toArray(new Type[0]);
            seg.writeSlots = toInts(ws);
            seg.writeTypes = wt.toArray(new Type[0]);
            seg.maxSlot = Math.max(maxSlot, 0);
            for (int i = s; i < e; i++) {
                if (insns[i].getOpcode() == Opcodes.NEW) {
                    seg.hasNew = true;
                    break;
                }
            }
            seg.host = host;
            hostLoad.put(host.name, Integer.valueOf(hostLoad.get(host.name).intValue() + 1));
            out.add(seg);
            made++;
        }
    }

    private static int countOut(List<Segment> all, MethodNode mn) {
        int c = 0;
        for (Segment s : all) {
            if (s.mn == mn) {
                c++;
            }
        }
        return c;
    }

    private static int[] toInts(List<Integer> xs) {
        int[] r = new int[xs.size()];
        for (int i = 0; i < r.length; i++) {
            r[i] = xs.get(i).intValue();
        }
        return r;
    }

    private static Type localType(Frame<BasicValue> f, int slot) {
        if (f == null || slot >= f.getLocals()) {
            return null;
        }
        BasicValue v = f.getLocal(slot);
        if (v == null) {
            return null;
        }
        return v.getType(); // SimpleVerifier 下为精确类型；TOP 时为 null
    }

    // ------------------------------------------------------------------
    // 片段合法性
    // ------------------------------------------------------------------

    private static final int ACCESS_OK = 0;          // 任意宿主
    private static final int ACCESS_SAME_PKG = 1;    // 仅同包宿主
    private static final int ACCESS_DENY = 2;        // 不可派分

    /**
     * 扫描片段的形态合法性与跨类访问需求。
     * 形态：无标签/帧/跳转/switch/返回/异常抛出/monitor；行号节点允许（搬运时丢弃）。
     */
    private static int scanAccess(AbstractInsnNode[] insns, int s, int e,
                                   ClassNode src, Map<String, ClassNode> pool) {
        int need = ACCESS_OK;
        String srcPkg = packageOf(src.name);
        for (int i = s; i < e; i++) {
            AbstractInsnNode n = insns[i];
            int type = n.getType();
            if (type == AbstractInsnNode.LABEL || type == AbstractInsnNode.FRAME) {
                return ACCESS_DENY;
            }
            int op = n.getOpcode();
            if (type == AbstractInsnNode.JUMP_INSN
                    || type == AbstractInsnNode.TABLESWITCH_INSN
                    || type == AbstractInsnNode.LOOKUPSWITCH_INSN
                    || op == Opcodes.ATHROW || op == Opcodes.MONITORENTER
                    || op == Opcodes.MONITOREXIT || op == Opcodes.JSR
                    || op == Opcodes.RET) {
                return ACCESS_DENY;
            }
            if (op >= Opcodes.IRETURN && op <= Opcodes.RETURN) {
                return ACCESS_DENY;
            }
            if (n instanceof FieldInsnNode) {
                FieldInsnNode fin = (FieldInsnNode) n;
                int r = memberNeed(fin.owner, srcPkg, pool,
                        fieldAccess(pool, fin.owner, fin.name, fin.desc));
                if (r == ACCESS_DENY) {
                    return ACCESS_DENY;
                }
                need = Math.max(need, r);
            } else if (n instanceof MethodInsnNode) {
                MethodInsnNode min = (MethodInsnNode) n;
                if (op == Opcodes.INVOKESPECIAL && !min.name.equals("<init>")) {
                    return ACCESS_DENY; // private 方法 / super 调用
                }
                Integer acc = methodAccess(pool, min.owner, min.name, min.desc);
                int r;
                if (min.name.equals("<init>")) {
                    r = memberNeed(min.owner, srcPkg, pool, acc);
                } else {
                    r = memberNeed(min.owner, srcPkg, pool, acc);
                }
                if (r == ACCESS_DENY) {
                    return ACCESS_DENY;
                }
                need = Math.max(need, r);
            } else if (n instanceof InvokeDynamicInsnNode) {
                // invokedynamic（lambda/method-reference/字符串拼接）的
                // bootstrap 参数里藏着对真实方法的符号引用，lambda body
                // 常是源类 private synthetic 方法：搬到无关宿主后
                // metafactory 解析即 IllegalAccessError，必须一并审查
                int r = indyNeed(((InvokeDynamicInsnNode) n).bsmArgs,
                        srcPkg, pool);
                if (r == ACCESS_DENY) {
                    return ACCESS_DENY;
                }
                need = Math.max(need, r);
            }
        }
        return need;
    }

    /**
     * 审查 invokedynamic bootstrap 常量参数（Handle / ConstantDynamic /
     * 嵌套数组）中引用的成员可访问性。
     */
    private static int indyNeed(Object[] args, String srcPkg,
                                 Map<String, ClassNode> pool) {
        int need = ACCESS_OK;
        if (args == null) {
            return need;
        }
        for (Object a : args) {
            int r = constantNeed(a, srcPkg, pool);
            if (r == ACCESS_DENY) {
                return ACCESS_DENY;
            }
            need = Math.max(need, r);
        }
        return need;
    }

    private static int constantNeed(Object c, String srcPkg,
                                     Map<String, ClassNode> pool) {
        if (c instanceof org.objectweb.asm.Handle) {
            org.objectweb.asm.Handle h = (org.objectweb.asm.Handle) c;
            if (h.getTag() == Opcodes.H_INVOKESPECIAL
                    && !h.getName().equals("<init>")) {
                return ACCESS_DENY;
            }
            Integer acc = methodAccess(pool, h.getOwner(),
                    h.getName(), h.getDesc());
            return memberNeed(h.getOwner(), srcPkg, pool, acc);
        }
        if (c instanceof org.objectweb.asm.ConstantDynamic) {
            // condy 的 bootstrap 参数 API 包私有无法枚举，且解析上下文
            // 随宿主类改变；保守拒绝（Java 8 class 不产生 condy）
            return ACCESS_DENY;
        }
        return ACCESS_OK;
    }

    /**
     * 按成员归属与访问标志给跨类访问需求。acc 为 null 表示 owner 不在
     * jar 内（JDK/外部类），按 public 乐观处理（-Xverify:all 全 JDK 兜底）。
     */
    private static int memberNeed(String owner, String srcPkg,
                                   Map<String, ClassNode> pool, Integer acc) {
        if (acc == null) {
            return ACCESS_OK;
        }
        if ((acc.intValue() & Opcodes.ACC_PUBLIC) != 0) {
            return ACCESS_OK;
        }
        if ((acc.intValue() & Opcodes.ACC_PRIVATE) != 0) {
            return ACCESS_DENY;
        }
        // protected / package-private：宿主与源同类加载器且同包才合法
        return packageOf(owner).equals(srcPkg) ? ACCESS_SAME_PKG : ACCESS_DENY;
    }

    private static Integer fieldAccess(Map<String, ClassNode> pool,
                                        String owner, String name, String desc) {
        ClassNode c = pool.get(owner);
        if (c == null) {
            return null;
        }
        for (org.objectweb.asm.tree.FieldNode f : c.fields) {
            if (f.name.equals(name) && f.desc.equals(desc)) {
                return Integer.valueOf(f.access);
            }
        }
        return null; // 父类声明等情况乐观放行
    }

    private static Integer methodAccess(Map<String, ClassNode> pool,
                                         String owner, String name, String desc) {
        ClassNode c = pool.get(owner);
        if (c == null) {
            return null;
        }
        for (MethodNode m : c.methods) {
            if (m.name.equals(name) && m.desc.equals(desc)) {
                return Integer.valueOf(m.access);
            }
        }
        return null;
    }

    /** 片段是否含值得藏起来的指令（纯常量赋值/搬运不派分）。 */
    private static boolean isWorthMoving(AbstractInsnNode[] insns, int s, int e) {
        boolean hasValuable = false;
        for (int i = s; i < e; i++) {
            AbstractInsnNode n = insns[i];
            int type = n.getType();
            if (type == AbstractInsnNode.METHOD_INSN
                    || type == AbstractInsnNode.FIELD_INSN
                    || type == AbstractInsnNode.TYPE_INSN
                    || type == AbstractInsnNode.MULTIANEWARRAY_INSN
                    || type == AbstractInsnNode.IINC_INSN) {
                hasValuable = true;
                break;
            }
            if (n instanceof LdcInsnNode) {
                hasValuable = true;
                break;
            }
            int op = n.getOpcode();
            if (op == Opcodes.AALOAD || op == Opcodes.AASTORE
                    || op == Opcodes.IALOAD || op == Opcodes.IASTORE
                    || (op >= Opcodes.LALOAD && op <= Opcodes.SASTORE)) {
                hasValuable = true;
                break;
            }
        }
        return hasValuable;
    }

    private static ClassNode pickHost(List<ClassNode> hosts,
                                       Map<String, Integer> hostLoad,
                                       String srcPkg, int accessNeed,
                                       String srcName, Set<String> sink,
                                       Random random) {
        boolean srcSink = sink.contains(srcName);
        List<ClassNode> fit = new ArrayList<ClassNode>();
        for (ClassNode h : hosts) {
            if (h.name.equals(srcName)) {
                continue;
            }
            // j2c 两侧隔离：源与宿主必须同在下沉侧或同在明文侧
            if (sink.contains(h.name) != srcSink) {
                continue;
            }
            if (hostLoad.get(h.name).intValue() >= MAX_OUT_PER_HOST) {
                continue;
            }
            if (accessNeed == ACCESS_SAME_PKG
                    && !packageOf(h.name).equals(srcPkg)) {
                continue;
            }
            fit.add(h);
        }
        if (fit.isEmpty()) {
            return null;
        }
        // 负载最小的一批里随机，保证派分均匀分散
        int min = Integer.MAX_VALUE;
        for (ClassNode h : fit) {
            min = Math.min(min, hostLoad.get(h.name).intValue());
        }
        List<ClassNode> lightest = new ArrayList<ClassNode>();
        for (ClassNode h : fit) {
            if (hostLoad.get(h.name).intValue() == min) {
                lightest.add(h);
            }
        }
        return lightest.get(random.nextInt(lightest.size()));
    }

    private static String packageOf(String internal) {
        int slash = internal.lastIndexOf('/');
        return slash < 0 ? "" : internal.substring(0, slash);
    }

    // ------------------------------------------------------------------
    // 应用：生成外提方法 + 替换调用点
    // ------------------------------------------------------------------

    /** 外提方法内临时槽：p=0（Object[] 参数），tI=1，tL=2/3，tA=4。 */
    private static final int SLOT_ARR = 0;
    private static final int SLOT_TI = 1;
    private static final int SLOT_TL = 2;
    private static final int SLOT_TA = 4;
    private static final int HOST_MAX_LOCALS = 5;

    private static void applySegments(MethodNode mn, List<Segment> segs,
                                       Map<String, ClassNode> pool, Random random) {
        AbstractInsnNode[] insns = mn.instructions.toArray();
        boolean[] moved = new boolean[insns.length];
        for (Segment seg : segs) {
            for (int i = seg.start; i < seg.end; i++) {
                moved[i] = true;
            }
        }
        // 组内按起点升序：先全部移除后统一插入，同锚点多段才能保持源码顺序
        List<Segment> ordered = new ArrayList<Segment>(segs);
        Collections.sort(ordered, (x, y) -> x.start - y.start);

        int tmpSlot = Math.max(mn.maxLocals, Analysis.observedMaxSlot(mn));

        // 1. 先建宿主外提方法并把所有被搬节点从源方法移除（保留节点不断链）。
        // 局部槽访问展开为 Object[] 桥接序列，其余指令原样保留。
        for (Segment seg : ordered) {
            String name = uniqueHostMethodName(seg.host, random);
            seg.hostMethod = name;
            int access = Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC;
            MethodNode out = new MethodNode(Opcodes.ASM9, access, name,
                    "([Ljava/lang/Object;)V", null, null);
            out.maxLocals = HOST_MAX_LOCALS;
            InsnList body = new InsnList();
            for (int i = seg.start; i < seg.end; i++) {
                AbstractInsnNode n = insns[i];
                int t = n.getType();
                if (t == AbstractInsnNode.LINE) {
                    continue; // 行号丢弃
                }
                mn.instructions.remove(n);
                if (t == AbstractInsnNode.VAR_INSN) {
                    emitHostVarAccess(body, (VarInsnNode) n, seg.frames[i]);
                } else if (t == AbstractInsnNode.IINC_INSN) {
                    emitHostIinc(body, (IincInsnNode) n);
                } else {
                    body.add(n);
                }
            }
            body.add(new InsnNode(Opcodes.RETURN));
            out.instructions.add(body);
            int pos = random.nextInt(seg.host.methods.size() + 1);
            seg.host.methods.add(pos, out);
        }

        // 2. 源方法链上只剩保留节点；按 start 升序在同一锚点前连续
        //    insertBefore，调用点顺序即源码顺序（倒序插会整体反转，
        //    把"写槽段"排到"读槽段"之后 -> top 槽 VerifyError）
        for (Segment seg : ordered) {
            // 存活锚点：区间后第一个不会被任何片段搬走的原始节点
            AbstractInsnNode afterNode = null;
            for (int k = seg.end; k < insns.length; k++) {
                if (!moved[k]) {
                    afterNode = insns[k];
                    break;
                }
            }
            InsnList call = buildCallSite(seg, tmpSlot);
            if (afterNode == null) {
                mn.instructions.add(call);
            } else {
                mn.instructions.insertBefore(afterNode, call);
            }
        }
        // 关键：外提序列使用了 mn 原 maxLocals 之上的临时槽，必须同步声明，
        // 否则后续 pass（平坦化提升等）按陈旧槽位表安排数组槽，造成撞槽
        mn.maxLocals = Math.max(mn.maxLocals, tmpSlot + 1);
    }

    /**
     * 外提方法体内展开一次局部槽访问：
     * LOAD s -> p[s] 拆箱/CHECKCAST（值入栈）；
     * STORE s -> 值暂存临时槽，装箱写回 p[s]（栈中性）。
     * 类型取自源方法该指令执行前的精确帧。
     */
    private static void emitHostVarAccess(InsnList il, VarInsnNode v,
                                           Frame<BasicValue> f) {
        int op = v.getOpcode();
        boolean isLoad = op == Opcodes.ILOAD || op == Opcodes.LLOAD
                || op == Opcodes.FLOAD || op == Opcodes.DLOAD
                || op == Opcodes.ALOAD;
        Type t = null;
        if (f != null) {
            if (isLoad && v.var < f.getLocals()) {
                BasicValue bv = f.getLocal(v.var);
                if (bv != null) {
                    t = bv.getType();
                }
            } else if (!isLoad && f.getStackSize() > 0) {
                BasicValue bv = f.getStack(f.getStackSize() - 1);
                if (bv != null) {
                    t = bv.getType();
                }
            }
        }
        if (t == null) {
            // 帧信息缺失的极端情况：按操作码宽度猜 int/long/float/double/Object
            t = guessVarType(op);
        }
        if (isLoad) {
            il.add(new VarInsnNode(Opcodes.ALOAD, SLOT_ARR));
            pushInt(il, v.var);
            il.add(new InsnNode(Opcodes.AALOAD));
            emitUnbox(il, t);
        } else {
            int tmp;
            switch (t.getSort()) {
                case Type.LONG:
                case Type.DOUBLE:
                    tmp = SLOT_TL;
                    break;
                case Type.ARRAY:
                case Type.OBJECT:
                    tmp = SLOT_TA;
                    break;
                default:
                    tmp = SLOT_TI;
                    break;
            }
            il.add(new VarInsnNode(storeOp(t), tmp));
            il.add(new VarInsnNode(Opcodes.ALOAD, SLOT_ARR));
            pushInt(il, v.var);
            il.add(new VarInsnNode(loadOp(t), tmp));
            emitBox(il, t);
            il.add(new InsnNode(Opcodes.AASTORE));
        }
    }

    /** IINC s,c -> p[s] = Integer(p[s].intValue()+c)。 */
    private static void emitHostIinc(InsnList il, IincInsnNode inc) {
        il.add(new VarInsnNode(Opcodes.ALOAD, SLOT_ARR));
        pushInt(il, inc.var);
        il.add(new InsnNode(Opcodes.AALOAD));
        il.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Integer"));
        il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/Integer", "intValue", "()I", false));
        pushInt(il, inc.incr);
        il.add(new InsnNode(Opcodes.IADD));
        il.add(new VarInsnNode(Opcodes.ISTORE, SLOT_TI));
        il.add(new VarInsnNode(Opcodes.ALOAD, SLOT_ARR));
        pushInt(il, inc.var);
        il.add(new VarInsnNode(Opcodes.ILOAD, SLOT_TI));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                "java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;", false));
        il.add(new InsnNode(Opcodes.AASTORE));
    }

    private static Type guessVarType(int op) {
        switch (op) {
            case Opcodes.LLOAD:
            case Opcodes.LSTORE:
                return Type.LONG_TYPE;
            case Opcodes.DLOAD:
            case Opcodes.DSTORE:
                return Type.DOUBLE_TYPE;
            case Opcodes.FLOAD:
            case Opcodes.FSTORE:
                return Type.FLOAT_TYPE;
            case Opcodes.ALOAD:
            case Opcodes.ASTORE:
                return Type.getType("Ljava/lang/Object;");
            default:
                return Type.INT_TYPE;
        }
    }

    private static InsnList buildCallSite(Segment seg, int tmpSlot) {
        InsnList il = new InsnList();
        int arrLen = seg.maxSlot + 1;
        pushInt(il, arrLen);
        il.add(new TypeInsnNode(Opcodes.ANEWARRAY, "java/lang/Object"));
        il.add(new VarInsnNode(Opcodes.ASTORE, tmpSlot));
        for (int i = 0; i < seg.readSlots.length; i++) {
            int slot = seg.readSlots[i];
            Type t = seg.readTypes[i];
            il.add(new VarInsnNode(Opcodes.ALOAD, tmpSlot));
            pushInt(il, slot);
            emitLoad(il, slot, t);
            emitBox(il, t);
            il.add(new InsnNode(Opcodes.AASTORE));
        }
        il.add(new VarInsnNode(Opcodes.ALOAD, tmpSlot));
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                seg.host.name, seg.hostMethod, "([Ljava/lang/Object;)V", false));
        for (int i = 0; i < seg.writeSlots.length; i++) {
            int slot = seg.writeSlots[i];
            Type t = seg.writeTypes[i];
            il.add(new VarInsnNode(Opcodes.ALOAD, tmpSlot));
            pushInt(il, slot);
            il.add(new InsnNode(Opcodes.AALOAD));
            emitUnbox(il, t);
            emitStore(il, slot, t);
        }
        return il;
    }

    // ------------------------------------------------------------------
    // 类型/装箱辅助
    // ------------------------------------------------------------------

    private static boolean isPrimitive(Type t) {
        int s = t.getSort();
        return s >= Type.BOOLEAN && s <= Type.DOUBLE;
    }

    private static int loadOp(Type t) {
        switch (t.getSort()) {
            case Type.LONG: return Opcodes.LLOAD;
            case Type.FLOAT: return Opcodes.FLOAD;
            case Type.DOUBLE: return Opcodes.DLOAD;
            case Type.ARRAY:
            case Type.OBJECT: return Opcodes.ALOAD;
            default: return Opcodes.ILOAD;
        }
    }

    private static int storeOp(Type t) {
        switch (t.getSort()) {
            case Type.LONG: return Opcodes.LSTORE;
            case Type.FLOAT: return Opcodes.FSTORE;
            case Type.DOUBLE: return Opcodes.DSTORE;
            case Type.ARRAY:
            case Type.OBJECT: return Opcodes.ASTORE;
            default: return Opcodes.ISTORE;
        }
    }

    private static void emitLoad(InsnList il, int slot, Type t) {
        il.add(new VarInsnNode(loadOp(t), slot));
    }

    private static void emitStore(InsnList il, int slot, Type t) {
        il.add(new VarInsnNode(storeOp(t), slot));
    }

    /** 栈顶值（类型 t）装箱为 Object（引用类型无操作）。 */
    private static void emitBox(InsnList il, Type t) {
        if (!isPrimitive(t)) {
            return;
        }
        String w;
        String desc;
        switch (t.getSort()) {
            case Type.BOOLEAN: w = "java/lang/Boolean"; desc = "(Z)Ljava/lang/Boolean;"; break;
            case Type.BYTE: w = "java/lang/Byte"; desc = "(B)Ljava/lang/Byte;"; break;
            case Type.CHAR: w = "java/lang/Character"; desc = "(C)Ljava/lang/Character;"; break;
            case Type.SHORT: w = "java/lang/Short"; desc = "(S)Ljava/lang/Short;"; break;
            case Type.INT: w = "java/lang/Integer"; desc = "(I)Ljava/lang/Integer;"; break;
            case Type.LONG: w = "java/lang/Long"; desc = "(J)Ljava/lang/Long;"; break;
            case Type.FLOAT: w = "java/lang/Float"; desc = "(F)Ljava/lang/Float;"; break;
            default: w = "java/lang/Double"; desc = "(D)Ljava/lang/Double;"; break;
        }
        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC, w, "valueOf", desc, false));
    }

    /** 栈顶 Object 拆箱/转型为类型 t。 */
    private static void emitUnbox(InsnList il, Type t) {
        if (isPrimitive(t)) {
            String w;
            String vn;
            switch (t.getSort()) {
                case Type.BOOLEAN: w = "java/lang/Boolean"; vn = "booleanValue"; break;
                case Type.BYTE: w = "java/lang/Byte"; vn = "byteValue"; break;
                case Type.CHAR: w = "java/lang/Character"; vn = "charValue"; break;
                case Type.SHORT: w = "java/lang/Short"; vn = "shortValue"; break;
                case Type.INT: w = "java/lang/Integer"; vn = "intValue"; break;
                case Type.LONG: w = "java/lang/Long"; vn = "longValue"; break;
                case Type.FLOAT: w = "java/lang/Float"; vn = "floatValue"; break;
                default: w = "java/lang/Double"; vn = "doubleValue"; break;
            }
            il.add(new TypeInsnNode(Opcodes.CHECKCAST, w));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL, w, vn,
                    "()" + t.getDescriptor(), false));
        } else {
            il.add(new TypeInsnNode(Opcodes.CHECKCAST,
                    t.getSort() == Type.ARRAY ? t.getDescriptor() : t.getInternalName()));
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

    private static String uniqueHostMethodName(ClassNode host, Random random) {
        Set<String> used = new HashSet<String>();
        for (MethodNode m : host.methods) {
            used.add(m.name);
        }
        for (int tries = 0; tries < 128; tries++) {
            int len = 6 + random.nextInt(5);
            StringBuilder sb = new StringBuilder(len);
            for (int i = 0; i < len; i++) {
                sb.append((char) ('a' + random.nextInt(26)));
            }
            String name = sb.toString();
            if (!used.contains(name)) {
                return name;
            }
        }
        return "x" + System.identityHashCode(host) + random.nextInt(100000);
    }
}
