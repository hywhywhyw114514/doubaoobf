package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TryCatchBlockNode;
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
 * 语句外提（逻辑打散）：
 *
 * 把构造器/方法中"只触碰 this 字段（实例方法）或什么局部变量都不碰
 * （静态方法）"的直线语句，每构建随机挑选一批，整体搬到随机命名的
 * private synthetic ()V 方法中，原位置只留一次随机名调用。
 *
 * 典型效果（对照截图中的构造器）：
 * <pre>
 *   this.list.add(Color.BLUE);            kzzqxw();
 *   this.list.add(Color.white);    →      vbmtn();
 *   this.square = new Panel(...);         aqcjf();
 * </pre>
 *
 * 连续的业务语句被拆散到类各处的多个方法里（这些外提方法随后同样会被
 * 不透明谓词/垃圾注入/平坦化处理，真假同构），单看任何一个方法都拼不出
 * 完整逻辑。每构建哪些语句被提走、提走比例均随机，无固定模式。
 *
 * 安全性：语句边界来自栈深为 0 的数据流锚点；语句内不得出现标签/跳转/
 * 返回/异常抛出/monitor、不得落在 try-catch 覆盖范围内、不得读写任何
 * 参数或局部槽（实例方法仅允许 ALOAD 0），构造器严格在 super/this 之后。
 */
public final class StatementOutliner {

    private static final int MAX_PER_METHOD = 6;

    private StatementOutliner() {
    }

    public static int apply(ClassNode cn, Random random) {
        if ((cn.access & (Opcodes.ACC_INTERFACE | Opcodes.ACC_ANNOTATION
                | Opcodes.ACC_MODULE)) != 0) {
            return 0;
        }
        Set<String> used = new HashSet<String>();
        for (MethodNode m : cn.methods) {
            used.add(m.name);
        }
        for (org.objectweb.asm.tree.FieldNode f : cn.fields) {
            used.add(f.name);
        }

        int outlined = 0;
        // 快照遍历：每处理一个方法都会向 cn.methods 插入新成员
        for (MethodNode mn : new ArrayList<MethodNode>(cn.methods)) {
            if (mn.name.equals("<clinit>")) {
                continue;
            }
            if ((mn.access & (Opcodes.ACC_ABSTRACT | Opcodes.ACC_NATIVE)) != 0) {
                continue;
            }
            if (mn.instructions == null || mn.instructions.size() == 0) {
                continue;
            }
            try {
                outlined += outlineMethod(cn, mn, random, used);
            } catch (Throwable t) {
                // 单方法分析失败不影响其他方法
                continue;
            }
        }
        return outlined;
    }

    private static int outlineMethod(ClassNode cn, MethodNode mn, Random random,
                                      Set<String> used) throws Exception {
        boolean isInit = mn.name.equals("<init>");
        boolean isStatic = (mn.access & Opcodes.ACC_STATIC) != 0;
        AbstractInsnNode[] insns = mn.instructions.toArray();

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

        // 紧边界帧分析（含 65535 一次性回退）；分析失败放弃本方法外提
        Frame<BasicValue>[] frames = Analysis.basic(mn);
        if (frames == null) {
            return 0;
        }

        // try-catch 覆盖的指令索引集合（外提会改变异常捕获语义）
        boolean[] inTry = new boolean[insns.length];
        for (TryCatchBlockNode tcb : mn.tryCatchBlocks == null
                ? new ArrayList<TryCatchBlockNode>() : mn.tryCatchBlocks) {
            int s = indexOf(insns, tcb.start);
            int e = indexOf(insns, tcb.end);
            if (s >= 0 && e >= 0) {
                for (int i = s; i < e && i < inTry.length; i++) {
                    inTry[i] = true;
                }
            }
        }

        // 收集栈空锚点（实际指令、barrier 之后）
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
            return 0;
        }

        // 枚举候选语句 [start, end)
        List<int[]> candidates = new ArrayList<int[]>();
        for (int a = 0; a + 1 < anchors.size(); a++) {
            int s = anchors.get(a).intValue();
            int e = anchors.get(a + 1).intValue();
            if (isMovable(insns, s, e, inTry, isStatic, cn)) {
                candidates.add(new int[] { s, e });
            }
        }
        if (candidates.isEmpty()) {
            return 0;
        }

        // 每构建随机：洗牌后按固定概率掷骰，再按起点倒序应用
        List<int[]> picked = new ArrayList<int[]>();
        double chance = 0.38 + random.nextDouble() * 0.3;
        for (int[] range : candidates) {
            if (picked.size() >= MAX_PER_METHOD) {
                break;
            }
            if (random.nextDouble() < chance) {
                picked.add(range);
            }
        }
        // 避免外提区间重叠（锚点切分本就相邻不重叠），按起点倒序
        java.util.Collections.sort(picked, (x, y) -> y[0] - x[0]);

        // 预计算"移动前"信息：
        // 1) moved[]：所有将被搬走的原始索引；
        // 2) 每区间的插入锚点 = 区间之后第一个不会被任何区间移动的原始
        //    节点（倒序应用时它始终挂在 mn 上）。不能在移动后沿
        //    getNext() 悬空指针找——节点即使 remove 过，add 进外提方法
        //    后 next 会被重指到外提方法内部，造成调用点误插入别的方法。
        boolean[] moved = new boolean[insns.length];
        for (int[] range : picked) {
            for (int i = range[0]; i < range[1]; i++) {
                moved[i] = true;
            }
        }

        int done = 0;
        for (int[] range : picked) {
            int s = range[0];
            int e = range[1];
            AbstractInsnNode afterNode = null;
            for (int k = e; k < insns.length; k++) {
                if (!moved[k]) {
                    afterNode = insns[k];
                    break;
                }
            }
            String name = uniqueName(used, random);
            used.add(name);
            // ACC_VARARGS：定参方法上无运行时语义、反编译不可见，仅作为
            // "外提片段"内部标记，让控制流平坦化跳过这些极简直线方法
            // （栈归一化/槽提升对它们会误判而整类回退 baseline）；守卫与
            // 环境调用注入仍照常覆盖，真假方法依旧同构
            int access = Opcodes.ACC_PRIVATE | Opcodes.ACC_SYNTHETIC
                    | Opcodes.ACC_VARARGS
                    | (isStatic ? Opcodes.ACC_STATIC : 0);
            MethodNode out = new MethodNode(Opcodes.ASM9, access, name, "()V", null, null);
            for (int i = s; i < e; i++) {
                AbstractInsnNode n = insns[i];
                if (n.getType() == AbstractInsnNode.LINE
                        || n.getType() == AbstractInsnNode.FRAME) {
                    continue;
                }
                // 必须先从旧列表显式摘除：直接 add 到另一个 InsnList
                // 不会断开旧链表的双向指针，mn 与外提方法的指令链会
                // 互相串扰，污染后续所有分析与插入
                mn.instructions.remove(n);
                out.instructions.add(n);
            }
            out.instructions.add(new InsnNode(Opcodes.RETURN));
            int pos = random.nextInt(cn.methods.size() + 1);
            cn.methods.add(pos, out);

            // 原位置：随机名调用，插在预计算的存活锚点前
            InsnList call = new InsnList();
            if (!isStatic) {
                call.add(new VarInsnNode(Opcodes.ALOAD, 0));
                call.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                        cn.name, name, "()V", false));
            } else {
                call.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        cn.name, name, "()V", false));
            }
            if (afterNode == null) {
                mn.instructions.add(call);
            } else {
                mn.instructions.insertBefore(afterNode, call);
            }
            done++;
        }
        return done;
    }

    private static boolean isMovable(AbstractInsnNode[] insns, int s, int e, boolean[] inTry,
                                      boolean isStatic, ClassNode cn) {
        boolean hasReal = false;
        for (int i = s; i < e; i++) {
            AbstractInsnNode n = insns[i];
            int type = n.getType();
            if (type == AbstractInsnNode.LABEL || type == AbstractInsnNode.FRAME
                    || type == AbstractInsnNode.LINE) {
                return false;
            }
            if (inTry[i]) {
                return false;
            }
            int op = n.getOpcode();
            if (op == Opcodes.ATHROW || op == Opcodes.MONITORENTER
                    || op == Opcodes.MONITOREXIT || op == Opcodes.JSR
                    || op == Opcodes.RET) {
                return false;
            }
            if (op >= Opcodes.IRETURN && op <= Opcodes.RETURN) {
                return false;
            }
            if (type == AbstractInsnNode.JUMP_INSN
                    || type == AbstractInsnNode.TABLESWITCH_INSN
                    || type == AbstractInsnNode.LOOKUPSWITCH_INSN) {
                return false;
            }
            if (n instanceof VarInsnNode) {
                VarInsnNode v = (VarInsnNode) n;
                if (isStatic) {
                    return false;
                }
                // 实例方法仅允许 ALOAD 0（this 已在 super 后初始化）
                if (op != Opcodes.ALOAD || v.var != 0) {
                    return false;
                }
            }
            // IINC 直接写任意局部槽，外提进 ()V 后槽不存在（maxLocals=1），
            // 会 VerifyError；含自增变量的语句段不移动
            if (type == AbstractInsnNode.IINC_INSN) {
                return false;
            }
            if (n instanceof MethodInsnNode) {
                MethodInsnNode min = (MethodInsnNode) n;
                if (min.name.equals("<init>") && min.owner.equals(cn.name)) {
                    return false; // this(...) 必须留在构造器原位
                }
            }
            hasReal = true;
        }
        return hasReal;
    }

    private static int indexOf(AbstractInsnNode[] insns, LabelNode label) {
        if (label == null) {
            return -1;
        }
        AbstractInsnNode target = label;
        for (int i = 0; i < insns.length; i++) {
            if (insns[i] == target) {
                return i;
            }
        }
        return -1;
    }

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
}
