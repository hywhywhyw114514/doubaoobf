package com.jdobf.transform;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * 类间交织网络（disperseLogic 强化层）。
 *
 * 早期不透明谓词的问题：恒等数学全部内联在当前类里，操作数是 LDC 常量，
 * 反编译器看一眼、或写个"删除常量折叠 if"的脚本就能剥光。本层把谓词
 * 的取值过程拆散到一整组跨包中继类中，单看任何一个类都无法判定真假：
 *
 * <ul>
 *   <li><b>跨类恒等编码链</b>：N 个中继类各持有一段随机可逆整数/长整数
 *       编码（奇乘法逆元 + 加/异或/循环移位），fwd 沿 R0→R1→…→Rn 逐类
 *       编码，top 调本类 rev，再沿 Rn→…→R0 逐类解码，整条跨类调用链
 *       数学上恒等。判定 {@code fwd(x) ^ x == 0} 需要跨 N 个类做过程间
 *       分析，字节码里条件本身不含任何常量。</li>
 *   <li><b>接口多态</b>：全部中继类实现同一合成接口，谓词处按
 *       Thread.getId() 奇偶随机 NEW 两个实现类之一，CHECKCAST 接口后
 *       INVOKEINTERFACE——静态分派目标不唯一，两个实现分别走"直连链"
 *       与"互递归环 + 链"，结果都恒等。</li>
 *   <li><b>ThreadLocal 跨类状态</b>：sow(x) 写入 R0 的 ThreadLocal，
 *       别的类 peek、再别的类组合 mark，所有状态读写跨类且线程私有，
 *       多线程下语义安全。</li>
 *   <li><b>跨类互递归环</b>：两个中继类的 cyc 方法以固定小深度互相
 *       调用（XOR 去程/回程自逆），调用图跨类成环且严格终止。</li>
 *   <li><b>无分支工作片段</b>：大部分注入是栈中性的跨类调用 + 真实
 *       JDK 环境调用 + 自有静态字段良性读写，没有 if 可供死分支脚本
 *       过滤；少数为带终止型死块的不透明守卫。</li>
 * </ul>
 *
 * 语义安全：守卫恒真走原路、恒假路径只放终止型死块（athrow / 死 return）；
 * 谓词不依赖跨线程共享可变状态；全部 API JDK8 可用，8-25 通过 -Xverify:all。
 */
public final class InterClassWeaver {

    private InterClassWeaver() {
    }

    // ------------------------------------------------------------------
    // 可逆运算步骤（生成期即做数值自测，数学恒等不成立直接 fail-fast）
    // ------------------------------------------------------------------

    private static final int STEP_ADD = 0;
    private static final int STEP_XOR = 1;
    private static final int STEP_MUL = 2;
    private static final int STEP_ROL = 3;

    private static final BigInteger MOD32 = BigInteger.ONE.shiftLeft(32);
    private static final BigInteger MOD64 = BigInteger.ONE.shiftLeft(64);

    /** 每个中继类盐表长度：动态常量解密 oc(x,idx) 的可用盐数。 */
    private static final int SALT_PER_RELAY = 14;

    private static final class Step {
        final int kind;
        final int p;     // 编码参数
        final int inv;   // MUL 的奇逆元

        Step(int kind, int p, int inv) {
            this.kind = kind;
            this.p = p;
            this.inv = inv;
        }
    }

    private static int oddInverse32(int a) {
        return BigInteger.valueOf(a & 0xFFFFFFFFL).modInverse(MOD32).intValue();
    }

    private static long oddInverse64(long a) {
        return BigInteger.valueOf(a).modInverse(MOD64).longValue();
    }

    private static List<Step> randomStepsI(Random r) {
        int count = 2 + r.nextInt(3); // 2..4
        List<Step> st = new ArrayList<Step>();
        for (int i = 0; i < count; i++) {
            int kind = r.nextInt(4);
            if (kind == STEP_MUL) {
                int a;
                do {
                    a = r.nextInt() | 1;
                } while (a == 1 || a == -1);
                st.add(new Step(STEP_MUL, a, oddInverse32(a)));
            } else if (kind == STEP_ROL) {
                st.add(new Step(STEP_ROL, 1 + r.nextInt(31), 0));
            } else if (kind == STEP_ADD) {
                int p;
                do {
                    p = r.nextInt();
                } while (p == 0);
                st.add(new Step(STEP_ADD, p, 0));
            } else {
                int p;
                do {
                    p = r.nextInt();
                } while (p == 0);
                st.add(new Step(STEP_XOR, p, 0));
            }
        }
        return st;
    }

    private static final class StepJ {
        final int kind;
        final long p;
        final long inv;

        StepJ(int kind, long p, long inv) {
            this.kind = kind;
            this.p = p;
            this.inv = inv;
        }
    }

    private static List<StepJ> randomStepsJ(Random r) {
        int count = 2 + r.nextInt(2); // 2..3
        List<StepJ> st = new ArrayList<StepJ>();
        for (int i = 0; i < count; i++) {
            int kind = r.nextInt(3);
            if (kind == STEP_MUL) {
                long a;
                do {
                    a = r.nextLong() | 1L;
                } while (a == 1L || a == -1L);
                st.add(new StepJ(STEP_MUL, a, oddInverse64(a)));
            } else if (kind == STEP_ADD) {
                long p;
                do {
                    p = r.nextLong();
                } while (p == 0L);
                st.add(new StepJ(STEP_ADD, p, 0L));
            } else {
                long p;
                do {
                    p = r.nextLong();
                } while (p == 0L);
                st.add(new StepJ(STEP_XOR, p, 0L));
            }
        }
        return st;
    }

    private static int applyEncI(int x, Step s) {
        switch (s.kind) {
            case STEP_ADD: return x + s.p;
            case STEP_XOR: return x ^ s.p;
            case STEP_MUL: return x * s.p;
            default:       return Integer.rotateLeft(x, s.p);
        }
    }

    private static int applyDecI(int x, Step s) {
        switch (s.kind) {
            case STEP_ADD: return x - s.p;
            case STEP_XOR: return x ^ s.p;
            case STEP_MUL: return x * s.inv;
            default:       return Integer.rotateRight(x, s.p);
        }
    }

    private static long applyEncJ(long x, StepJ s) {
        switch (s.kind) {
            case STEP_ADD: return x + s.p;
            case STEP_XOR: return x ^ s.p;
            default:       return x * s.p;
        }
    }

    private static long applyDecJ(long x, StepJ s) {
        switch (s.kind) {
            case STEP_ADD: return x - s.p;
            case STEP_XOR: return x ^ s.p;
            default:       return x * s.inv;
        }
    }

    private static void emitEncI(InsnList il, List<Step> steps) {
        for (Step s : steps) {
            switch (s.kind) {
                case STEP_ADD:
                    il.add(new LdcInsnNode(Integer.valueOf(s.p)));
                    il.add(new InsnNode(Opcodes.IADD));
                    break;
                case STEP_XOR:
                    il.add(new LdcInsnNode(Integer.valueOf(s.p)));
                    il.add(new InsnNode(Opcodes.IXOR));
                    break;
                case STEP_MUL:
                    il.add(new LdcInsnNode(Integer.valueOf(s.p)));
                    il.add(new InsnNode(Opcodes.IMUL));
                    break;
                default:
                    pushInt(il, s.p);
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            "java/lang/Integer", "rotateLeft", "(II)I", false));
                    break;
            }
        }
    }

    /** 逆编码：步骤逆序，每步换逆运算。 */
    private static void emitDecI(InsnList il, List<Step> steps) {
        for (int i = steps.size() - 1; i >= 0; i--) {
            Step s = steps.get(i);
            switch (s.kind) {
                case STEP_ADD:
                    il.add(new LdcInsnNode(Integer.valueOf(s.p)));
                    il.add(new InsnNode(Opcodes.ISUB));
                    break;
                case STEP_XOR:
                    il.add(new LdcInsnNode(Integer.valueOf(s.p)));
                    il.add(new InsnNode(Opcodes.IXOR));
                    break;
                case STEP_MUL:
                    il.add(new LdcInsnNode(Integer.valueOf(s.inv)));
                    il.add(new InsnNode(Opcodes.IMUL));
                    break;
                default:
                    pushInt(il, s.p);
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            "java/lang/Integer", "rotateRight", "(II)I", false));
                    break;
            }
        }
    }

    private static void emitEncJ(InsnList il, List<StepJ> steps) {
        for (StepJ s : steps) {
            il.add(new LdcInsnNode(Long.valueOf(s.p)));
            il.add(new InsnNode(s.kind == STEP_ADD ? Opcodes.LADD
                    : s.kind == STEP_XOR ? Opcodes.LXOR : Opcodes.LMUL));
        }
    }

    private static void emitDecJ(InsnList il, List<StepJ> steps) {
        for (int i = steps.size() - 1; i >= 0; i--) {
            StepJ s = steps.get(i);
            long v = s.kind == STEP_MUL ? s.inv : s.p;
            il.add(new LdcInsnNode(Long.valueOf(v)));
            il.add(new InsnNode(s.kind == STEP_ADD ? Opcodes.LSUB
                    : s.kind == STEP_XOR ? Opcodes.LXOR : Opcodes.LMUL));
        }
    }

    // ------------------------------------------------------------------
    // 网络构建
    // ------------------------------------------------------------------

    private static final class Relay {
        final ClassNode cn;
        final String internal;
        final List<Step> encI;
        final List<StepJ> encJ;
        String fwd;
        String rev;
        String fwdJ;
        String revJ;
        String work;
        String cycA;
        String cycB;
        String fInt;
        String fLong;
        /** 只编码不折返：sfwd_i=enc_i 后调 sfwd_{i+1}，末类直接返回。 */
        String seal;
        /** 每中继类一个加密盐表字段 + 动态常量解密方法 oc(II)I。 */
        String saltF;
        String oc;
        /** 本类盐表明文（生成期持有，用于产出 cipher；不写进类）。 */
        int[] salts;

        Relay(ClassNode cn, String internal, List<Step> encI, List<StepJ> encJ) {
            this.cn = cn;
            this.internal = internal;
            this.encI = encI;
            this.encJ = encJ;
        }
    }

    /**
     * 生成一整组跨包中继类。调用方在 baseline 字节码产出前把
     * {@link Network#nodes} 全部加入改名后的类表：Hierarchy 持有同一
     * Map 引用，COMPUTE_FRAMES 随后即可解析接口与实现类关系。
     *
     * @param weightedPackages 真实业务类所在包（可重复，按大类包加权）
     */
    public static Network build(Collection<ClassNode> existing,
                                List<String> weightedPackages, Random r) {
        Set<String> usedFull = new HashSet<String>();
        for (ClassNode c : existing) {
            usedFull.add(c.name);
        }
        int n = 5 + r.nextInt(3); // 5..7 个中继类

        // 尽量把中继类撒到不同真实包；不同包之间互相 public 调用
        List<String> packages = new ArrayList<String>();
        List<String> pool = new ArrayList<String>(weightedPackages);
        if (pool.isEmpty()) {
            pool.add("");
        }
        int guard = 0;
        while (packages.size() < n + 1 && guard++ < 200) {
            String p = pool.get(r.nextInt(pool.size()));
            if (!packages.contains(p)) {
                packages.add(p);
            }
        }
        while (packages.size() < n + 1) {
            packages.add(pool.get(r.nextInt(pool.size())));
        }

        // 合成接口
        String ifacePkg = packages.get(n);
        String ifaceSimple = pickSimple(usedFull, ifacePkg, r);
        String iface = ifacePkg.isEmpty() ? ifaceSimple : ifacePkg + "/" + ifaceSimple;
        ClassNode ifaceCn = new ClassNode(Opcodes.ASM9);
        ifaceCn.version = Opcodes.V1_8;
        ifaceCn.access = Opcodes.ACC_PUBLIC | Opcodes.ACC_INTERFACE | Opcodes.ACC_ABSTRACT;
        ifaceCn.name = iface;
        ifaceCn.superName = "java/lang/Object";
        String ifaceMethod = randName(r);
        MethodNode ifaceM = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_ABSTRACT,
                ifaceMethod, "(I)I", null, null);
        ifaceCn.methods.add(ifaceM);

        Relay[] rs = new Relay[n];
        for (int i = 0; i < n; i++) {
            String pkg = packages.get(i);
            String simple = pickSimple(usedFull, pkg, r);
            String internal = pkg.isEmpty() ? simple : pkg + "/" + simple;
            ClassNode cn = new ClassNode(Opcodes.ASM9);
            cn.version = Opcodes.V1_8;
            cn.access = Opcodes.ACC_PUBLIC | Opcodes.ACC_SUPER;
            cn.name = internal;
            cn.superName = "java/lang/Object";
            cn.interfaces = new ArrayList<String>();
            cn.interfaces.add(iface);

            Set<String> members = new HashSet<String>();
            Relay rr = new Relay(cn, internal, randomStepsI(r), randomStepsJ(r));
            rr.fwd = uniq(members, r);
            rr.rev = uniq(members, r);
            rr.fwdJ = uniq(members, r);
            rr.revJ = uniq(members, r);
            rr.work = uniq(members, r);
            rr.fInt = uniq(members, r);
            rr.fLong = uniq(members, r);
            rr.seal = uniq(members, r);
            rr.saltF = uniq(members, r);
            rr.oc = uniq(members, r);
            rr.salts = new int[SALT_PER_RELAY];
            for (int s = 0; s < rr.salts.length; s++) {
                rr.salts[s] = r.nextInt();
            }

            // 良性外观字段
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                    rr.fInt, "I", null, null));
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                    rr.fLong, "J", null, null));
            // 动态常量解密盐表（存的是全链加密态，明文盐永不进字节码）
            cn.fields.add(new FieldNode(Opcodes.ASM9,
                    Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                    rr.saltF, "[I", null, null));

            // 构造器
            MethodNode ctor = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC, "<init>", "()V", null, null);
            ctor.instructions.add(new VarInsnNode(Opcodes.ALOAD, 0));
            ctor.instructions.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                    "java/lang/Object", "<init>", "()V", false));
            ctor.instructions.add(new InsnNode(Opcodes.RETURN));
            ctor.maxStack = 1;
            ctor.maxLocals = 1;
            cn.methods.add(ctor);

            rs[i] = rr;
        }

        // 固定角色（尽量错开不同中继类）
        int idxTl = 0;
        int idxLoad = 1 % n;
        int idxMark = (n / 2) % n;
        int idxMark1 = (idxMark + 1) % n;
        int idxVerify = (n - 1) % n;
        int idxCycA = (2) % n;
        int idxCycB = (3) % n;
        int idxCycBase = (n >= 5) ? 4 % n : (idxCycA + 1) % n;

        // 互递归环方法名需先于接口实现生成分配（apply 实现里会引用）
        rs[idxCycA].cycA = "ca" + randName(r);
        rs[idxCycB].cycB = "cb" + randName(r);
        String cycBase = "cc" + randName(r);
        int ka = r.nextInt() | 1;
        int kb = r.nextInt() | 1;
        int kc = r.nextInt();

        // ---- R0：ThreadLocal 状态 + 编码链入口 ----
        Relay r0 = rs[idxTl];
        String tlName = "t" + randName(r);
        r0.cn.fields.add(new FieldNode(Opcodes.ASM9,
                Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
                tlName, "Ljava/lang/ThreadLocal;", null, null));
        String sow = "s" + randName(r);
        String tlGet = "g" + randName(r);
        String encOne = "e" + randName(r);

        MethodNode clinit = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_STATIC, "<clinit>", "()V", null, null);
        clinit.instructions.add(new TypeInsnNode(Opcodes.NEW, "java/lang/ThreadLocal"));
        clinit.instructions.add(new InsnNode(Opcodes.DUP));
        clinit.instructions.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                "java/lang/ThreadLocal", "<init>", "()V", false));
        clinit.instructions.add(new org.objectweb.asm.tree.FieldInsnNode(
                Opcodes.PUTSTATIC, r0.internal, tlName, "Ljava/lang/ThreadLocal;"));
        clinit.instructions.add(new InsnNode(Opcodes.RETURN));
        clinit.maxStack = 2;
        clinit.maxLocals = 0;
        r0.cn.methods.add(clinit);

        // sow(I)V
        MethodNode mSow = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, sow, "(I)V", null, null);
        mSow.instructions.add(new org.objectweb.asm.tree.FieldInsnNode(
                Opcodes.GETSTATIC, r0.internal, tlName, "Ljava/lang/ThreadLocal;"));
        mSow.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mSow.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                "java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;", false));
        mSow.instructions.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/ThreadLocal", "set", "(Ljava/lang/Object;)V", false));
        mSow.instructions.add(new InsnNode(Opcodes.RETURN));
        mSow.maxStack = 3;
        mSow.maxLocals = 1;
        r0.cn.methods.add(mSow);

        // tlGet()I
        MethodNode mGet = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, tlGet, "()I", null, null);
        mGet.instructions.add(new org.objectweb.asm.tree.FieldInsnNode(
                Opcodes.GETSTATIC, r0.internal, tlName, "Ljava/lang/ThreadLocal;"));
        mGet.instructions.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/ThreadLocal", "get", "()Ljava/lang/Object;", false));
        mGet.instructions.add(new TypeInsnNode(Opcodes.CHECKCAST, "java/lang/Integer"));
        mGet.instructions.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/Integer", "intValue", "()I", false));
        mGet.instructions.add(new InsnNode(Opcodes.IRETURN));
        mGet.maxStack = 2;
        mGet.maxLocals = 0;
        r0.cn.methods.add(mGet);

        // encOne(I)I：只跑 R0 一段编码（多态模板的另一侧）
        MethodNode mEncOne = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, encOne, "(I)I", null, null);
        mEncOne.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        emitEncI(mEncOne.instructions, r0.encI);
        mEncOne.instructions.add(new InsnNode(Opcodes.IRETURN));
        mEncOne.maxStack = 8;
        mEncOne.maxLocals = 1;
        r0.cn.methods.add(mEncOne);

        // ---- 每个中继类：fwd/rev 整数链、fwdJ/revJ 长整数链、接口实现、work ----
        for (int i = 0; i < n; i++) {
            Relay rr = rs[i];

            // fwd(I)I
            MethodNode fwdM = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.fwd, "(I)I", null, null);
            fwdM.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
            emitEncI(fwdM.instructions, rr.encI);
            if (i < n - 1) {
                fwdM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rs[i + 1].internal, rs[i + 1].fwd, "(I)I", false));
            } else {
                fwdM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rr.internal, rr.rev, "(I)I", false));
            }
            fwdM.instructions.add(new InsnNode(Opcodes.IRETURN));
            fwdM.maxStack = 8;
            fwdM.maxLocals = 1;
            rr.cn.methods.add(fwdM);

            // rev(I)I：rev_i(z) = i==0 ? dec_0(z) : rev_{i-1}(dec_i(z))
            MethodNode revM = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.rev, "(I)I", null, null);
            revM.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
            emitDecI(revM.instructions, rr.encI);
            if (i > 0) {
                revM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rs[i - 1].internal, rs[i - 1].rev, "(I)I", false));
            }
            revM.instructions.add(new InsnNode(Opcodes.IRETURN));
            revM.maxStack = 8;
            revM.maxLocals = 1;
            rr.cn.methods.add(revM);

            // fwdJ(J)J / revJ(J)J
            MethodNode fwdJM = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.fwdJ, "(J)J", null, null);
            fwdJM.instructions.add(new VarInsnNode(Opcodes.LLOAD, 0));
            emitEncJ(fwdJM.instructions, rr.encJ);
            if (i < n - 1) {
                fwdJM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rs[i + 1].internal, rs[i + 1].fwdJ, "(J)J", false));
            } else {
                fwdJM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rr.internal, rr.revJ, "(J)J", false));
            }
            fwdJM.instructions.add(new InsnNode(Opcodes.LRETURN));
            fwdJM.maxStack = 8;
            fwdJM.maxLocals = 2;
            rr.cn.methods.add(fwdJM);

            MethodNode revJM = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.revJ, "(J)J", null, null);
            revJM.instructions.add(new VarInsnNode(Opcodes.LLOAD, 0));
            emitDecJ(revJM.instructions, rr.encJ);
            if (i > 0) {
                revJM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rs[i - 1].internal, rs[i - 1].revJ, "(J)J", false));
            }
            revJM.instructions.add(new InsnNode(Opcodes.LRETURN));
            revJM.maxStack = 8;
            revJM.maxLocals = 2;
            rr.cn.methods.add(revJM);

            // seal(I)I：只沿 R0→…→top 编码，不折返。
            // 业务侧把值 seal 后交给末类 rev 路由方法（qadd/qmul/oc…），
            // 值在跨类调用之间以编码态存在，删掉任一跳都会得到乱码。
            MethodNode sealM = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.seal, "(I)I", null, null);
            sealM.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
            emitEncI(sealM.instructions, rr.encI);
            if (i < n - 1) {
                sealM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rs[i + 1].internal, rs[i + 1].seal, "(I)I", false));
            }
            sealM.instructions.add(new InsnNode(Opcodes.IRETURN));
            sealM.maxStack = 8;
            sealM.maxLocals = 1;
            rr.cn.methods.add(sealM);

            // 接口实现：偶数中继直连恒等链；奇数中继先绕互递归环再进链
            MethodNode applyM = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC, ifaceMethod, "(I)I", null, null);
            applyM.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
            if ((i & 1) == 1) {
                pushInt(applyM.instructions, 3 + (i % 4));
                applyM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rs[idxCycA].internal, rs[idxCycA].cycA, "(II)I", false));
            }
            applyM.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    r0.internal, r0.fwd, "(I)I", false));
            applyM.instructions.add(new InsnNode(Opcodes.IRETURN));
            applyM.maxStack = 8;
            applyM.maxLocals = 2;
            rr.cn.methods.add(applyM);
        }

        // ---- 跨类 ThreadLocal 读取 / 恒等标记 / verify ----
        Relay rLoad = rs[idxLoad];
        String load = "l" + randName(r);
        MethodNode mLoad = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, load, "()I", null, null);
        mLoad.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                r0.internal, tlGet, "()I", false));
        mLoad.instructions.add(new InsnNode(Opcodes.IRETURN));
        mLoad.maxStack = 4;
        mLoad.maxLocals = 0;
        rLoad.cn.methods.add(mLoad);

        Relay rMark = rs[idxMark];
        String mark0 = "m0" + randName(r);
        MethodNode mMark0 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, mark0, "()I", null, null);
        // int a = peek(); int b = fwd(peek()); return a ^ b; // 恒 0
        mMark0.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rLoad.internal, load, "()I", false));
        mMark0.instructions.add(new VarInsnNode(Opcodes.ISTORE, 0));
        mMark0.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mMark0.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                r0.internal, r0.fwd, "(I)I", false));
        mMark0.instructions.add(new VarInsnNode(Opcodes.ISTORE, 1));
        mMark0.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mMark0.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        mMark0.instructions.add(new InsnNode(Opcodes.IXOR));
        mMark0.instructions.add(new InsnNode(Opcodes.IRETURN));
        mMark0.maxStack = 4;
        mMark0.maxLocals = 2;
        rMark.cn.methods.add(mMark0);

        Relay rMark1 = rs[idxMark1];
        String mark1 = "m1" + randName(r);
        MethodNode mMark1 = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, mark1, "()I", null, null);
        mMark1.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rMark.internal, mark0, "()I", false));
        mMark1.instructions.add(new InsnNode(Opcodes.ICONST_1));
        mMark1.instructions.add(new InsnNode(Opcodes.IXOR));
        mMark1.instructions.add(new InsnNode(Opcodes.IRETURN));
        mMark1.maxStack = 4;
        mMark1.maxLocals = 0;
        rMark1.cn.methods.add(mMark1);

        Relay rVerify = rs[idxVerify];
        String verify = "v" + randName(r);
        MethodNode mVerify = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, verify, "(I)I", null, null);
        // return fwd(x) ^ x; // 恒 0
        mVerify.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mVerify.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                r0.internal, r0.fwd, "(I)I", false));
        mVerify.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mVerify.instructions.add(new InsnNode(Opcodes.IXOR));
        mVerify.instructions.add(new InsnNode(Opcodes.IRETURN));
        mVerify.maxStack = 4;
        mVerify.maxLocals = 1;
        rVerify.cn.methods.add(mVerify);

        // ---- 数据流强绑定基础设施 ----
        // 全构建基钥 G0（明文永不进任何类：只存 sealAll(G0)），
        // 运行时由末类 rev 链跨类解出。
        int g0 = r.nextInt();
        Relay rTop = rs[n - 1];
        Relay rTx = rs[idxMark1]; // tidX 与 R0 不同类（n>=5 保证）
        String tbase = "tb" + randName(r);
        String tidX = "tx" + randName(r);
        String lk = "lk" + randName(r);
        String ve0 = "va" + randName(r);
        String vd0 = "vb" + randName(r);
        String qAdd = "qa" + randName(r);
        String qSub = "qs" + randName(r);
        String qMul = "qm" + randName(r);

        // 数值版全链编码，与 seal 字节码链严格对应（生成期算 cipher / 自测）

        // R0.tbase()I = (int)Thread.getId() ^ open(seal(G0)) == tid ^ G0
        MethodNode mTbase = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, tbase, "()I", null, null);
        mTbase.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
        mTbase.instructions.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/Thread", "getId", "()J", false));
        mTbase.instructions.add(new InsnNode(Opcodes.L2I));
        // 先把 tid 暂存，再算 seal(G0) 的解码值，异或返回
        mTbase.instructions.add(new VarInsnNode(Opcodes.ISTORE, 0));
        int sealedG0 = g0;
        for (Relay rr : rs) {
            for (Step s : rr.encI) {
                sealedG0 = applyEncI(sealedG0, s);
            }
        }
        mTbase.instructions.add(new LdcInsnNode(Integer.valueOf(sealedG0)));
        mTbase.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rTop.internal, rTop.rev, "(I)I", false));
        mTbase.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mTbase.instructions.add(new InsnNode(Opcodes.IXOR));
        mTbase.instructions.add(new InsnNode(Opcodes.IRETURN));
        mTbase.maxStack = 4;
        mTbase.maxLocals = 1;
        r0.cn.methods.add(mTbase);

        // 另一中继类 tidX()I = (int)Thread.getId()：与 tbase 跨类对消
        MethodNode mTx = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, tidX, "()I", null, null);
        mTx.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
        mTx.instructions.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                "java/lang/Thread", "getId", "()J", false));
        mTx.instructions.add(new InsnNode(Opcodes.L2I));
        mTx.instructions.add(new InsnNode(Opcodes.IRETURN));
        mTx.maxStack = 3;
        mTx.maxLocals = 0;
        rTx.cn.methods.add(mTx);

        // R0.lk(s)I = tbase() ^ tidX() ^ s == G0 ^ s（局部变量加密的工作密钥）
        MethodNode mLk = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, lk, "(I)I", null, null);
        mLk.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                r0.internal, tbase, "()I", false));
        mLk.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rTx.internal, tidX, "()I", false));
        mLk.instructions.add(new InsnNode(Opcodes.IXOR));
        mLk.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mLk.instructions.add(new InsnNode(Opcodes.IXOR));
        mLk.instructions.add(new InsnNode(Opcodes.IRETURN));
        mLk.maxStack = 3;
        mLk.maxLocals = 1;
        r0.cn.methods.add(mLk);

        // ve/vd 各两个实现，分布在不同中继类，公式对称（XOR 自逆）：
        // ve(x,s)=x^lk(s)，vd 同形；业务槽位以密文态常驻局部变量表
        String ve1 = "vc" + randName(r);
        String vd1 = "vd" + randName(r);
        emitKeyXor(r0.cn, ve0, r0.internal, lk);
        emitKeyXor(rLoad.cn, ve1, r0.internal, lk);
        emitKeyXor(rVerify.cn, vd0, r0.internal, lk);
        emitKeyXor(rMark.cn, vd1, r0.internal, lk);

        // 末类算术路由：第一操作数以 seal 全链编码态传入，本类 rev 解回后运算。
        // 32 位溢出语义与原 IADD/ISUB/IMUL 完全一致（JVM 环内运算）。
        emitBinRoute(rTop.cn, qAdd, rTop.rev, Opcodes.IADD, rTop.internal);
        emitBinRoute(rTop.cn, qSub, rTop.rev, Opcodes.ISUB, rTop.internal);
        emitBinRoute(rTop.cn, qMul, rTop.rev, Opcodes.IMUL, rTop.internal);

        // 每个中继类：盐表 <clinit> 初始化 + oc(x,idx) 动态常量解密。
        // oc = x ^ tbase() ^ tidX() ^ rev(saltTable[idx])
        //    = x ^ (tid^G0) ^ tid ^ S = x ^ G0 ^ S
        // 业务侧 cipher = v ^ G0 ^ S，运行时还原 v；明文 v 与明文 S、G0
        // 都不在使用点的字节码里。
        for (int i = 0; i < n; i++) {
            Relay rr = rs[i];
            MethodNode existingInit = null;
            for (MethodNode mm : rr.cn.methods) {
                if (mm.name.equals("<clinit>")) {
                    existingInit = mm;
                    break;
                }
            }
            // 先在独立列表里把整段盐表初始化构造完，再整体挂接：空 InsnList
            // 提前 insertBefore 后再 add 节点不会进方法体（R0 已有 clinit）
            InsnList initIl = new InsnList();
            pushInt(initIl, rr.salts.length);
            initIl.add(new org.objectweb.asm.tree.IntInsnNode(Opcodes.NEWARRAY, Opcodes.T_INT));
            for (int s = 0; s < rr.salts.length; s++) {
                int sealed = rr.salts[s];
                for (Relay q : rs) {
                    for (Step st : q.encI) {
                        sealed = applyEncI(sealed, st);
                    }
                }
                initIl.add(new InsnNode(Opcodes.DUP));
                pushInt(initIl, s);
                initIl.add(new LdcInsnNode(Integer.valueOf(sealed)));
                initIl.add(new InsnNode(Opcodes.IASTORE));
            }
            initIl.add(new org.objectweb.asm.tree.FieldInsnNode(
                    Opcodes.PUTSTATIC, rr.internal, rr.saltF, "[I"));
            if (existingInit != null) {
                // R0 的 <clinit> 末尾有 RETURN，盐表初始化插在 RETURN 前
                AbstractInsnNode ret = existingInit.instructions.getLast();
                while (ret != null && ret.getOpcode() != Opcodes.RETURN) {
                    ret = ret.getPrevious();
                }
                if (ret != null) {
                    existingInit.instructions.insertBefore(ret, initIl);
                } else {
                    existingInit.instructions.add(initIl);
                }
                existingInit.maxStack = 4;
            } else {
                MethodNode init = new MethodNode(Opcodes.ASM9,
                        Opcodes.ACC_STATIC, "<clinit>", "()V", null, null);
                init.instructions.add(initIl);
                init.instructions.add(new InsnNode(Opcodes.RETURN));
                init.maxStack = 4;
                init.maxLocals = 0;
                rr.cn.methods.add(init);
            }

            MethodNode mOc = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.oc, "(II)I", null, null);
            mOc.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
            mOc.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    r0.internal, tbase, "()I", false));
            mOc.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    rTx.internal, tidX, "()I", false));
            mOc.instructions.add(new InsnNode(Opcodes.IXOR));
            mOc.instructions.add(new InsnNode(Opcodes.IXOR));
            mOc.instructions.add(new org.objectweb.asm.tree.FieldInsnNode(
                    Opcodes.GETSTATIC, rr.internal, rr.saltF, "[I"));
            mOc.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
            mOc.instructions.add(new InsnNode(Opcodes.IALOAD));
            mOc.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    rTop.internal, rTop.rev, "(I)I", false));
            mOc.instructions.add(new InsnNode(Opcodes.IXOR));
            mOc.instructions.add(new InsnNode(Opcodes.IRETURN));
            mOc.maxStack = 5;
            mOc.maxLocals = 2;
            rr.cn.methods.add(mOc);
        }

        // ---- 跨类互递归环（XOR 去程/回程自逆，深度有界）----
        Relay rA = rs[idxCycA];
        Relay rB = rs[idxCycB];
        Relay rC = rs[idxCycBase];

        // cycA(x,d): d<=0 -> C.base(x); else B.cycB(x^ka,d-1)^ka
        MethodNode mA = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rA.cycA, "(II)I", null, null);
        LabelNode aBase = new LabelNode();
        mA.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        mA.instructions.add(new JumpInsnNode(Opcodes.IFLE, aBase));
        mA.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mA.instructions.add(new LdcInsnNode(Integer.valueOf(ka)));
        mA.instructions.add(new InsnNode(Opcodes.IXOR));
        mA.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        mA.instructions.add(new InsnNode(Opcodes.ICONST_1));
        mA.instructions.add(new InsnNode(Opcodes.ISUB));
        mA.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rB.internal, rB.cycB, "(II)I", false));
        mA.instructions.add(new LdcInsnNode(Integer.valueOf(ka)));
        mA.instructions.add(new InsnNode(Opcodes.IXOR));
        mA.instructions.add(new InsnNode(Opcodes.IRETURN));
        mA.instructions.add(aBase);
        mA.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mA.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rC.internal, cycBase, "(I)I", false));
        mA.instructions.add(new InsnNode(Opcodes.IRETURN));
        mA.maxStack = 6;
        mA.maxLocals = 2;
        rA.cn.methods.add(mA);

        // cycB(x,d): d<=0 -> C.base(x); else A.cycA(x^kb,d-1)^kb
        MethodNode mB = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rB.cycB, "(II)I", null, null);
        LabelNode bBase = new LabelNode();
        mB.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        mB.instructions.add(new JumpInsnNode(Opcodes.IFLE, bBase));
        mB.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mB.instructions.add(new LdcInsnNode(Integer.valueOf(kb)));
        mB.instructions.add(new InsnNode(Opcodes.IXOR));
        mB.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        mB.instructions.add(new InsnNode(Opcodes.ICONST_1));
        mB.instructions.add(new InsnNode(Opcodes.ISUB));
        mB.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rA.internal, rA.cycA, "(II)I", false));
        mB.instructions.add(new LdcInsnNode(Integer.valueOf(kb)));
        mB.instructions.add(new InsnNode(Opcodes.IXOR));
        mB.instructions.add(new InsnNode(Opcodes.IRETURN));
        mB.instructions.add(bBase);
        mB.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mB.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                rC.internal, cycBase, "(I)I", false));
        mB.instructions.add(new InsnNode(Opcodes.IRETURN));
        mB.maxStack = 6;
        mB.maxLocals = 2;
        rB.cn.methods.add(mB);

        // cycBase(x) = (x ^ kc) ^ kc（结构噪声，恒等）
        MethodNode mC = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, cycBase, "(I)I", null, null);
        mC.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        mC.instructions.add(new LdcInsnNode(Integer.valueOf(kc)));
        mC.instructions.add(new InsnNode(Opcodes.IXOR));
        mC.instructions.add(new LdcInsnNode(Integer.valueOf(kc)));
        mC.instructions.add(new InsnNode(Opcodes.IXOR));
        mC.instructions.add(new InsnNode(Opcodes.IRETURN));
        mC.maxStack = 4;
        mC.maxLocals = 1;
        rC.cn.methods.add(mC);

        // ---- 每个中继类一个 void work：ThreadLocal 回种 + 环境调用 +
        //      自有静态字段良性写 + 跨类 mark / 互递归 / long 链 ----
        for (int i = 0; i < n; i++) {
            Relay rr = rs[i];
            MethodNode wm = new MethodNode(Opcodes.ASM9,
                    Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, rr.work, "(I)V", null, null);
            InsnList il = wm.instructions;
            // R0.sow(x)
            il.add(new VarInsnNode(Opcodes.ILOAD, 0));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    r0.internal, sow, "(I)V", false));
            // tmp = Thread.currentThread().getId() (int)
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Thread", "getId", "()J", false));
            il.add(new InsnNode(Opcodes.L2I));
            il.add(new VarInsnNode(Opcodes.ISTORE, 1));
            // fInt += tmp + c
            il.add(new org.objectweb.asm.tree.FieldInsnNode(
                    Opcodes.GETSTATIC, rr.internal, rr.fInt, "I"));
            il.add(new VarInsnNode(Opcodes.ILOAD, 1));
            pushInt(il, r.nextInt(4096) - 2048);
            il.add(new InsnNode(Opcodes.IADD));
            il.add(new InsnNode(Opcodes.IADD));
            il.add(new org.objectweb.asm.tree.FieldInsnNode(
                    Opcodes.PUTSTATIC, rr.internal, rr.fInt, "I"));
            // fLong = nanoTime() ^ c
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/System", "nanoTime", "()J", false));
            il.add(new LdcInsnNode(Long.valueOf(r.nextLong())));
            il.add(new InsnNode(Opcodes.LXOR));
            il.add(new org.objectweb.asm.tree.FieldInsnNode(
                    Opcodes.PUTSTATIC, rr.internal, rr.fLong, "J"));
            // 跨类 mark0()，结果丢弃
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    rMark.internal, mark0, "()I", false));
            il.add(new InsnNode(Opcodes.POP));
            if ((i & 1) == 0) {
                // 一半中继类再绕一次互递归环
                il.add(new VarInsnNode(Opcodes.ILOAD, 0));
                pushInt(il, 2 + (i % 4));
                il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                        rA.internal, rA.cycA, "(II)I", false));
                il.add(new InsnNode(Opcodes.POP));
            }
            // long 恒等链，结果丢弃
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/System", "nanoTime", "()J", false));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    r0.internal, r0.fwdJ, "(J)J", false));
            il.add(new InsnNode(Opcodes.POP2));
            il.add(new InsnNode(Opcodes.RETURN));
            wm.maxStack = 8;
            wm.maxLocals = 2;
            rr.cn.methods.add(wm);
        }

        // ---- 生成期数值自测：整数/长整数整链必须恒等，否则 fail-fast ----
        int[] samplesI = {0, 1, -1, Integer.MIN_VALUE, Integer.MAX_VALUE,
                0x55555555, 0xAAAAAAAA, r.nextInt(), r.nextInt(), r.nextInt()};
        for (int x : samplesI) {
            int y = x;
            for (Relay rr : rs) {
                for (Step s : rr.encI) {
                    y = applyEncI(y, s);
                }
            }
            for (int i = n - 1; i >= 0; i--) {
                List<Step> steps = rs[i].encI;
                for (int k = steps.size() - 1; k >= 0; k--) {
                    y = applyDecI(y, steps.get(k));
                }
            }
            if (y != x) {
                throw new IllegalStateException("InterClassWeaver int identity broken");
            }
        }
        long[] samplesJ = {0L, 1L, -1L, Long.MIN_VALUE, Long.MAX_VALUE,
                0x5555555555555555L, r.nextLong(), r.nextLong()};
        for (long x : samplesJ) {
            long y = x;
            for (Relay rr : rs) {
                for (StepJ s : rr.encJ) {
                    y = applyEncJ(y, s);
                }
            }
            for (int i = n - 1; i >= 0; i--) {
                List<StepJ> steps = rs[i].encJ;
                for (int k = steps.size() - 1; k >= 0; k--) {
                    y = applyDecJ(y, steps.get(k));
                }
            }
            if (y != x) {
                throw new IllegalStateException("InterClassWeaver long identity broken");
            }
        }

        List<ClassNode> nodes = new ArrayList<ClassNode>();
        nodes.add(ifaceCn);
        Set<String> names = new HashSet<String>();
        for (Relay rr : rs) {
            nodes.add(rr.cn);
            names.add(rr.internal);
        }
        names.add(iface);

        Network net = new Network();
        net.nodes = nodes;
        net.relayNames = names;
        net.iface = iface;
        net.ifaceMethod = ifaceMethod;
        net.r0 = r0.internal;
        net.mSow = sow;
        net.mFwd = r0.fwd;
        net.mFwdJ = r0.fwdJ;
        net.mEncOne = encOne;
        net.markOwner = rMark.internal;
        net.mMark0 = mark0;
        net.mMark1 = mark1;
        net.mark1Owner = rMark1.internal;
        net.verifyOwner = rVerify.internal;
        net.mVerify = verify;
        net.cycOwner = rA.internal;
        net.mCyc = rA.cycA;
        net.implX = r0.internal;
        net.implY = rs[n >= 3 ? 2 : 1].internal;
        net.workOwners = new String[n];
        net.workMethods = new String[n];
        for (int i = 0; i < n; i++) {
            net.workOwners[i] = rs[i].internal;
            net.workMethods[i] = rs[i].work;
        }
        net.g0 = g0;
        net.ocOwners = new String[n];
        net.ocMethods = new String[n];
        net.ocSalts = new int[n][];
        for (int i = 0; i < n; i++) {
            net.ocOwners[i] = rs[i].internal;
            net.ocMethods[i] = rs[i].oc;
            net.ocSalts[i] = rs[i].salts.clone();
        }
        net.sealOwner = r0.internal;
        net.mSeal = r0.seal;
        net.qOwner = rTop.internal;
        net.qAdd = qAdd;
        net.qSub = qSub;
        net.qMul = qMul;
        net.encOwners[0] = r0.internal;
        net.encMethods[0] = ve0;
        net.encOwners[1] = rLoad.internal;
        net.encMethods[1] = ve1;
        net.decOwners[0] = rVerify.internal;
        net.decMethods[0] = vd0;
        net.decOwners[1] = rMark.internal;
        net.decMethods[1] = vd1;
        return net;
    }

    private static String pickSimple(Set<String> usedFull, String pkg, Random r) {
        for (int tries = 0; tries < 80; tries++) {
            String s = randName(r);
            String full = pkg.isEmpty() ? s : pkg + "/" + s;
            if (!usedFull.contains(full)) {
                usedFull.add(full);
                return s;
            }
        }
        for (int i = 0; ; i++) {
            String s = "q" + Integer.toHexString(r.nextInt()) + i;
            String full = pkg.isEmpty() ? s : pkg + "/" + s;
            if (!usedFull.contains(full)) {
                usedFull.add(full);
                return s;
            }
        }
    }

    private static String randName(Random r) {
        int len = 6 + r.nextInt(6);
        StringBuilder sb = new StringBuilder(len);
        for (int i = 0; i < len; i++) {
            sb.append((char) ('a' + r.nextInt(26)));
        }
        return sb.toString();
    }

    private static String uniq(Set<String> used, Random r) {
        String s;
        do {
            s = randName(r);
        } while (!used.add(s));
        return s;
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

    /** 生成 {@code static int name(x,s) = x ^ lkOwner.lk(s)}。 */
    private static void emitKeyXor(ClassNode cn, String name, String lkOwner, String lk) {
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, name, "(II)I", null, null);
        m.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        m.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        m.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                lkOwner, lk, "(I)I", false));
        m.instructions.add(new InsnNode(Opcodes.IXOR));
        m.instructions.add(new InsnNode(Opcodes.IRETURN));
        m.maxStack = 3;
        m.maxLocals = 2;
        cn.methods.add(m);
    }

    /** 生成 {@code static int name(a,b) = revSelf(a) op b}（revSelf 在本类）。 */
    private static void emitBinRoute(ClassNode cn, String name, String revSelf,
                                      int binOp, String selfOwner) {
        MethodNode m = new MethodNode(Opcodes.ASM9,
                Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, name, "(II)I", null, null);
        m.instructions.add(new VarInsnNode(Opcodes.ILOAD, 0));
        m.instructions.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                selfOwner, revSelf, "(I)I", false));
        m.instructions.add(new VarInsnNode(Opcodes.ILOAD, 1));
        m.instructions.add(new InsnNode(binOp));
        m.instructions.add(new InsnNode(Opcodes.IRETURN));
        m.maxStack = 4;
        m.maxLocals = 2;
        cn.methods.add(m);
    }

    // ------------------------------------------------------------------
    // 运行时网络句柄 + 注入
    // ------------------------------------------------------------------

    public static final class Network {
        /** 合成接口 + 中继类，需由调用方加入改名后的类表。 */
        public List<ClassNode> nodes;
        Set<String> relayNames;

        String iface;
        String ifaceMethod;
        String r0;
        String mSow;
        String mFwd;
        String mFwdJ;
        String mEncOne;
        String markOwner;
        String mMark0;
        String mark1Owner;
        String mMark1;
        String verifyOwner;
        String mVerify;
        String cycOwner;
        String mCyc;
        String implX;
        String implY;
        String[] workOwners;
        String[] workMethods;

        // ---- 数据流强绑定（DataFlowBinder 使用）----
        /** 全构建基钥明文（仅生成期/编译期在混淆器 JVM 内存在）。 */
        int g0;
        /** 每中继类盐表明文，与 ocOwners/ocMethods 下标一一对应。 */
        int[][] ocSalts;
        String[] ocOwners;
        String[] ocMethods;
        /** seal 全链编码入口（R0）。 */
        String sealOwner;
        String mSeal;
        /** 末类算术路由（操作数 1 传 seal 编码态）。 */
        String qOwner;
        String qAdd;
        String qSub;
        String qMul;
        /** 局部变量加密/解密实现（各两个，跨类）。 */
        String[] encOwners = new String[2];
        String[] encMethods = new String[2];
        String[] decOwners = new String[2];
        String[] decMethods = new String[2];

        public boolean isRelay(String internal) {
            return relayNames.contains(internal);
        }

        public int relayClassCount() {
            return nodes.size();
        }

        /**
         * 在栈顶留下一个恒等 int（wantOne=true 时恒 1，否则恒 0）。
         * 值全部来自跨类调用/环境 API，字节码层面不含可折叠常量条件；
         * slot 为方法级垃圾槽（可能用到 slot+1 做临时变量）。
         */
        public void emitOpaqueInt(InsnList il, Random r, int slot, boolean wantOne) {
            int t = (slot >= 0) ? r.nextInt(5) : r.nextInt(2) * 3;
            switch (t) {
                case 0: // 跨类 ThreadLocal mark
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            markOwner, mMark0, "()I", false));
                    break;
                case 1: // fwd(x) ^ x，跨完整编码链
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            verifyOwner, mVerify, "(I)I", false));
                    break;
                case 2: // 接口多态：两个实现按线程 id 奇偶二选一
                    emitPoly(il, r, slot);
                    break;
                case 3: // long 环境值过跨类 long 恒等链：x ^ fwdJ(x) 恒 0
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            "java/lang/System", "nanoTime", "()J", false));
                    il.add(new InsnNode(Opcodes.DUP2));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            r0, mFwdJ, "(J)J", false));
                    il.add(new InsnNode(Opcodes.LXOR));
                    il.add(new InsnNode(Opcodes.L2I));
                    break;
                default: // 先 sow 再跨类 mark
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            r0, mSow, "(I)V", false));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            markOwner, mMark0, "()I", false));
                    break;
            }
            if (wantOne) {
                emitWantOne(il, r, true);
            }
        }

        /**
         * 业务数据消费型恒 0：verify(slot)=fwd(slot)^slot，slot 必须是调用点
         * 上<b>真实活动的业务 int 槽</b>（参数/中间值/密文槽均可，恒等性对任意
         * int 成立）。谓词结果数据流上依赖业务值——剥离 ILOAD/调用则栈与跳转
         * 同时失效，无法当作"平行垃圾"删除；要证伪需跨类模拟整条编码链。
         */
        public void emitBusinessZero(InsnList il, Random r, int slot, boolean wantOne) {
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    verifyOwner, mVerify, "(I)I", false));
            emitWantOne(il, r, wantOne);
        }

        /** 栈顶 0/1 翻转尾变换（随机三种）。 */
        private void emitWantOne(InsnList il, Random r, boolean wantOne) {
            if (!wantOne) {
                return;
            }
            switch (r.nextInt(3)) {
                case 0:
                    il.add(new InsnNode(Opcodes.ICONST_1));
                    il.add(new InsnNode(Opcodes.IXOR));
                    break;
                case 1:
                    il.add(new InsnNode(Opcodes.ICONST_1));
                    il.add(new InsnNode(Opcodes.IADD));
                    break;
                default:
                    il.add(new InsnNode(Opcodes.ICONST_1));
                    il.add(new InsnNode(Opcodes.SWAP));
                    il.add(new InsnNode(Opcodes.ISUB));
                    break;
            }
        }

        /**
         * 多态恒等片段，栈顶留 int 0：
         * e = R0.encOne(s); op = (threadId &amp; 1)==0 ? new X() : new Y();
         * op.apply(e) ^ e
         */
        private void emitPoly(InsnList il, Random r, int slot) {
            LabelNode pickY = new LabelNode();
            LabelNode join = new LabelNode();
            il.add(new VarInsnNode(Opcodes.ILOAD, slot));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    r0, mEncOne, "(I)I", false));
            il.add(new VarInsnNode(Opcodes.ISTORE, slot + 1));
            il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
            il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                    "java/lang/Thread", "getId", "()J", false));
            il.add(new InsnNode(Opcodes.L2I));
            il.add(new InsnNode(Opcodes.ICONST_1));
            il.add(new InsnNode(Opcodes.IAND));
            il.add(new JumpInsnNode(Opcodes.IFEQ, pickY));
            il.add(new TypeInsnNode(Opcodes.NEW, implX));
            il.add(new InsnNode(Opcodes.DUP));
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                    implX, "<init>", "()V", false));
            il.add(new JumpInsnNode(Opcodes.GOTO, join));
            il.add(pickY);
            il.add(new TypeInsnNode(Opcodes.NEW, implY));
            il.add(new InsnNode(Opcodes.DUP));
            il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                    implY, "<init>", "()V", false));
            il.add(join);
            il.add(new TypeInsnNode(Opcodes.CHECKCAST, iface));
            il.add(new VarInsnNode(Opcodes.ILOAD, slot + 1));
            il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE,
                    iface, ifaceMethod, "(I)I", true));
            il.add(new VarInsnNode(Opcodes.ILOAD, slot + 1));
            il.add(new InsnNode(Opcodes.IXOR));
        }

        /** 完整不透明守卫：恒真继续原指令，恒假落入终止型死块。 */
        public InsnList buildGuard(Random r, int slot, boolean voidOrInit) {
            LabelNode real = new LabelNode();
            LabelNode dead = new LabelNode();
            boolean wantOne = r.nextBoolean();
            boolean gotoForm = r.nextBoolean();
            InsnList il = new InsnList();
            emitOpaqueInt(il, r, slot, wantOne);
            if (gotoForm) {
                il.add(new JumpInsnNode(wantOne ? Opcodes.IFEQ : Opcodes.IFNE, dead));
                il.add(new JumpInsnNode(Opcodes.GOTO, real));
                il.add(dead);
                ControlFlow.appendDead(il, r, voidOrInit);
                il.add(real);
            } else {
                il.add(new JumpInsnNode(wantOne ? Opcodes.IFNE : Opcodes.IFEQ, real));
                il.add(dead);
                ControlFlow.appendDead(il, r, voidOrInit);
                il.add(real);
            }
            return il;
        }

        /** 栈中性工作片段（无分支，死分支过滤器无 if 可删）。 */
        public InsnList buildWork(Random r, int slot) {
            InsnList il = new InsnList();
            int t = r.nextInt(6);
            switch (t) {
                case 0: { // 环境值 -> 垃圾槽；sow；跨类 work
                    il.add(JunkCode.envIntSnippet(r, slot));
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            r0, mSow, "(I)V", false));
                    int i = r.nextInt(workOwners.length);
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            workOwners[i], workMethods[i], "(I)V", false));
                    break;
                }
                case 1: { // nanoTime 过 long 恒等链后丢弃
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            "java/lang/System", "nanoTime", "()J", false));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            r0, mFwdJ, "(J)J", false));
                    il.add(new InsnNode(Opcodes.POP2));
                    break;
                }
                case 2: { // 接口多态调用，结果丢弃
                    LabelNode pickY = new LabelNode();
                    LabelNode join = new LabelNode();
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            "java/lang/Thread", "currentThread", "()Ljava/lang/Thread;", false));
                    il.add(new MethodInsnNode(Opcodes.INVOKEVIRTUAL,
                            "java/lang/Thread", "getId", "()J", false));
                    il.add(new InsnNode(Opcodes.L2I));
                    il.add(new InsnNode(Opcodes.ICONST_1));
                    il.add(new InsnNode(Opcodes.IAND));
                    il.add(new JumpInsnNode(Opcodes.IFEQ, pickY));
                    il.add(new TypeInsnNode(Opcodes.NEW, implX));
                    il.add(new InsnNode(Opcodes.DUP));
                    il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                            implX, "<init>", "()V", false));
                    il.add(new JumpInsnNode(Opcodes.GOTO, join));
                    il.add(pickY);
                    il.add(new TypeInsnNode(Opcodes.NEW, implY));
                    il.add(new InsnNode(Opcodes.DUP));
                    il.add(new MethodInsnNode(Opcodes.INVOKESPECIAL,
                            implY, "<init>", "()V", false));
                    il.add(join);
                    il.add(new TypeInsnNode(Opcodes.CHECKCAST, iface));
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    il.add(new MethodInsnNode(Opcodes.INVOKEINTERFACE,
                            iface, ifaceMethod, "(I)I", true));
                    il.add(new InsnNode(Opcodes.POP));
                    break;
                }
                case 3: { // int 恒等链回写
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            r0, mFwd, "(I)I", false));
                    il.add(new VarInsnNode(Opcodes.ISTORE, slot));
                    break;
                }
                case 4: { // 互递归环回写
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    pushInt(il, 3 + r.nextInt(4));
                    il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                            cycOwner, mCyc, "(II)I", false));
                    il.add(new VarInsnNode(Opcodes.ISTORE, slot));
                    break;
                }
                default: { // verify（恒 0）丢弃；偶尔 mark1（恒 1）丢弃
                    il.add(new VarInsnNode(Opcodes.ILOAD, slot));
                    if (r.nextBoolean()) {
                        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                                verifyOwner, mVerify, "(I)I", false));
                    } else {
                        il.add(new InsnNode(Opcodes.POP));
                        il.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                                mark1Owner, mMark1, "()I", false));
                    }
                    il.add(new InsnNode(Opcodes.POP));
                    break;
                }
            }
            return il;
        }

        // ---- 逐类注入 ----

        private static final int WEAVE_MAX_PER_METHOD = 10;
        private static final int WEAVE_METHOD_NODE_CAP = 14000;
        private static final int SYNTH_STACK_BOUND = 256;

        public int weave(ClassNode cn, Random r) {
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
                // <clinit> 不注入：跨类静态调用会触发中继类初始化，
                // 避免任何类初始化顺序耦合
                if (mn.name.equals("<clinit>")) {
                    continue;
                }
                try {
                    inserted += weaveOne(cn, mn, r);
                } catch (Throwable t) {
                    continue;
                }
            }
            return inserted;
        }

        private int weaveOne(ClassNode cn, MethodNode mn, Random upstream) throws Exception {
            // 每方法从主管线随机流派生一个独立的短生命周期 Random：
            // java.util.Random 是 LCG，主管线在数百万次抽取后会落到某些
            // 偏移区段，该区段内"紧邻的两个 nextDouble"（本方法的 rate 与
            // 紧随其后的锚点判定）呈现强反相关，导致按概率本该 ~18% 命中的
            // 锚点在整次构建里 0 命中。派生流只承担每方法内十几个抽取，
            // 种子仍完全来自 obfSeed，保持同种子可复现。
            long upstreamSeed = upstream.nextLong();
            Random r = new Random(upstreamSeed ^ 0x9E3779B97F4A7C15L);
            AbstractInsnNode[] insns = mn.instructions.toArray();
            if (insns.length >= WEAVE_METHOD_NODE_CAP) {
                return 0;
            }
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

            int observed = 0;
            for (AbstractInsnNode n : insns) {
                if (n instanceof VarInsnNode) {
                    int op = n.getOpcode();
                    int width = (op == Opcodes.LLOAD || op == Opcodes.DLOAD
                            || op == Opcodes.LSTORE || op == Opcodes.DSTORE) ? 2 : 1;
                    observed = Math.max(observed, ((VarInsnNode) n).var + width);
                } else if (n instanceof IincInsnNode) {
                    observed = Math.max(observed, ((IincInsnNode) n).var + 1);
                }
            }
            // 多态模板用 slot+1 做临时变量，预留两个 int 槽
            int slot = Math.max(observed, 1);
            int analysisLocals = Math.max(slot + 2, 8);

            int savedStack = mn.maxStack;
            int savedLocals = mn.maxLocals;
            Frame<BasicValue>[] frames;
            mn.maxStack = SYNTH_STACK_BOUND;
            mn.maxLocals = analysisLocals;
            try {
                frames = new Analyzer<BasicValue>(
                        new BasicInterpreter()).analyze(cn.name, mn);
            } catch (Throwable first) {
                mn.maxStack = 65535;
                mn.maxLocals = 65535;
                try {
                    frames = new Analyzer<BasicValue>(
                            new BasicInterpreter()).analyze(cn.name, mn);
                } catch (Throwable second) {
                    mn.maxStack = savedStack;
                    mn.maxLocals = savedLocals;
                    return 0;
                }
            } finally {
                mn.maxStack = savedStack;
                mn.maxLocals = savedLocals;
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

            double rate = 0.10 + r.nextDouble() * 0.16;
            List<AbstractInsnNode> picked = new ArrayList<AbstractInsnNode>();
            for (AbstractInsnNode a : anchors) {
                if (picked.size() >= WEAVE_MAX_PER_METHOD) {
                    break;
                }
                if (r.nextDouble() < rate) {
                    picked.add(a);
                }
            }
            if (picked.isEmpty()) {
                return 0;
            }
            boolean voidOrInit = mn.name.equals("<init>")
                    || Type.getMethodType(mn.desc).getReturnType().getSort() == Type.VOID;

            // 序言先插：slot 与 slot+1 两个垃圾槽都初始化；
            // 随后 sow 进 R0 的 ThreadLocal——mark0/mark1/load 在本线程首次
            // 调用前必须保证 TL 非空，否则 get()->checkcast Integer 会 NPE。
            // 每个被织入方法入口都 sow，重入只是覆盖成另一个合法 int，
            // mark 类谓词对任意值恒 0，多线程各持各的槽。
            InsnList prologue = new InsnList();
            pushInt(prologue, r.nextInt(256) + 1);
            prologue.add(new VarInsnNode(Opcodes.ISTORE, slot));
            pushInt(prologue, r.nextInt(256) + 1);
            prologue.add(new VarInsnNode(Opcodes.ISTORE, slot + 1));
            prologue.add(new VarInsnNode(Opcodes.ILOAD, slot));
            prologue.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    r0, mSow, "(I)V", false));
            mn.instructions.insertBefore(prologuePoint, prologue);

            Collections.shuffle(picked, r);
            for (int i = picked.size() - 1; i >= 0; i--) {
                AbstractInsnNode a = picked.get(i);
                if (mn.instructions.indexOf(a) < 0) {
                    continue;
                }
                InsnList piece = r.nextInt(100) < 42
                        ? buildGuard(r, slot, voidOrInit)
                        : buildWork(r, slot);
                mn.instructions.insertBefore(a, piece);
            }
            return picked.size();
        }
    }
}
