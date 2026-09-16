package com.jdobf.transform;

import org.objectweb.asm.Label;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldInsnNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.zip.CRC32;

/**
 * 伪代码类“完整性暗桩链”安装器（在所有混淆变换完成后执行）。
 *
 * <h3>防删除（硬符号引用，迭代遍历）</h3>
 * 每个伪代码类注入一个 {@code public static void prime(int expected)} 方法；
 * 另生成若干“分发类”，每个分发类顺序硬编码 INVOKESTATIC 调用一组伪代码类的
 * prime，分发类之间再首尾串联：
 * <pre>
 *   Main.main() -> D0.run() -> D1.run() -> ... -> Dk.run()
 *                    |             |
 *                    +-- 64 个 prime（返回后再调下一个，栈不增长）
 * </pre>
 * 启动时每个伪代码类都会被显式调用，任一类/分发类被删除或改名，
 * 符号解析即抛 NoClassDefFoundError。每 {@link #CHUNK} 个类一个分发类，
 * 故万级类数量时调用深度也只有约 160 帧，不会 StackOverflow。
 *
 * <h3>防篡改（CRC32 自校验）</h3>
 * prime/run 运行时通过自身 ClassLoader 读取自己的 {@code .class} 字节计算
 * CRC32，与调用方内联传入的期望值比对，任何字节改动都抛 IllegalStateException；
 * 期望值内联在调用方，改动期望值本身又会改变调用方字节、被其前驱发现。
 *
 * <h3>定版顺序</h3>
 * 伪代码类无外向依赖，先全部渲染取 CRC；分发类逆向渲染（Dk+1 的 CRC
 * 内联进 Dk）；最后把 D0 的 CRC 写入 Main 锚点字段并渲染 Main。
 *
 * <p>失败时整体回退：恢复被修改类的基线字节、移除新增分发类条目。
 */
public final class GuardChain {

    private static final int ASM = Opcodes.ASM9;

    /** 每个分发类负责串联的伪代码类数量；入口方法体积约 64×6 字节，远低于 64KB 限制。 */
    private static final int CHUNK = 64;

    private static final String CRC = "java/util/zip/CRC32";
    private static final String INPUT_STREAM = "java/io/InputStream";

    /** 校验失败时抛出的异常类型（均为 JDK 自带、含无参构造器，无明文特征字符串）。 */
    private static final String[] FAIL_TYPES = {
            "java/lang/IllegalStateException",
            "java/lang/RuntimeException",
            "java/lang/NullPointerException",
            "java/lang/ArithmeticException",
            "java/lang/ArrayIndexOutOfBoundsException",
    };

    public interface Renderer {
        byte[] render(ClassNode cn) throws Exception;
    }

    public interface Log {
        void log(String message);
    }

    private GuardChain() {
    }

    /** n 个伪代码类需要的分发节点数量。 */
    public static int dispatcherCountFor(int n) {
        return (n + CHUNK - 1) / CHUNK;
    }

    /**
     * 安装暗桩链。
     *
     * @param chain       伪代码类最终内部名（已改名），顺序即校验顺序
     * @param dispatchers 分发节点最终内部名（已改名；顺序与 chain 分块对应，
     *                    数量 = {@link #dispatcherCountFor}）
     * @param mainClass   Main-Class 最终内部名
     * @param nodes       全部最终 ClassNode（变换后的节点会被追加方法）
     * @param finalBytes  各类最终字节映射；成功时替换链上类/Main/分发类条目
     * @param baseline    安装前基线字节，失败时用于回退
     * @return true 已安装；false 失败并已回退
     */
    public static boolean install(List<String> chain, List<String> dispatchers,
                                  String mainClass,
                                  Map<String, ClassNode> nodes,
                                  Map<String, byte[]> finalBytes,
                                  Map<String, byte[]> baseline,
                                  Random random, Renderer renderer, Log log) {
        int n = chain.size();
        int dispatchCount = dispatchers.size();
        if (n == 0 || dispatchCount == 0 || dispatchCount != dispatcherCountFor(n)) {
            return false;
        }
        List<String> restoreTouched = new ArrayList<String>(chain);
        restoreTouched.addAll(dispatchers);
        restoreTouched.add(mainClass);
        try {
            ClassNode[] fakes = new ClassNode[n];
            for (int i = 0; i < n; i++) {
                ClassNode cn = nodes.get(chain.get(i));
                if (cn == null) {
                    throw new IllegalStateException("链上类不存在: " + chain.get(i));
                }
                fakes[i] = cn;
            }
            ClassNode[] dispatchNodes = new ClassNode[dispatchCount];
            for (int k = 0; k < dispatchCount; k++) {
                ClassNode cn = nodes.get(dispatchers.get(k));
                if (cn == null) {
                    throw new IllegalStateException("分发类不存在: " + dispatchers.get(k));
                }
                dispatchNodes[k] = cn;
            }

            // 1. 每个伪代码类注入自校验方法；名字使用混淆风格（单/双字母），
            //    与改名产物保持一致，由分发类记录每个类的实际方法名
            String[] primeNames = new String[n];
            for (int i = 0; i < n; i++) {
                String name = freshObfName(random, fakes[i], true);
                primeNames[i] = name;
                MethodNode prime = new MethodNode(ASM,
                        Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, name, "(I)V", null, null);
                emitSelfCheck(prime, chain.get(i), random);
                prime.visitInsn(Opcodes.RETURN);
                prime.visitMaxs(0, 0);
                prime.visitEnd();
                fakes[i].methods.add(prime);
            }

            // 2. 渲染全部伪代码类，取最终 CRC
            int[] fakeCrc = new int[n];
            for (int i = 0; i < n; i++) {
                byte[] b = renderer.render(fakes[i]);
                fakeCrc[i] = crc32(b);
                finalBytes.put(chain.get(i), b);
            }

            // 3. 分发类入口方法名：所有分发类共用一个、且与各自已有成员都不冲突
            String runName = freshSharedMethodName(random, dispatchNodes);

            // 4. 逆向构建/渲染分发类：末分发类无前驱常量，其 CRC 内联进上一个
            byte[][] dispatchBytes = new byte[dispatchCount][];
            int nextDispatcherCrc = 0;
            for (int k = dispatchCount - 1; k >= 0; k--) {
                String self = dispatchers.get(k);
                MethodNode run = new MethodNode(ASM,
                        Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC, runName, "(I)V", null, null);
                emitSelfCheck(run, self, random);
                int from = k * CHUNK;
                int to = Math.min(n, from + CHUNK);
                for (int i = from; i < to; i++) {
                    run.visitLdcInsn(Integer.valueOf(fakeCrc[i]));
                    run.visitMethodInsn(Opcodes.INVOKESTATIC,
                            chain.get(i), primeNames[i], "(I)V", false);
                }
                if (k + 1 < dispatchCount) {
                    run.visitLdcInsn(Integer.valueOf(nextDispatcherCrc));
                    run.visitMethodInsn(Opcodes.INVOKESTATIC,
                            dispatchers.get(k + 1), runName, "(I)V", false);
                }
                run.visitInsn(Opcodes.RETURN);
                run.visitMaxs(0, 0);
                run.visitEnd();
                dispatchNodes[k].methods.add(run);

                byte[] b = renderer.render(dispatchNodes[k]);
                dispatchBytes[k] = b;
                nextDispatcherCrc = crc32(b);
            }

            // 5. Main 锚点：持有 D0 的 CRC，入口最先发起整条链
            ClassNode mainNode = nodes.get(mainClass);
            if (mainNode == null) {
                throw new IllegalStateException("主类不存在: " + mainClass);
            }
            MethodNode mainMethod = findMain(mainNode);
            if (mainMethod == null) {
                throw new IllegalStateException("主类缺少 main(String[]) 方法: " + mainClass);
            }
            String anchor = freshObfName(random, mainNode, false);
            mainNode.fields.add(new FieldNode(Opcodes.ACC_PRIVATE | Opcodes.ACC_STATIC
                    | Opcodes.ACC_FINAL, anchor, "I", null, Integer.valueOf(nextDispatcherCrc)));
            InsnList head = new InsnList();
            head.add(new FieldInsnNode(Opcodes.GETSTATIC, mainClass, anchor, "I"));
            head.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
                    dispatchers.get(0), runName, "(I)V", false));
            mainMethod.instructions.insert(head);
            byte[] mainBytes = renderer.render(mainNode);

            // 6. 提交
            for (int k = 0; k < dispatchCount; k++) {
                finalBytes.put(dispatchers.get(k), dispatchBytes[k]);
            }
            finalBytes.put(mainClass, mainBytes);
            log.log("完整性暗桩链已激活：" + n + " 个伪代码类经 " + dispatchCount
                    + " 个分发节点与入口串联（删除/篡改任一节点将拒绝启动）");
            return true;
        } catch (Throwable t) {
            log.log("[警告] 完整性暗桩链安装失败，已回退为无暗桩字节码: " + t);
            for (String name : restoreTouched) {
                byte[] base = baseline.get(name);
                if (base != null) {
                    finalBytes.put(name, base);
                }
            }
            return false;
        }
    }

    /**
     * 向方法发射“读取自身 .class -> CRC32 -> 与入参 expected 比对”的完整前缀。
     * 槽位：0=expected 1=loader 2=resource 3=stream 4=crc 5=buf 6=read。
     * 通过校验后控制流落到末尾；失败抛 IllegalStateException。
     */
    private static void emitSelfCheck(MethodNode m, String self, Random random) {
        m.visitCode();
        m.visitLdcInsn(Type.getObjectType(self));
        m.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/Class",
                "getClassLoader", "()Ljava/lang/ClassLoader;", false);
        m.visitVarInsn(Opcodes.ASTORE, 1);
        m.visitLdcInsn(self + ".class");
        m.visitVarInsn(Opcodes.ASTORE, 2);
        m.visitVarInsn(Opcodes.ALOAD, 1);
        Label lSystem = new Label();
        m.visitJumpInsn(Opcodes.IFNULL, lSystem);
        m.visitVarInsn(Opcodes.ALOAD, 1);
        m.visitVarInsn(Opcodes.ALOAD, 2);
        m.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/ClassLoader",
                "getResourceAsStream", "(Ljava/lang/String;)Ljava/io/InputStream;", false);
        Label lGot = new Label();
        m.visitJumpInsn(Opcodes.GOTO, lGot);
        m.visitLabel(lSystem);
        m.visitVarInsn(Opcodes.ALOAD, 2);
        m.visitMethodInsn(Opcodes.INVOKESTATIC, "java/lang/ClassLoader",
                "getSystemResourceAsStream", "(Ljava/lang/String;)Ljava/io/InputStream;", false);
        m.visitLabel(lGot);
        m.visitVarInsn(Opcodes.ASTORE, 3);
        m.visitVarInsn(Opcodes.ALOAD, 3);
        Label lInOk = new Label();
        m.visitJumpInsn(Opcodes.IFNONNULL, lInOk);
        throwFailure(m, FAIL_TYPES[random.nextInt(FAIL_TYPES.length)]);
        m.visitLabel(lInOk);

        m.visitTypeInsn(Opcodes.NEW, CRC);
        m.visitInsn(Opcodes.DUP);
        m.visitMethodInsn(Opcodes.INVOKESPECIAL, CRC, "<init>", "()V", false);
        m.visitVarInsn(Opcodes.ASTORE, 4);
        m.visitIntInsn(Opcodes.SIPUSH, 4096);
        m.visitIntInsn(Opcodes.NEWARRAY, Opcodes.T_BYTE);
        m.visitVarInsn(Opcodes.ASTORE, 5);

        Label lLoop = new Label();
        Label lEnd = new Label();
        m.visitLabel(lLoop);
        m.visitVarInsn(Opcodes.ALOAD, 3);
        m.visitVarInsn(Opcodes.ALOAD, 5);
        m.visitMethodInsn(Opcodes.INVOKEVIRTUAL, INPUT_STREAM,
                "read", "([B)I", false);
        m.visitInsn(Opcodes.DUP);
        m.visitVarInsn(Opcodes.ISTORE, 6);
        m.visitJumpInsn(Opcodes.IFLT, lEnd);
        m.visitVarInsn(Opcodes.ALOAD, 4);
        m.visitVarInsn(Opcodes.ALOAD, 5);
        m.visitInsn(Opcodes.ICONST_0);
        m.visitVarInsn(Opcodes.ILOAD, 6);
        m.visitMethodInsn(Opcodes.INVOKEVIRTUAL, CRC, "update", "([BII)V", false);
        m.visitJumpInsn(Opcodes.GOTO, lLoop);

        m.visitLabel(lEnd);
        m.visitVarInsn(Opcodes.ALOAD, 3);
        m.visitMethodInsn(Opcodes.INVOKEVIRTUAL, INPUT_STREAM, "close", "()V", false);
        m.visitVarInsn(Opcodes.ALOAD, 4);
        m.visitMethodInsn(Opcodes.INVOKEVIRTUAL, CRC, "getValue", "()J", false);
        m.visitInsn(Opcodes.L2I);
        m.visitVarInsn(Opcodes.ILOAD, 0);
        Label lCrcOk = new Label();
        m.visitJumpInsn(Opcodes.IF_ICMPEQ, lCrcOk);
        throwFailure(m, FAIL_TYPES[random.nextInt(FAIL_TYPES.length)]);
        m.visitLabel(lCrcOk);
    }

    private static void throwFailure(MethodNode m, String type) {
        m.visitTypeInsn(Opcodes.NEW, type);
        m.visitInsn(Opcodes.DUP);
        m.visitMethodInsn(Opcodes.INVOKESPECIAL, type, "<init>", "()V", false);
        m.visitInsn(Opcodes.ATHROW);
    }

    /** 生成混淆风格成员名（1~2 个小写字母），保证类内唯一。 */
    private static String freshObfName(Random random, ClassNode cn, boolean method) {
        while (true) {
            int len = 1 + random.nextInt(2);
            StringBuilder sb = new StringBuilder(len);
            for (int i = 0; i < len; i++) {
                sb.append((char) ('a' + random.nextInt(26)));
            }
            String name = sb.toString();
            if (method) {
                if (cn.methods == null || !hasMethod(cn, name)) {
                    return name;
                }
            } else {
                if (cn.fields == null || !hasField(cn, name)) {
                    return name;
                }
            }
        }
    }

    /** 找一个在所有分发类中都不冲突的共用混淆风格方法名。 */
    private static String freshSharedMethodName(Random random, ClassNode[] dispatchNodes) {
        for (int attempt = 0; attempt < 128; attempt++) {
            int len = 1 + random.nextInt(2);
            StringBuilder sb = new StringBuilder(len);
            for (int i = 0; i < len; i++) {
                sb.append((char) ('a' + random.nextInt(26)));
            }
            String name = sb.toString();
            boolean clash = false;
            for (ClassNode cn : dispatchNodes) {
                if (hasMethod(cn, name)) {
                    clash = true;
                    break;
                }
            }
            if (!clash) {
                return name;
            }
        }
        int serial = 0;
        while (true) {
            String name = "g" + serial++;
            boolean clash = false;
            for (ClassNode cn : dispatchNodes) {
                if (hasMethod(cn, name)) {
                    clash = true;
                    break;
                }
            }
            if (!clash) {
                return name;
            }
        }
    }

    private static boolean hasMethod(ClassNode cn, String name) {
        for (MethodNode mn : cn.methods) {
            if (mn.name.equals(name)) {
                return true;
            }
        }
        return false;
    }

    private static boolean hasField(ClassNode cn, String name) {
        for (FieldNode fn : cn.fields) {
            if (fn.name.equals(name)) {
                return true;
            }
        }
        return false;
    }

    private static MethodNode findMain(ClassNode cn) {
        if (cn.methods == null) {
            return null;
        }
        for (MethodNode mn : cn.methods) {
            if ("main".equals(mn.name)
                    && "([Ljava/lang/String;)V".equals(mn.desc)
                    && (mn.access & Opcodes.ACC_STATIC) != 0) {
                return mn;
            }
        }
        return null;
    }

    private static int crc32(byte[] data) {
        CRC32 crc = new CRC32();
        crc.update(data);
        return (int) crc.getValue();
    }
}
