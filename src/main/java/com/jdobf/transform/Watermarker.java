package com.jdobf.transform;

import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.ClassNode;

import java.nio.charset.StandardCharsets;
import java.util.Collection;

/**
 * 数字水印：把水印文本写入每个类的 SourceFile 值。
 *
 * class 文件头是魔数 CAFEBABE 与版本号（不可改动），随后立即是常量池；
 * ASM 在 visit() 阶段只分配 this_class/super_class 两个条目，紧接着
 * visitSource 分配的 UTF8 即为常量池第 3 个左右条目，字节位置在文件
 * 最顶部前几行——用 16 进制编辑器打开 class，第一眼即可看到水印，
 * 效果类似 Zelix KlassMaster 的 watermark。
 *
 * SourceFile 是 JVMS 标准调试属性：JVM 只做存储从不校验其内容，
 * 因此零运行时开销；水印文本左右各加三个空格（0x20），在 hex 视图的
 * ASCII 栏呈现为三格空白，与相邻的常量池数据自然区分。
 *
 * 该 UTF8 位于最终渲染字节中，暗桩链的 CRC 同样覆盖它，
 * 从受保护类上剥离水印会导致 CRC 自校验失败、拒绝启动。
 */
public final class Watermarker {

    /** 水印两侧的空白格数：hex 视图 ASCII 栏里左右各三个空格。 */
    public static final int PADDING = 3;

    /** 水印文本长度上限（SourceFile 是常量池 UTF8，上限 65535，此处保守取值）。 */
    public static final int MAX_TEXT_LENGTH = 240;

    private static final int ASM = Opcodes.ASM9;
    private static final String SPACES = "   ";

    private Watermarker() {
    }

    /**
     * 规整用户输入的水印文本：仅保留可打印 ASCII（0x20~0x7E），
     * 换行/制表符合并为空格，裁剪首尾空白并限长；为空时返回 null。
     */
    public static String normalize(String text) {
        if (text == null) {
            return null;
        }
        StringBuilder sb = new StringBuilder(text.length());
        for (int i = 0; i < text.length() && sb.length() < MAX_TEXT_LENGTH; i++) {
            char ch = text.charAt(i);
            if (ch == '\r' || ch == '\n' || ch == '\t') {
                sb.append(' ');
            } else if (ch >= 0x20 && ch <= 0x7E) {
                sb.append(ch);
            } else {
                sb.append('_');
            }
        }
        String out = sb.toString().trim();
        while (out.contains("  ")) {
            out = out.replace("  ", " ");
        }
        return out.isEmpty() ? null : out;
    }

    /** SourceFile 中写入的实际字符串：三格空格 + 水印 + 三格空格。 */
    public static String sourceName(String normalizedText) {
        return SPACES + normalizedText + SPACES;
    }

    /**
     * 给所有类节点挂水印（写 SourceFile 值）。
     * 必须在 StripDebug 之后/渲染之前设置，幂等可重复调用。
     */
    public static void attach(Collection<ClassNode> nodes, String normalizedText) {
        String value = sourceName(normalizedText);
        for (ClassNode cn : nodes) {
            cn.sourceFile = value;
            cn.sourceDebug = null;
        }
    }

    /**
     * 包一层 ClassVisitor：visit() 一结束（this/super 常量刚分配完）
     * 立刻发 visitSource，使水印 UTF8 排在常量池最前部；
     * 类自带的真实 SourceFile 回调一律忽略，防止顶掉水印。
     * 供不走 ClassNode 的路径（多版本条目 ClassRemapper 直写）使用。
     */
    public static ClassVisitor visitor(ClassVisitor cv, final String normalizedText) {
        final String value = sourceName(normalizedText);
        return new ClassVisitor(ASM, cv) {
            private boolean watermarkEmitted;

            @Override
            public void visit(int version, int access, String name, String signature,
                              String superName, String[] interfaces) {
                super.visit(version, access, name, signature, superName, interfaces);
                super.visitSource(value, null);
                watermarkEmitted = true;
            }

            @Override
            public void visitSource(String source, String debug) {
                // 真实 SourceFile 被水印顶替，不向下传递
                if (!watermarkEmitted) {
                    super.visitSource(source, debug);
                }
            }
        };
    }

    /** 仅供诊断/测试：按 US_ASCII 取字节。 */
    public static byte[] bytes(String text) {
        return text.getBytes(StandardCharsets.US_ASCII);
    }
}
