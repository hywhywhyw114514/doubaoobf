package com.jdobf.core;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * 混淆名生成器。
 *
 * 两种风格：
 * <ul>
 *   <li>{@link Style#NORMAL}：纯 a-zA-Z 计数器编码，名字合法且唯一；</li>
 *   <li>{@link Style#BRAINDEAD}（“更脑残的 rename”）：学习 LightStarGuard
 *       示例 jar 的命名手法——
 *       <ul>
 *         <li>类名：ASCII 前缀 caobi + 一个稀有基字符（希腊/古教会西里尔/IPA）
 *             + 八十余个字符，主体为 U+0300-U+036F 组合附加符号，
 *             中间随机撒入稀有西里尔/希腊/IPA/生僻汉字，
 *             反编译器里显示为一大串叠字乱码；</li>
 *         <li>方法/字段名：只由 I（大写 i）、l（小写 L）、1（数字一）
 *             三种视觉上几乎无法区分的字符组成的长串；</li>
 *         <li>包名：两个小写 ASCII 字母（如 sb 风格）。</li>
 *       </ul>
 *       所有字符均为 BMP 合法字符，不含 . ; [ /，可直接写入常量池并被 JVM 加载。
 *       调用方（GlobalRemapper）仍会用 used 集合去重，因此随机流即使极小概率
 *       撞名也会重新生成，并带计数器兜底保证永不死循环。
 * </ul>
 */
public class NameGenerator {

    public enum Style {
        /** 普通风格：a-zA-Z 短名 */
        NORMAL,
        /** 更脑残的 rename：caobi 组合符号类名 + I/l/1 眼瞎成员名 */
        BRAINDEAD
    }

    private static final char[] ALPHABET = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".toCharArray();

    /** 眼瞎三件套：大写 I、小写 l、数字 1，多数等宽字体里完全一模一样 */
    private static final char[] HOMOGLYPH = {'I', 'l', '1'};

    /** caobi 之后紧跟的稀有“基字符”：希腊/古西里尔/IPA 怪字母 */
    private static final char[] WEIRD_BASES = {
            0x03C7, // χ Greek chi
            0x03A7, // Χ Greek capital chi
            0x03BB, // λ
            0x03B8, // θ
            0x03C9, // ω
            0x04A0, // Ҡ
            0x0495, // ҕ
            0x04B8, // Ҹ
            0x04AC, // Ҭ
            0x046A, // Ѫ
            0x04F6, // Ӷ
            0x0294, // ʔ
            0x0295, // ʕ
            0x02A1, // ʡ
            0x0277, // ɷ
            0x01A2, // Ƣ
    };

    /** 西里尔稀有字母（0460-04FF 扩展段，避开常见俄文字母的观感） */
    private static final char[] CYRILLIC_RARE = collectLetters(0x0460, 0x04FF, false);
    /** 希腊字母 */
    private static final char[] GREEK_LETTERS = collectLetters(0x0370, 0x03FF, false);
    /** 拉丁扩展 + IPA 怪字母 */
    private static final char[] LATIN_IPA = concat(
            collectLetters(0x0180, 0x024F, false),
            collectLetters(0x0250, 0x02AF, true));
    /** 生僻汉字（CJK 统一表意文字开头一小段，符号化观感） */
    private static final char[] RARE_CJK = collectLetters(0x4E00, 0x4E6F, false);
    /** 组合附加符号 U+0300-U+036F + 西里尔组合号 U+0483-U+0489 */
    private static final char[] COMBINING_MARKS = concat(
            collectMarks(0x0300, 0x036F),
            collectMarks(0x0483, 0x0489));

    private final Style style;

    private long counter;
    private final Random random;

    public NameGenerator() {
        this(Style.NORMAL);
    }

    public NameGenerator(Style style) {
        // 未显式给种子时按运行时熵随机，避免独立使用时退化为固定序列
        this(style, new Random().nextLong() ^ System.nanoTime());
    }

    public NameGenerator(Style style, long seed) {
        this.style = style == null ? Style.NORMAL : style;
        this.random = new Random(seed);
    }

    public Style style() {
        return style;
    }

    /**
     * 生成下一个成员名（方法/字段）：
     * NORMAL 为 a-zA-Z 计数名；BRAINDEAD 为 I/l/1 眼瞎长名。
     */
    public String next() {
        if (style == Style.BRAINDEAD) {
            return nextHomoglyph(26 + random.nextInt(16), false);
        }
        long n = counter++;
        StringBuilder sb = new StringBuilder();
        // 首字符必须是字母，整个字母表都是字母，直接编码即可
        do {
            sb.append(ALPHABET[(int) (n % ALPHABET.length)]);
            n /= ALPHABET.length;
        } while (n > 0);
        return sb.toString();
    }

    /**
     * 生成下一个类的简单名。
     * NORMAL 与 {@link #next()} 相同；
     * BRAINDEAD 为 caobi + 稀有基字符 + 组合符号海。
     */
    public String nextClassName() {
        if (style != Style.BRAINDEAD) {
            return next();
        }
        StringBuilder sb = new StringBuilder("caobi");
        sb.append(WEIRD_BASES[random.nextInt(WEIRD_BASES.length)]);
        int tail = 80 + random.nextInt(10);
        for (int i = 0; i < tail; i++) {
            int r = random.nextInt(100);
            if (r < 70) {
                // 绝大多数是组合附加符号：不占宽度，全部叠在前一个基字符上
                sb.append(COMBINING_MARKS[random.nextInt(COMBINING_MARKS.length)]);
            } else if (r < 84) {
                sb.append(CYRILLIC_RARE[random.nextInt(CYRILLIC_RARE.length)]);
            } else if (r < 90) {
                sb.append(COMBINING_MARKS[random.nextInt(COMBINING_MARKS.length)]);
                sb.append(COMBINING_MARKS[random.nextInt(COMBINING_MARKS.length)]);
                i++;
            } else if (r < 95) {
                sb.append(GREEK_LETTERS[random.nextInt(GREEK_LETTERS.length)]);
            } else if (r < 98) {
                sb.append(LATIN_IPA[random.nextInt(LATIN_IPA.length)]);
            } else {
                sb.append(RARE_CJK[random.nextInt(RARE_CJK.length)]);
            }
        }
        return sb.toString();
    }

    /**
     * 生成“ASCII 安全”的类简单名（纯 I/l/1）。
     * 用于必须出现在 MANIFEST.MF / META-INF/services 等纯文本资源里的类：
     * 既保持眼瞎观感（与示例里的 IlIlll... 一致），又不依赖资源文件的 Unicode 编码兼容。
     */
    public String nextAsciiClassName() {
        if (style != Style.BRAINDEAD) {
            return next();
        }
        return nextHomoglyph(28 + random.nextInt(8), true);
    }

    /**
     * 生成包路径的最后一段：
     * NORMAL 为 a-zA-Z 计数名；BRAINDEAD 为两位小写字母（sb 风格）。
     */
    public String nextPackageLeaf() {
        if (style != Style.BRAINDEAD) {
            return next();
        }
        StringBuilder sb = new StringBuilder();
        sb.append((char) ('a' + random.nextInt(26)));
        sb.append((char) ('a' + random.nextInt(26)));
        return sb.toString();
    }

    /** 计数器兜底名：随机流耗尽/撞名时保证调用方一定能拿到唯一名字。 */
    public String fallbackName() {
        if (style != Style.BRAINDEAD) {
            return next();
        }
        long n = counter++;
        StringBuilder sb = new StringBuilder("z");
        do {
            sb.append(HOMOGLYPH[(int) (n % HOMOGLYPH.length)]);
            n /= HOMOGLYPH.length;
        } while (n > 0);
        return sb.toString();
    }

    private String nextHomoglyph(int len, boolean asciiClass) {
        StringBuilder sb = new StringBuilder(len);
        // 类名首字符不用数字 1（某些老旧工具只按 Java 源标识符规则识别类名），
        // 方法/字段名无此顾虑。
        sb.append(HOMOGLYPH[random.nextInt(asciiClass ? 2 : 3)]);
        for (int i = 1; i < len; i++) {
            sb.append(HOMOGLYPH[random.nextInt(HOMOGLYPH.length)]);
        }
        return sb.toString();
    }

    /** 随机 int，仅用于字节码模式多样化，不参与命名 */
    public int randomInt() {
        return random.nextInt();
    }

    public int randomInt(int bound) {
        return bound <= 0 ? 0 : random.nextInt(bound);
    }

    // ------------------------------------------------------------------
    // 字符集构建：按 Unicode 类别过滤，自动剔除未分配码位
    // ------------------------------------------------------------------

    private static char[] collectLetters(int from, int to, boolean includeModifier) {
        List<Character> list = new ArrayList<Character>();
        for (int c = from; c <= to; c++) {
            int t = Character.getType(c);
            if (t == Character.UPPERCASE_LETTER || t == Character.LOWERCASE_LETTER
                    || t == Character.OTHER_LETTER
                    || (includeModifier && t == Character.MODIFIER_LETTER)) {
                list.add((char) c);
            }
        }
        return toArray(list);
    }

    private static char[] collectMarks(int from, int to) {
        List<Character> list = new ArrayList<Character>();
        for (int c = from; c <= to; c++) {
            int t = Character.getType(c);
            if (t == Character.NON_SPACING_MARK || t == Character.ENCLOSING_MARK) {
                list.add((char) c);
            }
        }
        return toArray(list);
    }

    private static char[] toArray(List<Character> list) {
        char[] arr = new char[list.size()];
        for (int i = 0; i < arr.length; i++) {
            arr[i] = list.get(i);
        }
        return arr;
    }

    private static char[] concat(char[] a, char[] b) {
        char[] r = new char[a.length + b.length];
        System.arraycopy(a, 0, r, 0, a.length);
        System.arraycopy(b, 0, r, a.length, b.length);
        return r;
    }
}
