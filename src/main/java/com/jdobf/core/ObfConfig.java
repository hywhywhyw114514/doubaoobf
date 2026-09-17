package com.jdobf.core;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * 混淆配置。所有开关与强度都在这里集中管理。
 */
public class ObfConfig implements Serializable {

    private static final long serialVersionUID = 1L;

    /** 输入 jar */
    public String inputJar;
    /** 输出 jar */
    public String outputJar;

    /** 重命名类 */
    public boolean renameClasses = true;
    /** 重命名包 */
    public boolean renamePackages = false;
    /** 重命名方法 */
    public boolean renameMethods = true;
    /** 重命名字段 */
    public boolean renameFields = true;

    /**
     * 重命名风格。NORMAL 为常规 a-zA-Z 短名；
     * BRAINDEAD 为“更脑残的 rename”：类名 caobi+组合附加符号海，
     * 方法/字段为 I/l/1 眼瞎长名，包名为两位小写字母。
     */
    public RenameStyle renameStyle = RenameStyle.NORMAL;

    /** 重命名风格 */
    public enum RenameStyle {
        /** 常规 a-zA-Z */
        NORMAL,
        /** 更脑残的 rename（caobi 组合符号类名 + I/l/1 眼瞎名） */
        BRAINDEAD
    }

    /** 字符串加密 */
    public boolean encryptStrings = false;
    /** 数字常量混淆 */
    public boolean obfuscateNumbers = false;
    /** 控制流混淆（多点随机不透明谓词，模板/极性/死分支每构建随机） */
    public boolean controlFlow = false;
    /**
     * 逻辑分散：把构造器/方法中操作字段的直线语句随机外提到多个 private
     * 合成方法（原位置只留随机名调用），并把非递归实例方法（含构造器）的
     * 局部变量随机提升为实例字段。消除"真实业务语句连续聚成一块"和
     * "局部变量一眼可数"的形态。每构建提升/外提的选择随机。
     */
    public boolean disperseLogic = false;
    /** 控制流平坦化（全方法 switch 状态机，激进，显著增大体积） */
    public boolean flattenControlFlow = false;
    /**
     * 反编译器抗性：在完成其它控制流变换后追加稀疏状态入口和不可达异常岛。
     * 只生成 JVM 可验证字节码，用于降低 Procyon 等结构化反编译器的还原质量。
     */
    public boolean decompilerHardening = false;
    /** 抗性等级：1=稀疏入口，2=入口 + 单异常岛，3=入口 + 重叠异常岛。 */
    public int decompilerHardeningPasses = 3;
    /** 垃圾代码注入（向已有类注入永不调用的垃圾方法） */
    public boolean junkCode = false;
    /**
     * 屎山脑残混淆：每个类灌入海量巨型假方法（深层嵌套循环/分叉/switch/
     * 互调/数组/字符串拼接），并在所有真实方法体内高密度插入栈中性脑残
     * 代码片段。几行代码可膨胀成上万行，体积可能放大几十到上千倍。
     */
    public boolean shitBloat = false;
    /** 屎山模式每个类注入的巨型假方法数（0..400） */
    public int shitMethodsPerClass = 60;
    /**
     * j2c 原生下沉：把合格静态方法从 Java 类中抽走转为 native，真实（已混淆）
     * 字节码加密后嵌入 C++ 源码，编译进 64 位 DLL；运行时 JNI 桥接把隐藏类
     * 在原 ClassLoader 中重新 DefineClass 并转发调用。Java 层只留下不含真实
     * 逻辑的虚假类（塞满垃圾方法）。当前仅支持 Windows x64（需 MSVC 或 g++）。
     */
    public boolean j2c = false;
    /**
     * VMProtect 加壳（需要 j2c）：j2c 的 loader 与双 payload 编译后，先以
     * SDK 标记（虚拟化/变异/Ultra）包裹全部 JNI 函数，再调用内置的
     * VMProtect_Con 加壳（打包压缩 + 用户态反调试 + 内存保护；不启用反
     * 虚拟机以免误伤云主机/CI/沙箱用户）。loader 前置进 jar 头部、payload
     * 再经 XOR 加密入资源，落盘产物的关键段全部呈高熵。仅 Windows x64，
     * 找不到内置 VMP 时自动降级为普通 j2c 并告警。
     */
    public boolean vmpPack = false;
    /**
     * j2c 两个加密 native payload 在产出 jar 内的资源条目名模板（留空 = 每构建
     * 随机伪装名）。支持占位符 {@code {}}，分别替换为 1/2，例如
     * {@code native/engine{}.dat} → {@code native/engine1.dat}、
     * {@code native/engine2.dat}；不含占位符时序号自动插入到扩展名前
     * （{@code x.bin} → {@code x1.bin}/{@code x2.bin}）。仅允许相对路径、
     * ASCII 可见字符，非法或与现有条目冲突时回退为随机名并给出警告。
     */
    public String j2cNativeName = "";
    /** 死代码/伪代码类注入（生成大量看似真实的独立类，内含不透明谓词） */
    public boolean deadCodeClasses = false;
    /**
     * 类拆分与重定向：把真实类里的静态方法整体迁移到伪代码类中藏匿，
     * 原方法只留转发桩；部分伪代码类永远拿不到真方法、保持纯诱饵。
     * 必须先开启 {@link #deadCodeClasses}。
     */
    public boolean splitRedirect = false;
    /** 剥离调试信息（源码文件、行号、局部变量名） */
    public boolean stripDebug = true;
    /** 保留 Serializable 类的实例字段名 */
    public boolean keepSerializableFields = true;
    /** 混淆完成后在输出 jar 旁导出重命名映射表 */
    public boolean exportMapping = true;
    /** 嵌入数字水印（类级自定义属性，16 进制打开 class 可见，运行时被 JVM 忽略） */
    public boolean watermarkEnabled = true;
    /** 水印文本（仅保留可打印 ASCII，长度上限见 Watermarker） */
    public String watermarkText = "Doubaoobf";

    /** 控制流注入层数 1-3 */
    public int controlFlowPasses = 2;
    /** 每个类注入的垃圾方法数 */
    public int junkMethodsPerClass = 3;
    /** 生成的死代码/伪代码类数量 */
    public int deadClassCount = 0;

    /** 在树形界面中勾选的类（内部名） */
    public List<String> excludedClasses = new ArrayList<String>();
    /** 在树形界面中勾选的包路径（以 / 结尾） */
    public List<String> excludedPackages = new ArrayList<String>();
    /** 正则排除规则文本，每行一条，匹配类内部名，例如 ^com/foo/.*$ */
    public String exclusionRegexText = "";

    private transient List<Pattern> compiledPatterns;

    /** 强度预设 */
    public enum Preset {
        OFF,        // 不混淆
        LIGHT,      // 轻量
        MEDIUM,     // 中等
        AGGRESSIVE, // 激进
        CUSTOM      // 自定义
    }

    public void applyPreset(Preset preset) {
        switch (preset) {
            case OFF:
                renameClasses = renamePackages = renameMethods = renameFields = false;
                encryptStrings = obfuscateNumbers = controlFlow = flattenControlFlow = false;
                decompilerHardening = false;
                junkCode = deadCodeClasses = shitBloat = j2c = false;
                disperseLogic = false;
                stripDebug = false;
                controlFlowPasses = 1;
                junkMethodsPerClass = 0;
                shitMethodsPerClass = 60;
                deadClassCount = 0;
                break;
            case LIGHT:
                renameClasses = true;
                renamePackages = false;
                renameMethods = true;
                renameFields = true;
                encryptStrings = false;
                obfuscateNumbers = false;
                controlFlow = false;
                disperseLogic = false;
                flattenControlFlow = false;
                decompilerHardening = false;
                junkCode = false;
                shitBloat = false;
                j2c = false;
                deadCodeClasses = false;
                stripDebug = true;
                controlFlowPasses = 1;
                junkMethodsPerClass = 0;
                deadClassCount = 0;
                break;
            case MEDIUM:
                renameClasses = true;
                renamePackages = true;
                renameMethods = true;
                renameFields = true;
                encryptStrings = true;
                obfuscateNumbers = true;
                controlFlow = false;
                disperseLogic = true;
                flattenControlFlow = false;
                decompilerHardening = false;
                junkCode = false;
                shitBloat = false;
                j2c = false;
                deadCodeClasses = true;
                stripDebug = true;
                controlFlowPasses = 2;
                junkMethodsPerClass = 2;
                deadClassCount = 6;
                break;
            case AGGRESSIVE:
                renameClasses = true;
                renamePackages = true;
                renameMethods = true;
                renameFields = true;
                encryptStrings = true;
                obfuscateNumbers = true;
                controlFlow = true;
                disperseLogic = true;
                flattenControlFlow = true;
                decompilerHardening = true;
                junkCode = true;
                shitBloat = false;
                j2c = false;
                deadCodeClasses = true;
                stripDebug = true;
                controlFlowPasses = 3;
                junkMethodsPerClass = 5;
                deadClassCount = 20;
                break;
            case CUSTOM:
            default:
                break;
        }
    }

    private List<Pattern> patterns() {
        if (compiledPatterns == null) {
            compiledPatterns = new ArrayList<Pattern>();
            if (exclusionRegexText != null) {
                for (String line : exclusionRegexText.split("\n")) {
                    String t = line.trim();
                    if (!t.isEmpty() && !t.startsWith("#")) {
                        try {
                            compiledPatterns.add(Pattern.compile(t));
                        } catch (Exception ignored) {
                            // 非法正则直接忽略
                        }
                    }
                }
            }
        }
        return compiledPatterns;
    }

    /** 判断类（内部名，如 com/foo/Bar）是否被排除 */
    public boolean isClassExcluded(String internalName) {
        for (String c : excludedClasses) {
            if (c.equals(internalName)) {
                return true;
            }
        }
        for (String p : excludedPackages) {
            String prefix = p.endsWith("/") ? p : p + "/";
            if (internalName.startsWith(prefix)) {
                return true;
            }
        }
        for (Pattern pat : patterns()) {
            if (pat.matcher(internalName).matches()) {
                return true;
            }
        }
        return false;
    }

    public boolean anyTransformEnabled() {
        return renameClasses || renamePackages || renameMethods || renameFields
                || encryptStrings || obfuscateNumbers || controlFlow
                || flattenControlFlow || junkCode || shitBloat || j2c || deadCodeClasses
                || splitRedirect || stripDebug || disperseLogic || vmpPack
                || decompilerHardening;
    }
}
