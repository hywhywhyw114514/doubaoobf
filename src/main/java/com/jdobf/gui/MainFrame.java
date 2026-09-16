package com.jdobf.gui;

import com.formdev.flatlaf.FlatDarkLaf;
import com.formdev.flatlaf.FlatLaf;
import com.formdev.flatlaf.FlatLightLaf;
import com.jdobf.core.ObfConfig;
import com.jdobf.core.Obfuscator;
import com.jdobf.transform.ShitBloat;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.JScrollPane;
import javax.swing.JSpinner;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;
import javax.swing.UIManager;
import javax.swing.border.CompoundBorder;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.RenderingHints;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

/**
 * 混淆器主界面（FlatLaf 现代风格：卡片式分区、圆角、浅/深主题切换）。
 * 仅界面层现代化，所有控件字段与业务行为保持不变。
 */
public class MainFrame extends JFrame {

    private final JTextField inputField = new JTextField(28);
    private final JTextField outputField = new JTextField(28);

    private final CheckBoxTree tree = new CheckBoxTree();
    private final JTextArea regexArea = new JTextArea(4, 30);

    private final JComboBox<String> presetBox =
            new JComboBox<String>(new String[]{"自定义", "关闭（不混淆）", "轻量", "中等", "激进"});
    private final JCheckBox chkRenameClasses = new JCheckBox("类名重命名", true);
    private final JCheckBox chkRenamePackages = new JCheckBox("包名重命名", false);
    private final JCheckBox chkRenameMethods = new JCheckBox("方法重命名", true);
    private final JCheckBox chkRenameFields = new JCheckBox("字段重命名", true);
    private final JCheckBox chkBraindeadRename =
            new JCheckBox("更脑残的 rename（类名 caobi+组合符号海，方法/字段 I/l/1 眼瞎名）", false);
    private final JCheckBox chkStrings = new JCheckBox("字符串加密", false);
    private final JCheckBox chkNumbers = new JCheckBox("数字常量混淆", false);
    private final JCheckBox chkControlFlow = new JCheckBox("控制流混淆", false);
    private final JCheckBox chkFlatten = new JCheckBox("控制流平坦化（switch 状态机）", false);
    private final JCheckBox chkDisperse =
            new JCheckBox("逻辑分散（语句外提 + 局部变量转字段）", false);
    private final JCheckBox chkJunk = new JCheckBox("垃圾方法注入（每类注入无用方法）", false);
    private final JCheckBox chkShitBloat =
            new JCheckBox("屎山脑残混淆（假方法海+真实代码灌屎，几行变上万行）", false);
    private final JCheckBox chkJ2c =
            new JCheckBox("j2c 原生下沉（混淆后真实逻辑转 C++/DLL，Java 层只剩虚假类）", false);
    private final JCheckBox chkVmp =
            new JCheckBox("VMProtect 加壳（j2c 产物虚拟化+变异，需 j2c，仅 Win64）", false);
    private final JTextField j2cNameField = new JTextField(22);
    private final JSpinner shitCount =
            new JSpinner(new javax.swing.SpinnerNumberModel(60, 0, 400, 1));
    private final JCheckBox chkDeadClasses =
            new JCheckBox("伪代码类注入（生成逼真死代码类/不透明谓词）", false);
    private final JCheckBox chkSplitRedirect =
            new JCheckBox("类拆分与重定向（真实逻辑拆入伪代码类藏匿）", false);
    private final JCheckBox chkStrip = new JCheckBox("剥离调试信息", true);
    private final JCheckBox chkKeepSerializable = new JCheckBox("保留 Serializable 字段", true);
    private final JCheckBox chkExportMapping = new JCheckBox("导出重命名映射表", true);
    private final JCheckBox chkWatermark = new JCheckBox("数字水印（hex 打开可见）", true);
    private final JTextField watermarkField = new JTextField("Doubaoobf", 18);
    private final JSpinner flowPasses = new JSpinner(new javax.swing.SpinnerNumberModel(2, 1, 3, 1));
    private final JSpinner junkCount = new JSpinner(new javax.swing.SpinnerNumberModel(3, 0, 20, 1));
    /** 伪代码类数量上限：spinner 模型与预设回填 clamp 的单一真源。 */
    private static final int MAX_DEAD_CLASSES = 10000;
    private final JSpinner deadClassCount =
            new JSpinner(new javax.swing.SpinnerNumberModel(0, 0, MAX_DEAD_CLASSES, 1));

    private final JProgressBar progressBar = new JProgressBar();
    private final JTextArea logArea = new JTextArea();
    private final JButton startButton = new JButton("开始混淆");
    private JButton themeButton;

    /** 需要随主题换色的文字标签 */
    private final List<JLabel> cardTitles = new ArrayList<JLabel>();
    private JLabel headerTitle;
    private JLabel headerSubtitle;
    private JLabel dropHint;
    private JLabel regexHint;

    private boolean syncingPreset = false;
    private boolean darkMode = false;

    public MainFrame() {
        super("豆包 Java 字节码混淆器");
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        setMinimumSize(new Dimension(920, 640));
        setSize(1060, 780);
        setLocationRelativeTo(null);
        setContentPane(buildContent());
        wireEvents();
        installJarDropSupport();
        applyPreset(ObfConfig.Preset.MEDIUM, 3); // 默认中等
        applyDynamicColors();
        getRootPane().setDefaultButton(startButton);
    }

    // ------------------------------------------------------------------
    // 界面构建
    // ------------------------------------------------------------------

    private JComponent buildContent() {
        JPanel root = new JPanel(new BorderLayout(0, 12));
        root.setBorder(BorderFactory.createEmptyBorder(14, 16, 14, 16));

        Box north = Box.createVerticalBox();
        JComponent header = buildHeader();
        header.setAlignmentX(Component.LEFT_ALIGNMENT);
        north.add(header);
        north.add(Box.createVerticalStrut(12));
        JComponent fileCard = buildFileCard();
        fileCard.setAlignmentX(Component.LEFT_ALIGNMENT);
        north.add(fileCard);
        root.add(north, BorderLayout.NORTH);

        JTabbedPane tabs = new JTabbedPane();
        tabs.addTab("混淆选项", wrapScroll(buildOptionsPanel()));
        tabs.addTab("排除项（不混淆的类/包）", wrapScroll(buildExcludePanel()));
        root.add(tabs, BorderLayout.CENTER);

        root.add(buildConsoleCard(), BorderLayout.SOUTH);
        return root;
    }

    /** 标题栏：产品名 + 副标题 + 主题切换 */
    private JComponent buildHeader() {
        JPanel h = new JPanel(new BorderLayout());
        h.setOpaque(false);

        Box left = Box.createVerticalBox();
        headerTitle = new JLabel("豆包 Java 字节码混淆器");
        headerTitle.setFont(headerTitle.getFont().deriveFont(Font.BOLD, 20f));
        headerTitle.setAlignmentX(Component.LEFT_ALIGNMENT);
        headerSubtitle = new JLabel("ASM 9 字节码变换 · 拖入 JAR 即可开始");
        headerSubtitle.setFont(headerSubtitle.getFont().deriveFont(Font.PLAIN, 12f));
        headerSubtitle.setAlignmentX(Component.LEFT_ALIGNMENT);
        left.add(headerTitle);
        left.add(Box.createVerticalStrut(2));
        left.add(headerSubtitle);
        h.add(left, BorderLayout.WEST);

        themeButton = new JButton("深色模式");
        themeButton.setFocusPainted(false);
        themeButton.putClientProperty("JButton.buttonType", "roundRect");
        JPanel right = new JPanel(new FlowLayout(FlowLayout.RIGHT, 0, 0));
        right.setOpaque(false);
        right.add(themeButton);
        h.add(right, BorderLayout.EAST);
        return h;
    }

    /** 输入/输出 JAR 卡片 */
    private JComponent buildFileCard() {
        Card card = new Card("JAR 文件");
        JPanel p = new JPanel(new GridBagLayout());
        p.setOpaque(false);
        GridBagConstraints c = new GridBagConstraints();
        c.insets = new Insets(3, 2, 3, 8);
        c.anchor = GridBagConstraints.WEST;

        c.gridx = 0; c.gridy = 0;
        p.add(new JLabel("输入 JAR："), c);
        c.gridx = 1; c.weightx = 1; c.fill = GridBagConstraints.HORIZONTAL;
        p.add(inputField, c);
        c.gridx = 2; c.weightx = 0; c.fill = GridBagConstraints.NONE;
        JButton browseIn = new JButton("浏览…");
        browseIn.setFocusPainted(false);
        browseIn.addActionListener(e -> chooseInput());
        p.add(browseIn, c);

        c.gridx = 0; c.gridy = 1;
        p.add(new JLabel("输出 JAR："), c);
        c.gridx = 1; c.weightx = 1; c.fill = GridBagConstraints.HORIZONTAL;
        p.add(outputField, c);
        c.gridx = 2; c.weightx = 0; c.fill = GridBagConstraints.NONE;
        JButton browseOut = new JButton("浏览…");
        browseOut.setFocusPainted(false);
        browseOut.addActionListener(e -> chooseOutput());
        p.add(browseOut, c);

        JPanel wrap = new JPanel(new BorderLayout(0, 6));
        wrap.setOpaque(false);
        wrap.add(p, BorderLayout.CENTER);
        dropHint = new JLabel("提示：可直接将 .jar 文件拖放到窗口任意位置以设置输入 JAR");
        dropHint.setFont(dropHint.getFont().deriveFont(Font.PLAIN, 12f));
        wrap.add(dropHint, BorderLayout.SOUTH);
        card.setContent(wrap);
        return card;
    }

    private JComponent buildExcludePanel() {
        JPanel p = new JPanel(new BorderLayout(0, 12));
        p.setBorder(BorderFactory.createEmptyBorder(6, 4, 6, 4));
        p.setOpaque(false);

        tree.setOpaque(false);
        JScrollPane treeScroll = new JScrollPane(tree);
        treeScroll.setBorder(BorderFactory.createEmptyBorder());
        treeScroll.getViewport().setOpaque(false);
        treeScroll.getVerticalScrollBar().setUnitIncrement(16);
        Card treeCard = new Card("勾选后该类/包不参与混淆（包为递归排除）");
        treeCard.setContent(treeScroll);
        p.add(treeCard, BorderLayout.CENTER);

        regexHint = new JLabel("正则排除（每行一条，匹配类内部名，例如  ^com/foo/.*$）：");
        regexHint.setFont(regexHint.getFont().deriveFont(Font.PLAIN, 12f));
        regexArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 13));
        JScrollPane regexScroll = new JScrollPane(regexArea);
        regexScroll.setPreferredSize(new Dimension(500, 96));
        Card regexCard = new Card("正则排除规则");
        JPanel regexWrap = new JPanel(new BorderLayout(0, 6));
        regexWrap.setOpaque(false);
        regexWrap.add(regexHint, BorderLayout.NORTH);
        regexWrap.add(regexScroll, BorderLayout.CENTER);
        regexCard.setContent(regexWrap);
        p.add(regexCard, BorderLayout.SOUTH);
        return p;
    }

    private JComponent buildOptionsPanel() {
        Box list = Box.createVerticalBox();
        list.setBorder(BorderFactory.createEmptyBorder(6, 4, 6, 4));

        // —— 强度预设 + 数量参数 ——
        Card presetCard = new Card("混淆强度");
        JPanel presetRow = new JPanel(new FlowLayout(FlowLayout.LEFT, 10, 0));
        presetRow.setOpaque(false);
        presetRow.add(new JLabel("预设："));
        presetBox.setPreferredSize(new Dimension(172, 28));
        presetRow.add(presetBox);
        presetRow.add(Box.createHorizontalStrut(16));
        presetRow.add(new JLabel("控制流层数："));
        flowPasses.setPreferredSize(new Dimension(58, 28));
        presetRow.add(flowPasses);
        presetRow.add(Box.createHorizontalStrut(10));
        presetRow.add(new JLabel("每类垃圾方法数："));
        junkCount.setPreferredSize(new Dimension(64, 28));
        presetRow.add(junkCount);
        presetRow.add(Box.createHorizontalStrut(10));
        presetRow.add(new JLabel("伪代码类数量："));
        deadClassCount.setPreferredSize(new Dimension(76, 28));
        presetRow.add(deadClassCount);
        presetRow.add(Box.createHorizontalStrut(10));
        presetRow.add(new JLabel("屎山每类假方法数："));
        shitCount.setPreferredSize(new Dimension(64, 28));
        presetRow.add(shitCount);
        presetCard.setContent(presetRow);
        list.add(presetCard);
        list.add(Box.createVerticalStrut(12));

        // —— 重命名 ——
        Card renameCard = new Card("重命名");
        JPanel renameGrid = new JPanel(new GridBagLayout());
        renameGrid.setOpaque(false);
        addCheck(renameGrid, 0, 0, chkRenameClasses);
        addCheck(renameGrid, 1, 0, chkRenamePackages);
        addCheck(renameGrid, 0, 1, chkRenameMethods);
        addCheck(renameGrid, 1, 1, chkRenameFields);
        GridBagConstraints braindeadGbc = new GridBagConstraints();
        braindeadGbc.gridx = 0;
        braindeadGbc.gridy = 2;
        braindeadGbc.gridwidth = 2;
        braindeadGbc.anchor = GridBagConstraints.WEST;
        braindeadGbc.insets = new Insets(4, 4, 4, 20);
        chkBraindeadRename.setToolTipText(

"<html><div style='width:380px'>"
+ "学习 LightStarGuard 风格的脑残命名：<br>"
+ "· 类名：caobi + 希腊/古西里尔/IPA 基字符 + 80 余个组合附加符号，"
+ "反编译器里显示成一整串叠字乱码；<br>"
+ "· 方法/字段名：只由 I（大写i）、l（小写L）、1（数字一）组成，肉眼完全分不清；<br>"
+ "· 包名：两位小写字母（如 sb）；<br>"
+ "· MANIFEST 入口类与 META-INF/services 相关类自动使用 I/l/1 纯 ASCII 名，保证可启动。"
+ "</div></html>");
        renameGrid.add(chkBraindeadRename, braindeadGbc);
        renameCard.setContent(renameGrid);
        list.add(renameCard);
        list.add(Box.createVerticalStrut(12));

        // —— 代码保护 ——
        Card protectCard = new Card("代码保护");
        JPanel protectGrid = new JPanel(new GridBagLayout());
        protectGrid.setOpaque(false);
        addCheck(protectGrid, 0, 0, chkStrings);
        addCheck(protectGrid, 1, 0, chkNumbers);
        addCheck(protectGrid, 0, 1, chkControlFlow);
        addCheck(protectGrid, 1, 1, chkJunk);
        addCheck(protectGrid, 0, 2, chkFlatten);
        addCheck(protectGrid, 1, 2, chkDeadClasses);
        GridBagConstraints wide = new GridBagConstraints();
        wide.gridx = 0;
        wide.gridy = 3;
        wide.gridwidth = 2;
        wide.anchor = GridBagConstraints.WEST;
        wide.insets = new Insets(4, 4, 4, 4);
        protectGrid.add(chkSplitRedirect, wide);
        chkShitBloat.setToolTipText(
"<html><div style='width:400px'>"
+ "极端体积膨胀，纯属整活/恶心逆向，<b>产出 jar 可能放大几十到上千倍</b>：<br>"
+ "· 每个类注入几十~上百个巨型假方法：3-5 层嵌套循环、恒假分叉、<br>"
+ "&nbsp;&nbsp;TABLESWITCH 假分支、假方法互调长链、int 数组填充求和、<br>"
+ "&nbsp;&nbsp;StringBuilder 拼接取 hashCode，单方法反编译几百上千行；<br>"
+ "· 所有真实方法体内也高密度插入栈中性脑残片段（只写专用垃圾槽），<br>"
+ "&nbsp;&nbsp;几行业务代码反编译可达上万行；<br>"
+ "· 语义完全不变，无除法/空指针/越界，产出经多 JDK -Xverify:all 校验；<br>"
+ "· 数量旋钮为每类假方法数（0-400），越大越炸裂、混淆越慢。"
+ "</div></html>");
        GridBagConstraints shitGbc = new GridBagConstraints();
        shitGbc.gridx = 0;
        shitGbc.gridy = 4;
        shitGbc.gridwidth = 2;
        shitGbc.anchor = GridBagConstraints.WEST;
        shitGbc.insets = new Insets(4, 4, 4, 20);
        protectGrid.add(chkShitBloat, shitGbc);
        chkJ2c.setToolTipText(
"<html><div style='width:420px'>"
+ "把混淆后的合格静态方法整体抽走转为 JNI native：<br>"
+ "· 真实（已混淆）字节码 XOR 加密嵌入 DLL，运行时由原生桥接重新翻译回 JVM 执行；<br>"
+ "· Java 层对应方法只剩 native 声明 + 满是无用逻辑的虚假类，无一丝真实代码；<br>"
+ "· 仅支持 <b>Windows x64</b>，需要本机安装 Visual Studio（C++ 工具链）或 g++；<br>"
+ "&nbsp;&nbsp;找不到编译器时该选项自动跳过；<br>"
+ "· 产出与运行平台绑定（jar 仅能在 windows/amd64 运行），体积与构建时间增加。"
+ "</div></html>");
        GridBagConstraints j2cGbc = new GridBagConstraints();
        j2cGbc.gridx = 0;
        j2cGbc.gridy = 5;
        j2cGbc.gridwidth = 2;
        j2cGbc.anchor = GridBagConstraints.WEST;
        j2cGbc.insets = new Insets(4, 4, 4, 20);
        protectGrid.add(chkJ2c, j2cGbc);
        // j2c native 资源名自定义行（留空随机；{} 占位替换为 1/2）
        JPanel j2cNameRow = new JPanel(new FlowLayout(FlowLayout.LEFT, 8, 0));
        j2cNameRow.setOpaque(false);
        JLabel j2cNameLbl = new JLabel("native 文件名：");
        j2cNameField.setPreferredSize(new Dimension(260, 28));
        j2cNameField.setToolTipText(
"<html><div style='width:380px'>"
+ "两个加密 native payload 在产出 jar 内的资源条目名模板：<br>"
+ "· 留空 = 每构建随机伪装名（如 core/seq/b3f9a2c10f4e.bin）；<br>"
+ "· 用 {} 作序号占位：native/engine{}.dat → native/engine1.dat、"
+ "native/engine2.dat；<br>"
+ "· 不写占位符时序号自动插入扩展名前：x.bin → x1.bin / x2.bin；<br>"
+ "· 仅支持相对路径与 ASCII 字符；非法或与现有条目重名时回退随机名。"
+ "</div></html>");
        j2cNameLbl.setToolTipText(j2cNameField.getToolTipText());
        j2cNameRow.add(Box.createHorizontalStrut(20));
        j2cNameRow.add(j2cNameLbl);
        j2cNameRow.add(j2cNameField);
        GridBagConstraints j2cNameGbc = new GridBagConstraints();
        j2cNameGbc.gridx = 0;
        j2cNameGbc.gridy = 6;
        j2cNameGbc.gridwidth = 2;
        j2cNameGbc.anchor = GridBagConstraints.WEST;
        j2cNameGbc.insets = new Insets(0, 4, 4, 20);
        protectGrid.add(j2cNameRow, j2cNameGbc);
        chkVmp.setToolTipText(
"<html><div style='width:420px'>"
+ "在 j2c 编译出的三个 PE（loader + 双 payload）上启用内置 VMProtect Ultimate：<br>"
+ "· 每个下沉函数随机使用<b>虚拟化+变异 / 虚拟化 / 变异</b>标记，映射器核心用 Ultra；<br>"
+ "· 开启打包压缩、用户态反调试、内存保护；<b>不</b>开反虚拟机（避免误伤"
+ "云主机/CI/沙箱）与内核调试器检测；<br>"
+ "· 加壳后的高熵 PE 再经原有 XOR 密钥流加密入 jar；<br>"
+ "· 仅 <b>Windows x64</b> 构建，构建时间与产物体积明显增加；单个 PE 加壳"
+ "失败时自动回退为未加壳版本。"
+ "</div></html>");
        GridBagConstraints vmpGbc = new GridBagConstraints();
        vmpGbc.gridx = 0;
        vmpGbc.gridy = 7;
        vmpGbc.gridwidth = 2;
        vmpGbc.anchor = GridBagConstraints.WEST;
        vmpGbc.insets = new Insets(0, 4, 4, 20);
        protectGrid.add(chkVmp, vmpGbc);
        chkVmp.setEnabled(false);
        addCheck(protectGrid, 0, 8, chkStrip);
        addCheck(protectGrid, 1, 8, chkDisperse);
        chkDisperse.setToolTipText(
"<html><div style='width:400px'>"
+ "消除「核心业务语句连续挤在一个方法里」的形态：<br>"
+ "· 构造器/方法中只操作字段的直线语句随机外提到多个随机命名的<br>"
+ "&nbsp;&nbsp;private 合成方法，原位置只剩一串随机名调用，逻辑被拆散到各处；<br>"
+ "· 非递归实例方法（含构造器）的局部变量随机提升为实例字段，<br>"
+ "&nbsp;&nbsp;反编译时方法内干净的局部变量表消失，字段数量增加；<br>"
+ "· 外提方法同样会被后续谓词/屎山/平坦化处理，真假同构；<br>"
+ "· 每构建外提/提升的选择与比例随机，避免固定模式被通解；<br>"
+ "· 语义不变，静态方法与递归方法自动跳过（保证线程/重入安全）。"
+ "</div></html>");
        protectCard.setContent(protectGrid);
        list.add(protectCard);
        list.add(Box.createVerticalStrut(12));

        // —— 输出与标记 ——
        Card outputCard = new Card("输出与标记");
        JPanel outputRow = new JPanel(new FlowLayout(FlowLayout.LEFT, 12, 0));
        outputRow.setOpaque(false);
        outputRow.add(chkKeepSerializable);
        outputRow.add(chkExportMapping);
        outputRow.add(chkWatermark);
        outputRow.add(new JLabel("文本："));
        watermarkField.setPreferredSize(new Dimension(200, 28));
        watermarkField.setToolTipText("嵌入每个 class 的标记文本，用 16 进制编辑器打开即可看到");
        outputRow.add(watermarkField);
        outputCard.setContent(outputRow);
        list.add(outputCard);

        return list;
    }

    private void addCheck(JPanel p, int x, int y, JCheckBox cb) {
        GridBagConstraints c = new GridBagConstraints();
        c.gridx = x;
        c.gridy = y;
        c.anchor = GridBagConstraints.WEST;
        c.weightx = 1;
        c.insets = new Insets(4, 4, 4, 20);
        p.add(cb, c);
    }

    /** 底部控制台卡片：进度 + 主操作按钮 + 日志终端 */
    private JComponent buildConsoleCard() {
        Card card = new Card("运行日志");
        JPanel body = new JPanel(new BorderLayout(0, 8));
        body.setOpaque(false);

        JPanel row = new JPanel(new BorderLayout(10, 0));
        row.setOpaque(false);
        progressBar.setStringPainted(true);
        progressBar.setPreferredSize(new Dimension(progressBar.getPreferredSize().width, 26));
        row.add(progressBar, BorderLayout.CENTER);
        startButton.setPreferredSize(new Dimension(128, 32));
        startButton.setFocusPainted(false);
        row.add(startButton, BorderLayout.EAST);
        body.add(row, BorderLayout.NORTH);

        logArea.setEditable(false);
        logArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 13));
        logArea.setBorder(new CompoundBorder(
                BorderFactory.createLineBorder(UIManager.getColor("App.consoleBorder"), 1, true),
                BorderFactory.createEmptyBorder(8, 10, 8, 10)));
        JScrollPane logScroll = new JScrollPane(logArea);
        logScroll.setBorder(BorderFactory.createEmptyBorder());
        logScroll.getViewport().setOpaque(false);
        logScroll.getVerticalScrollBar().setUnitIncrement(16);
        logScroll.setPreferredSize(new Dimension(600, 150));
        body.add(logScroll, BorderLayout.CENTER);

        card.setContent(body);
        return card;
    }

    private JScrollPane wrapScroll(JComponent content) {
        JScrollPane scroll = new JScrollPane(content,
                JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
        scroll.setBorder(BorderFactory.createEmptyBorder());
        scroll.getViewport().setOpaque(false);
        scroll.getVerticalScrollBar().setUnitIncrement(16);
        return scroll;
    }

    // ------------------------------------------------------------------
    // 事件
    // ------------------------------------------------------------------

    private void wireEvents() {
        themeButton.addActionListener(e -> toggleTheme());

        presetBox.addActionListener(e -> {
            if (syncingPreset) {
                return;
            }
            int idx = presetBox.getSelectedIndex();
            ObfConfig.Preset preset;
            switch (idx) {
                case 1:
                    preset = ObfConfig.Preset.OFF;
                    break;
                case 2:
                    preset = ObfConfig.Preset.LIGHT;
                    break;
                case 3:
                    preset = ObfConfig.Preset.MEDIUM;
                    break;
                case 4:
                    preset = ObfConfig.Preset.AGGRESSIVE;
                    break;
                default:
                    return;
            }
            applyPreset(preset, idx);
        });

        java.awt.event.ItemListener customMark = e -> markCustom();
        for (JCheckBox cb : allChecks()) {
            cb.addItemListener(customMark);
        }
        flowPasses.addChangeListener(e -> markCustom());
        junkCount.addChangeListener(e -> markCustom());
        deadClassCount.addChangeListener(e -> markCustom());
        shitCount.addChangeListener(e -> markCustom());

        // 水印开关与文本框联动
        chkWatermark.addItemListener(e ->
                watermarkField.setEnabled(chkWatermark.isSelected()));
        watermarkField.setEnabled(chkWatermark.isSelected());

        // j2c 开关与 native 文件名输入框、VMP 勾选联动
        chkJ2c.addItemListener(e -> {
            j2cNameField.setEnabled(chkJ2c.isSelected());
            chkVmp.setEnabled(chkJ2c.isSelected());
            if (!chkJ2c.isSelected()) {
                chkVmp.setSelected(false);
            }
        });
        j2cNameField.setEnabled(chkJ2c.isSelected());
        chkVmp.setEnabled(chkJ2c.isSelected());

        // 类拆分与重定向互锁：必须先开启伪代码类注入；关闭伪代码类时
        // 自动取消勾选并禁用，避免产生无效配置
        chkSplitRedirect.setToolTipText(
                "必须先开启“伪代码类注入”。开启后真实类的静态方法会被拆散迁移到随机伪代码类中藏匿，部分伪代码类保持纯诱饵");
        chkDeadClasses.addItemListener(e -> updateSplitGate());
        updateSplitGate();

        startButton.addActionListener(e -> startObfuscation());

        // 在输入框直接粘贴路径后按回车也能加载 JAR 结构
        inputField.addActionListener(e -> {
            String path = inputField.getText().trim();
            if (!path.isEmpty() && new File(path).isFile()) {
                File f = new File(path);
                if (outputField.getText().trim().isEmpty()) {
                    String n = f.getName();
                    int dot = n.lastIndexOf('.');
                    String base = dot > 0 ? n.substring(0, dot) : n;
                    outputField.setText(new File(f.getParentFile(), base + "-obf.jar").getAbsolutePath());
                }
                loadJarTree(f);
            }
        });
    }

    private JCheckBox[] allChecks() {
        return new JCheckBox[]{chkRenameClasses, chkRenamePackages, chkRenameMethods,
                chkRenameFields, chkBraindeadRename, chkStrings, chkNumbers, chkControlFlow,
                chkFlatten, chkDisperse, chkJunk, chkShitBloat, chkJ2c, chkDeadClasses,
                chkSplitRedirect,
                chkStrip, chkKeepSerializable, chkWatermark};
    }

    /** 按伪代码类开关状态刷新类拆分选项的可用性。 */
    private void updateSplitGate() {
        boolean dead = chkDeadClasses.isSelected();
        if (!dead && chkSplitRedirect.isSelected()) {
            chkSplitRedirect.setSelected(false);
        }
        chkSplitRedirect.setEnabled(dead);
    }

    private void applyPreset(ObfConfig.Preset preset, int comboIndex) {
        syncingPreset = true;
        ObfConfig tmp = new ObfConfig();
        tmp.applyPreset(preset);
        chkRenameClasses.setSelected(tmp.renameClasses);
        chkRenamePackages.setSelected(tmp.renamePackages);
        chkRenameMethods.setSelected(tmp.renameMethods);
        chkRenameFields.setSelected(tmp.renameFields);
        chkStrings.setSelected(tmp.encryptStrings);
        chkNumbers.setSelected(tmp.obfuscateNumbers);
        chkControlFlow.setSelected(tmp.controlFlow);
        chkFlatten.setSelected(tmp.flattenControlFlow);
        chkDisperse.setSelected(tmp.disperseLogic);
        chkJunk.setSelected(tmp.junkCode);
        chkShitBloat.setSelected(tmp.shitBloat);
        chkJ2c.setSelected(tmp.j2c);
        chkVmp.setSelected(tmp.vmpPack && tmp.j2c);
        j2cNameField.setText(tmp.j2cNativeName == null ? "" : tmp.j2cNativeName);
        j2cNameField.setEnabled(tmp.j2c);
        chkVmp.setEnabled(tmp.j2c);
        chkDeadClasses.setSelected(tmp.deadCodeClasses);
        chkStrip.setSelected(tmp.stripDebug);
        chkKeepSerializable.setSelected(tmp.keepSerializableFields);
        flowPasses.setValue(Integer.valueOf(Math.max(1, tmp.controlFlowPasses)));
        junkCount.setValue(Integer.valueOf(Math.max(0, tmp.junkMethodsPerClass)));
        shitCount.setValue(Integer.valueOf(Math.max(0,
                Math.min(ShitBloat.MAX_SHIT_METHODS, tmp.shitMethodsPerClass))));
        deadClassCount.setValue(Integer.valueOf(Math.max(0,
                Math.min(MAX_DEAD_CLASSES, tmp.deadClassCount))));
        if (comboIndex >= 0) {
            presetBox.setSelectedIndex(comboIndex);
        }
        syncingPreset = false;
    }

    private void markCustom() {
        if (!syncingPreset) {
            presetBox.setSelectedIndex(0);
        }
    }

    // ------------------------------------------------------------------
    // 主题
    // ------------------------------------------------------------------

    private void toggleTheme() {
        darkMode = !darkMode;
        try {
            FlatLaf.setup(darkMode ? new FlatDarkLaf() : new FlatLightLaf());
            FlatLaf.updateUI();
        } catch (Exception ignored) {
        }
        applyDynamicColors();
        SwingUtilities.updateComponentTreeUI(this);
        themeButton.setText(darkMode ? "浅色模式" : "深色模式");
    }

    /** 自绘组件与标签颜色全部在此动态读取 UIManager，浅/深主题即时生效。 */
    private void applyDynamicColors() {
        Color head = UIManager.getColor("App.headerText");
        Color sub = UIManager.getColor("App.subText");
        Color bg = UIManager.getColor("App.consoleBg");
        Color fg = UIManager.getColor("App.consoleFg");
        Color sel = UIManager.getColor("App.consoleSelection");
        if (head != null) {
            headerTitle.setForeground(head);
            for (JLabel t : cardTitles) {
                t.setForeground(head);
            }
        }
        if (sub != null) {
            headerSubtitle.setForeground(sub);
            dropHint.setForeground(sub);
            regexHint.setForeground(sub);
        }
        if (bg != null && fg != null) {
            logArea.setBackground(bg);
            logArea.setForeground(fg);
            logArea.setCaretColor(fg);
            logArea.setSelectionColor(sel != null ? sel : new Color(0x2D4F7A));
            logArea.setSelectedTextColor(Color.WHITE);
            logArea.setBorder(new CompoundBorder(
                    BorderFactory.createLineBorder(
                            UIManager.getColor("App.consoleBorder"), 1, true),
                    BorderFactory.createEmptyBorder(8, 10, 8, 10)));
        }
        repaint();
    }

    // ------------------------------------------------------------------
    // 文件选择与 JAR 树加载
    // ------------------------------------------------------------------

    private void chooseInput() {
        JFileChooser fc = new JFileChooser();
        fc.setFileFilter(new FileNameExtensionFilter("JAR 文件 (*.jar)", "jar"));
        if (!inputField.getText().trim().isEmpty()) {
            fc.setSelectedFile(new File(inputField.getText().trim()));
        }
        if (fc.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        acceptInputJar(fc.getSelectedFile());
    }

    /** 设置输入 JAR：写入路径、自动补默认输出路径并加载类树（浏览与拖放共用）。 */
    private void acceptInputJar(File f) {
        if (f == null) {
            return;
        }
        inputField.setText(f.getAbsolutePath());
        if (outputField.getText().trim().isEmpty()) {
            String n = f.getName();
            int dot = n.lastIndexOf('.');
            String base = dot > 0 ? n.substring(0, dot) : n;
            outputField.setText(new File(f.getParentFile(), base + "-obf.jar").getAbsolutePath());
        }
        loadJarTree(f);
    }

    // ------------------------------------------------------------------
    // 拖放支持：把 JAR 拖到窗口任意位置即可设置输入
    // ------------------------------------------------------------------

    private void installJarDropSupport() {
        javax.swing.TransferHandler jarDrop = new javax.swing.TransferHandler() {
            @Override
            public boolean canImport(JComponent comp,
                                    java.awt.datatransfer.DataFlavor[] flavors) {
                for (java.awt.datatransfer.DataFlavor f : flavors) {
                    if (java.awt.datatransfer.DataFlavor.javaFileListFlavor.equals(f)) {
                        return true;
                    }
                }
                return false;
            }

            @Override
            @SuppressWarnings("unchecked")
            public boolean importData(JComponent comp,
                                     java.awt.datatransfer.Transferable t) {
                if (!t.isDataFlavorSupported(
                        java.awt.datatransfer.DataFlavor.javaFileListFlavor)) {
                    return false;
                }
                try {
                    Object data = t.getTransferData(
                            java.awt.datatransfer.DataFlavor.javaFileListFlavor);
                    List<File> files = (List<File>) data;
                    File jar = null;
                    for (File f : files) {
                        if (f.isFile()
                                && f.getName().toLowerCase(java.util.Locale.ROOT)
                                        .endsWith(".jar")) {
                            jar = f;
                            break;
                        }
                    }
                    if (jar == null) {
                        return false;
                    }
                    final File chosen = jar;
                    SwingUtilities.invokeLater(() -> {
                        acceptInputJar(chosen);
                        log("已通过拖放设置输入 JAR：" + chosen.getName());
                    });
                    return true;
                } catch (Exception e) {
                    return false;
                }
            }
        };
        attachTransferHandler(getContentPane(), jarDrop);
    }

    private void attachTransferHandler(Component c, javax.swing.TransferHandler th) {
        if (c instanceof JComponent) {
            ((JComponent) c).setTransferHandler(th);
        }
        if (c instanceof java.awt.Container) {
            for (Component child : ((java.awt.Container) c).getComponents()) {
                attachTransferHandler(child, th);
            }
        }
    }

    private void chooseOutput() {
        JFileChooser fc = new JFileChooser();
        fc.setDialogTitle("选择输出位置");
        if (fc.showSaveDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        outputField.setText(fc.getSelectedFile().getAbsolutePath());
    }

    private void loadJarTree(final File jar) {
        log("正在读取 JAR 条目：" + jar.getName());
        SwingWorker<List<CheckBoxTree.PathEntry>, Void> worker =
                new SwingWorker<List<CheckBoxTree.PathEntry>, Void>() {
                    @Override
                    protected List<CheckBoxTree.PathEntry> doInBackground() throws Exception {
                        List<Obfuscator.EntryInfo> infos = Obfuscator.listEntries(jar.getAbsolutePath());
                        List<CheckBoxTree.PathEntry> list =
                                new ArrayList<CheckBoxTree.PathEntry>();
                        for (Obfuscator.EntryInfo info : infos) {
                            list.add(new CheckBoxTree.PathEntry(info.path, info.isClass));
                        }
                        return list;
                    }

                    @Override
                    protected void done() {
                        try {
                            tree.rebuild(get());
                            log("JAR 条目加载完成，共 " + tree.root().getDepth() + " 层目录。");
                        } catch (Exception ex) {
                            JOptionPane.showMessageDialog(MainFrame.this,
                                    "读取 JAR 失败：" + ex.getMessage(),
                                    "错误", JOptionPane.ERROR_MESSAGE);
                            log("读取 JAR 失败：" + ex);
                        }
                    }
                };
        worker.execute();
    }

    // ------------------------------------------------------------------
    // 执行混淆
    // ------------------------------------------------------------------

    private void startObfuscation() {
        String in = inputField.getText().trim();
        String out = outputField.getText().trim();
        if (in.isEmpty() || out.isEmpty()) {
            JOptionPane.showMessageDialog(this, "请先选择输入与输出 JAR 路径。",
                    "提示", JOptionPane.WARNING_MESSAGE);
            return;
        }
        if (new File(in).equals(new File(out))) {
            JOptionPane.showMessageDialog(this, "输出路径不能与输入相同。",
                    "提示", JOptionPane.WARNING_MESSAGE);
            return;
        }

        final ObfConfig cfg = new ObfConfig();
        cfg.inputJar = in;
        cfg.outputJar = out;
        cfg.renameClasses = chkRenameClasses.isSelected();
        cfg.renamePackages = chkRenamePackages.isSelected();
        cfg.renameMethods = chkRenameMethods.isSelected();
        cfg.renameFields = chkRenameFields.isSelected();
        cfg.renameStyle = chkBraindeadRename.isSelected()
                ? ObfConfig.RenameStyle.BRAINDEAD : ObfConfig.RenameStyle.NORMAL;
        cfg.encryptStrings = chkStrings.isSelected();
        cfg.obfuscateNumbers = chkNumbers.isSelected();
        cfg.controlFlow = chkControlFlow.isSelected();
        cfg.flattenControlFlow = chkFlatten.isSelected();
        cfg.disperseLogic = chkDisperse.isSelected();
        cfg.junkCode = chkJunk.isSelected();
        cfg.shitBloat = chkShitBloat.isSelected();
        cfg.j2c = chkJ2c.isSelected();
        cfg.vmpPack = chkVmp.isSelected() && chkJ2c.isSelected();
        cfg.j2cNativeName = j2cNameField.getText();
        cfg.deadCodeClasses = chkDeadClasses.isSelected();
        // 硬保险：UI 已互锁，这里再兜底一次（无伪代码类时拆分无意义）
        cfg.splitRedirect = cfg.deadCodeClasses && chkSplitRedirect.isSelected();
        cfg.stripDebug = chkStrip.isSelected();
        cfg.keepSerializableFields = chkKeepSerializable.isSelected();
        cfg.exportMapping = chkExportMapping.isSelected();
        cfg.watermarkEnabled = chkWatermark.isSelected();
        cfg.watermarkText = watermarkField.getText();
        cfg.controlFlowPasses = (Integer) flowPasses.getValue();
        cfg.junkMethodsPerClass = (Integer) junkCount.getValue();
        cfg.shitMethodsPerClass = (Integer) shitCount.getValue();
        cfg.deadClassCount = (Integer) deadClassCount.getValue();
        cfg.exclusionRegexText = regexArea.getText();

        CheckBoxTree.Exclusion ex = tree.collectExclusions();
        cfg.excludedClasses = new ArrayList<String>(ex.classes);
        cfg.excludedPackages = new ArrayList<String>(ex.packages);

        startButton.setEnabled(false);
        progressBar.setValue(0);
        progressBar.setIndeterminate(true);
        log("———— 开始混淆 ————");

        SwingWorker<Void, String> worker = new SwingWorker<Void, String>() {
            private volatile boolean userCancelled = false;

            @Override
            protected Void doInBackground() {
                Obfuscator.Listener listener = new Obfuscator.Listener() {
                    public void log(String message) {
                        publish(message);
                    }

                    public void progress(int done, int total) {
                        SwingUtilities.invokeLater(new Runnable() {
                            public void run() {
                                progressBar.setIndeterminate(false);
                                progressBar.setMaximum(Math.max(1, total));
                                progressBar.setValue(done);
                            }
                        });
                    }

                    public boolean cancelled() {
                        return userCancelled;
                    }
                };
                try {
                    new Obfuscator(cfg, listener).run();
                } catch (final Throwable t) {
                    publish("混淆失败：" + t);
                    java.io.StringWriter sw = new java.io.StringWriter();
                    t.printStackTrace(new java.io.PrintWriter(sw));
                    publish(sw.toString());
                }
                return null;
            }

            @Override
            protected void process(List<String> chunks) {
                for (String s : chunks) {
                    log(s);
                }
            }

            @Override
            protected void done() {
                startButton.setEnabled(true);
                progressBar.setIndeterminate(false);
                logArea.append("———— 结束 ————\n");
            }
        };
        worker.execute();
    }

    private void log(String msg) {
        logArea.append(msg + "\n");
        logArea.setCaretPosition(logArea.getDocument().getLength());
    }

    // ------------------------------------------------------------------
    // 现代卡片容器：圆角白底（深色主题为深灰），标题加粗
    // ------------------------------------------------------------------

    private final class Card extends JPanel {
        private Card(String title) {
            super(new BorderLayout(0, 10));
            setOpaque(false);
            setBorder(BorderFactory.createEmptyBorder(14, 16, 14, 16));
            JLabel t = new JLabel(title);
            t.setFont(t.getFont().deriveFont(Font.BOLD, 14f));
            cardTitles.add(t);
            add(t, BorderLayout.NORTH);
        }

        private void setContent(JComponent c) {
            add(c, BorderLayout.CENTER);
        }

        @Override
        public Dimension getMaximumSize() {
            // 纵向 Box 布局中宽度可拉伸、高度保持首选，不被拉成奇怪比例
            return new Dimension(super.getMaximumSize().width, getPreferredSize().height);
        }

        @Override
        protected void paintComponent(Graphics g) {
            Graphics2D g2 = (Graphics2D) g.create();
            g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            int arc = 12;
            Color bg = UIManager.getColor("App.card");
            Color line = UIManager.getColor("App.cardBorder");
            if (bg != null) {
                g2.setColor(bg);
                g2.fillRoundRect(0, 0, getWidth(), getHeight(), arc, arc);
            }
            if (line != null) {
                g2.setColor(line);
                g2.drawRoundRect(0, 0, getWidth() - 1, getHeight() - 1, arc, arc);
            }
            g2.dispose();
            super.paintComponent(g);
        }
    }

    // ------------------------------------------------------------------
    // 启动
    // ------------------------------------------------------------------

    public static void launch() {
        // 自定义主题属性：classpath 下 com/jdobf/gui/FlatLaf*.properties
        FlatLaf.registerCustomDefaultsSource("com.jdobf.gui");
        SwingUtilities.invokeLater(new Runnable() {
            public void run() {
                try {
                    // 统一基础字体：优先 Segoe UI（物理字体在部分 JDK 下不做中文
                    // 回退会变方框），不能显示中文时退回 Microsoft YaHei UI
                    String family = "Microsoft YaHei UI";
                    Font segui = new Font("Segoe UI", Font.PLAIN, 13);
                    if (segui.canDisplayUpTo("豆包字节码混淆器") == -1) {
                        family = "Segoe UI";
                    } else {
                        Font yahei = new Font("Microsoft YaHei UI", Font.PLAIN, 13);
                        if (yahei.canDisplayUpTo("豆包字节码混淆器") != -1
                                && new Font("Microsoft YaHei", Font.PLAIN, 13)
                                        .canDisplayUpTo("豆包字节码混淆器") == -1) {
                            family = "Microsoft YaHei";
                        }
                    }
                    UIManager.put("defaultFont", new Font(family, Font.PLAIN, 13));
                    FlatLightLaf.setup();
                } catch (Throwable t) {
                    try {
                        UIManager.setLookAndFeel(
                                UIManager.getSystemLookAndFeelClassName());
                    } catch (Exception ignored) {
                    }
                }
                new MainFrame().setVisible(true);
            }
        });
    }
}
