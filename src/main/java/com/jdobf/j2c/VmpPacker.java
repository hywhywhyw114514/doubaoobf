package com.jdobf.j2c;

import com.jdobf.core.Obfuscator;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.TimeUnit;

/**
 * VMProtect 加壳封装（内置 VMProtect Ultimate 的 Console 版与 SDK）。
 *
 * <h3>资源布局</h3>（打包在 fatJar 内，构建时释放到 j2c 临时构建目录）
 * <ul>
 *   <li>{@code VMProtect_Con.exe} / {@code VMProtect_Ext32/64.dll}：加壳器本体；</li>
 *   <li>{@code VMProtectSDK.h} / {@code VMProtectSDK64.lib} /
 *       {@code VMProtectSDK64.a}：编译期标记 SDK（MSVC / MinGW）。</li>
 * </ul>
 *
 * <h3>流程</h3>
 * 编译带 {@code J2C_VMP} 标记的 PE → 生成 .vmp 工程（打包 + 用户态反调试
 * + 内存保护 + 剥离调试信息；<b>不</b>启用反虚拟机与内核调试器检测，避免
 * 误伤云主机/CI/沙箱与普通开发机；保留重定位以兼容手动映射与 ASLR）→
 * 调用 VMProtect_Con → 校验产物 MZ/体积。加壳后 SDK 标记调用被替换为
 * VM 代码，对 VMProtectSDK64.dll 的导入被剥离，运行机无需任何 VMP 文件。
 */
public final class VmpPacker {

    /** 工程选项位掩码：1=打包 2=调试器检测 4=内存保护 32=剥离调试信息。 */
    private static final int PROJECT_OPTIONS = 1 | 2 | 4 | 32;

    private static final String RES_DIR = "/com/jdobf/j2c/vmp/";

    /** 构建期 SDK 文件名（释放到编译目录）。 */
    private static final String[] SDK_FILES = {
            "VMProtectSDK.h", "VMProtectSDK64.lib", "VMProtectSDK64.a",
    };
    /** 加壳器文件名（释放到编译目录，con 需与 Ext dll 同目录）。 */
    private static final String[] TOOL_FILES = {
            "VMProtect_Con.exe", "VMProtect_Ext32.dll", "VMProtect_Ext64.dll",
    };

    private VmpPacker() {
    }

    /** 仅 Windows x64 且内置资源齐全时可用。 */
    public static boolean available() {
        if (!System.getProperty("os.name", "").toLowerCase().contains("win")) {
            return false;
        }
        String arch = System.getProperty("os.arch", "").toLowerCase();
        if (!arch.contains("amd64") && !arch.contains("x86_64")) {
            return false;
        }
        return VmpPacker.class.getResource(RES_DIR + "VMProtect_Con.exe") != null
                && VmpPacker.class.getResource(RES_DIR + "VMProtect_Ext64.dll") != null
                && VmpPacker.class.getResource(RES_DIR + "VMProtectSDK.h") != null;
    }

    /** 把加壳器与 SDK 全部释放到 j2c 构建目录（目录用完随 j2c 一起删除）。 */
    public static void prepare(File buildDir) throws IOException {
        for (String name : TOOL_FILES) {
            extract(name, new File(buildDir, name));
        }
        for (String name : SDK_FILES) {
            extract(name, new File(buildDir, name));
        }
    }

    /**
     * 对构建目录中的一个 PE 执行 VMP 加壳。
     *
     * @param tag 日志/工程文件名前缀（如 "loader"/"payload1"）
     * @return 加壳输出（con 输出尾部，含 [U]/[V]/[M] 标记统计）
     */
    public static String pack(File buildDir, String tag, File input, File output,
                              Obfuscator.Listener listener)
            throws IOException, InterruptedException {
        String projectName = "vmp_" + tag + ".vmp";
        int options = PROJECT_OPTIONS;
        String optOverride = System.getenv("J2C_VMP_OPTIONS");
        if (optOverride != null) {
            try {
                options = Integer.parseInt(optOverride.trim());
            } catch (NumberFormatException nfe) {
                listener.log("[警告] J2C_VMP_OPTIONS 非法（" + optOverride
                        + "），使用默认 " + PROJECT_OPTIONS);
            }
        }
        String xml = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\r\n"
                + "<Document>\r\n"
                + " <Protection InputFileName=\"" + input.getName()
                + "\" Options=\"" + options + "\""
                + " CheckKernelDebugger=\"false\" CompressionMode=\"0\""
                + " VMCodeSectionName=\".vmp\" VMExecutorCount=\"1\""
                + " LicenseDataFileName=\"\" OutputFileName=\"" + output.getName()
                + "\" WaterMarkName=\"\" RunParameters=\"\">\r\n"
                + "  <Folders/>\r\n"
                + "  <Procedures/>\r\n"
                + " </Protection>\r\n"
                + " <DLLBox/>\r\n"
                + " <Script IncludedInCompilation=\"true\"></Script>\r\n"
                + "</Document>\r\n";
        File projectFile = new File(buildDir, projectName);
        writeFile(projectFile, xml.getBytes(StandardCharsets.UTF_8));

        ProcessBuilder pb = new ProcessBuilder(
                new File(buildDir, "VMProtect_Con.exe").getAbsolutePath(),
                input.getName(), output.getName(), "-pf", projectName);
        pb.directory(buildDir);
        pb.redirectErrorStream(true);
        long t0 = System.currentTimeMillis();
        Process p = pb.start();
        String console = readAll(p.getInputStream());
        if (!p.waitFor(900, TimeUnit.SECONDS)) {
            p.destroyForcibly();
            throw new IOException("VMProtect 加壳超时（900s）：" + tag);
        }
        long secs = (System.currentTimeMillis() - t0) / 1000;
        if (p.exitValue() != 0 || !output.isFile() || output.length() < 1024) {
            throw new IOException("VMProtect 加壳失败（" + tag + "），退出码 "
                    + p.exitValue() + "\n" + tail(console));
        }
        int u = countOccur(console, "[U]");
        int v = countOccur(console, "[V]");
        int m = countOccur(console, "[M]");
        if (u + v + m == 0) {
            throw new IOException("VMProtect 未在 " + tag + " 中发现任何保护标记，"
                    + "标记链接可能被优化，请检查编译选项。\n" + tail(console));
        }
        listener.log("  VMP 加壳 " + tag + "：Ultra " + u + " / 虚拟化 " + v
                + " / 变异 " + m + " 处，" + input.length() / 1024 + "KB -> "
                + output.length() / 1024 + "KB，耗时 " + secs + "s");
        return console;
    }

    private static int countOccur(String text, String sub) {
        int n = 0, pos = 0;
        while ((pos = text.indexOf(sub, pos)) >= 0) {
            n++;
            pos += sub.length();
        }
        return n;
    }

    private static void extract(String resource, File target) throws IOException {
        InputStream in = VmpPacker.class.getResourceAsStream(RES_DIR + resource);
        if (in == null) {
            throw new IOException("内置 VMProtect 资源缺失：" + resource);
        }
        try {
            FileOutputStream fos = new FileOutputStream(target);
            try {
                byte[] buf = new byte[65536];
                int n;
                while ((n = in.read(buf)) > 0) {
                    fos.write(buf, 0, n);
                }
            } finally {
                fos.close();
            }
        } finally {
            in.close();
        }
    }

    private static void writeFile(File f, byte[] data) throws IOException {
        FileOutputStream fos = new FileOutputStream(f);
        try {
            fos.write(data);
        } finally {
            fos.close();
        }
    }

    private static String readAll(InputStream in) throws IOException {
        ByteArrayOutputStream bos = new ByteArrayOutputStream();
        byte[] buf = new byte[4096];
        int n;
        while ((n = in.read(buf)) > 0) {
            bos.write(buf, 0, n);
        }
        // con 在中文 Windows 输出 GBK，按 GBK 解码避免日志乱码
        try {
            return bos.toString("GBK");
        } catch (Exception e) {
            return new String(bos.toByteArray(), StandardCharsets.UTF_8);
        }
    }

    private static String tail(String s) {
        if (s == null) {
            return "(无加壳器输出)";
        }
        s = s.trim();
        if (s.length() <= 3000) {
            return s;
        }
        return "..." + s.substring(s.length() - 3000);
    }
}
