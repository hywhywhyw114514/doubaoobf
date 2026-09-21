package com.jdobf.j2c;

import com.jdobf.core.Obfuscator;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * DoubaoProtect 加壳封装（内置 DoubaoProtect 命令行加壳器、运行时与 SDK）。
 *
 * <h3>资源布局</h3>（打包在 fatJar 内，构建时释放到 j2c 临时构建目录）
 * <ul>
 *   <li>{@code DoubaoProtect.exe}：命令行加壳器；</li>
 *   <li>{@code DoubaoRT32.dll / DoubaoRT64.dll}：目标 PE 内嵌运行时；</li>
 *   <li>{@code DoubaoProtect.h} / {@code DoubaoSDK.lib}：编译期标记 SDK
 *       （MSVC 使用静态库；MinGW 由本类生成 {@code dbpmarks.cpp} 提供
 *       相同布局的标记函数）。</li>
 * </ul>
 *
 * <h3>流程</h3>
 * 编译带 {@code J2C_DBP} 标记的 PE → 调用 {@code DoubaoProtect.exe} 对
 * SDK 标记区域做 Ultra/变异保护，并把对应架构的 DoubaoRT 运行
 * 时嵌入产物 → 校验产物 MZ/体积。加壳后标记调用点被替换为运行时门控，
 * 原 PE 依赖的 DOUBAO 文件无需随 jar 分发。
 *
 * <p>与 VMP 路径一致：加壳发生在 payload 整体 XOR 加密之前，且单个 PE
 * 加壳失败时回退未加壳版本，不拖垮整个 j2c 构建。</p>
 */
public final class DbpPacker {

    private static final String RES_DIR = "/com/jdobf/j2c/dbp/";

    /** 构建期 SDK 文件（释放到编译目录）。 */
    private static final String[] SDK_FILES = {
            "DoubaoProtect.h", "DoubaoSDK.lib",
    };
    /** 加壳器与运行时文件：exe 需与 DoubaoRT*.dll 同目录。 */
    private static final String[] TOOL_FILES = {
            "DoubaoProtect.exe", "DoubaoRT32.dll", "DoubaoRT64.dll",
    };

    private DbpPacker() {
    }

    /** 仅 Windows x64 且内置加壳器/SDK/64 位运行时齐全时可用。 */
    public static boolean available() {
        if (!System.getProperty("os.name", "").toLowerCase().contains("win")) {
            return false;
        }
        String arch = System.getProperty("os.arch", "").toLowerCase();
        if (!arch.contains("amd64") && !arch.contains("x86_64")) {
            return false;
        }
        return resourceExists("DoubaoProtect.exe")
                && resourceExists("DoubaoRT32.dll")
                && resourceExists("DoubaoRT64.dll")
                && resourceExists("DoubaoProtect.h")
                && resourceExists("DoubaoSDK.lib");
    }

    /**
     * 把加壳器、运行时与 SDK 全部释放到 j2c 构建目录
     * （目录用完随 j2c 一起删除）。
     */
    public static void prepare(File buildDir) throws IOException {
        for (String name : TOOL_FILES) {
            extract(name, new File(buildDir, name));
        }
        for (String name : SDK_FILES) {
            extract(name, new File(buildDir, name));
        }
        // MinGW 无法直接链接 MSVC 的 DoubaoSDK.lib；这里生成一份等价的
        // 全局汇编标记函数，由 NativeToolchain 在 g++ 构建时加入。
        writeFile(new File(buildDir, "dbpmarks.cpp"),
                markerAsmSource().getBytes(StandardCharsets.UTF_8));
    }

    /**
     * 对构建目录中的一个 PE 执行 DoubaoProtect 加壳。
     *
     * @param tag 日志标识（如 "loader"/"payload1"）
     * @return 加壳器输出
     */
    public static String pack(File buildDir, String tag, File input, File output,
                              Obfuscator.Listener listener)
            throws IOException, InterruptedException {
        List<String> cmd = new ArrayList<String>();
        cmd.add(new File(buildDir, "DoubaoProtect.exe").getAbsolutePath());
        cmd.add(input.getName());
        cmd.add("-o");
        cmd.add(output.getName());
        cmd.add("--rt32");
        cmd.add(new File(buildDir, "DoubaoRT32.dll").getAbsolutePath());
        cmd.add("--rt64");
        cmd.add(new File(buildDir, "DoubaoRT64.dll").getAbsolutePath());
        // 与 VMP 路径一致：默认不启用反虚拟机，避免误伤云主机/CI/沙箱。
        // 需要完整默认防护时可设置 J2C_DBP_FULL=1。
        if (!"1".equals(System.getenv("J2C_DBP_FULL"))) {
            cmd.add("--no-antivm");
        }
        String extra = System.getenv("J2C_DBP_ARGS");
        if (extra != null && !extra.trim().isEmpty()) {
            for (String a : extra.trim().split("\\s+")) {
                cmd.add(a);
            }
        }

        ProcessBuilder pb = new ProcessBuilder(cmd);
        pb.directory(buildDir);
        pb.redirectErrorStream(true);
        long t0 = System.currentTimeMillis();
        Process p = pb.start();
        String console = readAll(p.getInputStream());
        if (!p.waitFor(900, TimeUnit.SECONDS)) {
            p.destroyForcibly();
            throw new IOException("DoubaoProtect 加壳超时（900s）：" + tag);
        }
        long secs = (System.currentTimeMillis() - t0) / 1000;
        if (p.exitValue() != 0 || !output.isFile() || output.length() < 1024) {
            throw new IOException("DoubaoProtect 加壳失败（" + tag + "），退出码 "
                    + p.exitValue() + "\n" + tail(console));
        }
        listener.log("  DBP 加壳 " + tag + "：" + input.length() / 1024
                + "KB -> " + output.length() / 1024 + "KB，耗时 " + secs + "s");
        return console;
    }

    /** MinGW/GCC 使用的标记函数汇编实现（x64 COFF，与 DoubaoSDK.lib 布局一致）。 */
    private static String markerAsmSource() {
        String h = "#ifdef __GNUC__\n"
                + "__asm__(\n"
                + "\".text\\n\"\n"
                + "\".globl DbpMarkV\\n\"\n"
                + "\".globl DbpMarkM\\n\"\n"
                + "\".globl DbpMarkU\\n\"\n"
                + "\".globl DbpMarkEnd\\n\"\n"
                + "\"DbpMarkV:\\n\"\n"
                + "\"ret\\n\"\n"
                + "\".byte 0xDB,0xDB,0x50,0x21,0xB7,0x7E,0xA1,0x4C,0x01\\n\"\n"
                + "\"DbpMarkM:\\n\"\n"
                + "\"ret\\n\"\n"
                + "\".byte 0xDB,0xDB,0x50,0x21,0xB7,0x7E,0xA1,0x4C,0x02\\n\"\n"
                + "\"DbpMarkU:\\n\"\n"
                + "\"ret\\n\"\n"
                + "\".byte 0xDB,0xDB,0x50,0x21,0xB7,0x7E,0xA1,0x4C,0x03\\n\"\n"
                + "\"DbpMarkEnd:\\n\"\n"
                + "\"ret\\n\"\n"
                + "\".byte 0xDB,0xDB,0x50,0x21,0xB7,0x7E,0xA1,0x4C,0x04\\n\"\n"
                + ");\n"
                + "#endif\n";
        return h;
    }

    private static boolean resourceExists(String resource) {
        return DbpPacker.class.getResource(RES_DIR + resource) != null;
    }

    private static void extract(String resource, File target) throws IOException {
        InputStream in = DbpPacker.class.getResourceAsStream(RES_DIR + resource);
        if (in == null) {
            throw new IOException("内置 DoubaoProtect 资源缺失：" + resource);
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
        // DoubaoProtect 在中文 Windows 控制台可能输出 GBK
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
