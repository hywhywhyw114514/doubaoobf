package com.jdobf.j2c;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * j2c 原生工具链：仅支持 Windows x64。
 *
 * 探测顺序：
 * <ol>
 *   <li>环境变量 {@code J2C_CC}（直接指向 g++/clang++ 或 cl.exe）；</li>
 *   <li>PATH 上的 g++ / x86_64-w64-mingw32-g++；</li>
 *   <li>vswhere 找到的 Visual Studio（vcvars64.bat + cl）。</li>
 * </ol>
 * JNI 头文件在 JAVA_HOME、java.home 及常见 JDK 安装目录中查找 jni.h。
 */
public final class NativeToolchain {

    public static final class Toolchain {
        final boolean msvc;
        final File compiler;      // g++ 路径；MSVC 模式下为 vcvars64.bat
        final File jniInclude;
        final File jniPlatform;

        Toolchain(boolean msvc, File compiler, File jniInclude, File jniPlatform) {
            this.msvc = msvc;
            this.compiler = compiler;
            this.jniInclude = jniInclude;
            this.jniPlatform = jniPlatform;
        }

        public String describe() {
            return msvc ? "MSVC (Visual Studio)" : compiler.getName();
        }
    }

    private NativeToolchain() {
    }

    /** 运行前置检查：平台/编译器/JNI 头缺一即抛带操作建议的异常。 */
    public static Toolchain preflight() throws IOException {
        String os = System.getProperty("os.name", "").toLowerCase();
        String arch = System.getProperty("os.arch", "").toLowerCase();
        if (!os.contains("win")) {
            throw new IOException("j2c 目前仅支持 Windows（当前系统: "
                    + System.getProperty("os.name") + "），请关闭 j2c 选项。");
        }
        if (!"amd64".equals(arch) && !"x86_64".equals(arch)) {
            throw new IOException("j2c 仅支持 64 位 JVM（当前 os.arch=" + arch + "）。");
        }
        File[] inc = findJniInclude();
        if (inc == null) {
            throw new IOException("j2c 未找到 jni.h：请安装 JDK（不是 JRE），或设置 JAVA_HOME "
                    + "指向 JDK 目录后重试。");
        }
        Toolchain tc = detectCompiler(inc[0], inc[1]);
        if (tc == null) {
            throw new IOException("j2c 需要 64 位 C++ 编译器，但未找到。请任选其一：\n"
                    + "  1) 安装 Visual Studio 2022 并勾选“使用 C++ 的桌面开发”；\n"
                    + "  2) 安装 MSYS2/MinGW-w64 并把 g++ 加入 PATH；\n"
                    + "  3) 设置环境变量 J2C_CC 指向 g++.exe 或 cl.exe。");
        }
        return tc;
    }

    private static Toolchain detectCompiler(File jniInclude, File jniPlatform) {
        // 1) J2C_CC 显式指定
        String explicit = System.getenv("J2C_CC");
        if (explicit != null && !explicit.trim().isEmpty()) {
            File f = new File(explicit.trim());
            if (f.isFile()) {
                boolean isCl = f.getName().toLowerCase().startsWith("cl");
                return new Toolchain(isCl, f, jniInclude, jniPlatform);
            }
        }
        // 2) PATH 上的 mingw g++
        for (String exe : new String[] { "g++.exe", "x86_64-w64-mingw32-g++.exe",
                "clang++.exe" }) {
            File onPath = which(exe);
            if (onPath != null) {
                return new Toolchain(false, onPath, jniInclude, jniPlatform);
            }
        }
        // 3) Visual Studio（vswhere）
        File vcvars = findVcvars();
        if (vcvars != null) {
            return new Toolchain(true, vcvars, jniInclude, jniPlatform);
        }
        return null;
    }

    private static File which(String exe) {
        String pathEnv = System.getenv("PATH");
        if (pathEnv == null) {
            return null;
        }
        for (String p : pathEnv.split(File.pathSeparator)) {
            File f = new File(p, exe);
            if (f.isFile()) {
                return f;
            }
        }
        return null;
    }

    private static File findVcvars() {
        String pf = System.getenv("ProgramFiles(x86)");
        if (pf == null) {
            pf = System.getenv("ProgramFiles");
        }
        if (pf != null) {
            File vswhere = new File(pf,
                    "Microsoft Visual Studio\\Installer\\vswhere.exe");
            if (vswhere.isFile()) {
                try {
                    Process p = new ProcessBuilder(vswhere.getAbsolutePath(),
                            "-latest", "-products", "*",
                            "-requires",
                            "Microsoft.VisualStudio.Component.VC.Tools.x86.x64",
                            "-property", "installationPath")
                            .redirectErrorStream(true).start();
                    String out = readAll(p.getInputStream());
                    if (p.waitFor() == 0) {
                        for (String line : out.split("\\r?\\n")) {
                            String root = line.trim();
                            if (!root.isEmpty()) {
                                File v = new File(root,
                                        "VC\\Auxiliary\\Build\\vcvars64.bat");
                                if (v.isFile()) {
                                    return v;
                                }
                            }
                        }
                    }
                } catch (Exception ignored) {
                    // 落到固定路径
                }
            }
        }
        for (String root : new String[] { "D:\\VisualStudio", "C:\\Program Files\\Microsoft Visual Studio\\2022\\Community",
                "C:\\Program Files (x86)\\Microsoft Visual Studio\\2019\\BuildTools" }) {
            File v = new File(root, "VC\\Auxiliary\\Build\\vcvars64.bat");
            if (v.isFile()) {
                return v;
            }
        }
        return null;
    }

    /** @return [jni.h 所在 include 目录, win32 平台目录]，找不到返回 null */
    private static File[] findJniInclude() {
        List<File> roots = new ArrayList<File>();
        String javaHome = System.getProperty("java.home");
        if (javaHome != null) {
            roots.add(new File(javaHome));
            roots.add(new File(javaHome).getParentFile());
        }
        String envHome = System.getenv("JAVA_HOME");
        if (envHome != null) {
            roots.add(new File(envHome));
        }
        File pf = new File("C:\\Program Files");
        File[] jdks = pf.listFiles();
        if (jdks != null) {
            roots.addAll(Arrays.asList(jdks));
        }
        File adopt = new File("C:\\Program Files\\Eclipse Adoptium");
        if (adopt.isDirectory()) {
            File[] ads = adopt.listFiles();
            if (ads != null) {
                roots.addAll(Arrays.asList(ads));
            }
        }
        for (File root : roots) {
            if (root == null) {
                continue;
            }
            File inc = new File(root, "include");
            File win = new File(inc, "win32");
            if (new File(inc, "jni.h").isFile()
                    && new File(win, "jni_md.h").isFile()) {
                return new File[] { inc, win };
            }
        }
        return null;
    }

    /**
     * 在 buildDir 中把 cppFile 编译为 dllFile。
     *
     * @return 编译器输出（成功时也返回，供日志记录）
     * @throws IOException 编译失败（消息中包含编译器输出尾部）
     */
    public static String compile(Toolchain tc, File buildDir, File cppFile, File dllFile)
            throws IOException, InterruptedException {
        return compile(tc, buildDir, cppFile, dllFile, false);
    }

    /**
     * @param vmpMarkers 为 true 时定义 J2C_VMP（源码中的 VMP_* 标记宏展开为
     *                   VMProtect SDK 调用）并链接 VMProtectSDK64 导入库，
     *                   同时关闭 ICF/REF 折叠保证每个被标记入口 RVA 唯一。
     *                   构建目录需已放入 VMProtectSDK.h 与对应导入库。
     */
    public static String compile(Toolchain tc, File buildDir, File cppFile, File dllFile,
                                 boolean vmpMarkers)
            throws IOException, InterruptedException {
        ProcessBuilder pb;
        if (tc.msvc) {
            // vcvars64 初始化环境后 cl；/MT 静态 CRT，产物可独立运行
            String cmd = "\"" + tc.compiler.getAbsolutePath() + "\" >nul 2>nul && "
                    + "cl /nologo /utf-8 /O2 /MT /EHsc /LD "
                    + (vmpMarkers ? "/D J2C_VMP " : "")
                    + "/I\"" + tc.jniInclude.getAbsolutePath() + "\" "
                    + "/I\"" + tc.jniPlatform.getAbsolutePath() + "\" "
                    + "\"" + cppFile.getName() + "\" "
                    + "/Fe:\"" + dllFile.getName() + "\" /link /RELEASE /DLL"
                    + (vmpMarkers ? " VMProtectSDK64.lib /OPT:NOICF /OPT:NOREF" : "");
            pb = new ProcessBuilder("cmd.exe", "/c", cmd);
        } else {
            java.util.List<String> args = new java.util.ArrayList<String>();
            args.add(tc.compiler.getAbsolutePath());
            args.add("-O2");
            args.add("-s");
            args.add("-shared");
            args.add("-static-libgcc");
            args.add("-static-libstdc++");
            if (vmpMarkers) {
                args.add("-DJ2C_VMP");
            }
            args.add("-I" + tc.jniInclude.getAbsolutePath());
            args.add("-I" + tc.jniPlatform.getAbsolutePath());
            args.add(cppFile.getName());
            if (vmpMarkers) {
                // 直接把 MinGW 导入归档作为输入，不依赖 -L/-l 命名规则
                args.add("VMProtectSDK64.a");
            }
            args.add("-o");
            args.add(dllFile.getName());
            pb = new ProcessBuilder(args);
        }
        pb.directory(buildDir);
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = readAll(p.getInputStream());
        if (!p.waitFor(300, java.util.concurrent.TimeUnit.SECONDS)) {
            p.destroyForcibly();
            throw new IOException("j2c DLL 编译超时（300s）。\n" + tail(output));
        }
        if (p.exitValue() != 0 || !dllFile.isFile() || dllFile.length() < 1024) {
            throw new IOException("j2c DLL 编译失败：\n" + tail(output));
        }
        return output;
    }

    private static String tail(String s) {
        if (s == null) {
            return "(无编译器输出)";
        }
        s = s.trim();
        if (s.length() <= 3000) {
            return s;
        }
        return "..." + s.substring(s.length() - 3000);
    }

    private static String readAll(java.io.InputStream in) throws IOException {
        ByteArrayOutputStream bos = new ByteArrayOutputStream();
        byte[] buf = new byte[4096];
        int n;
        while ((n = in.read(buf)) > 0) {
            bos.write(buf, 0, n);
        }
        return new String(bos.toByteArray(), StandardCharsets.UTF_8);
    }
}
