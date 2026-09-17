import com.jdobf.core.ObfConfig;
import com.jdobf.core.Obfuscator;

/** 命令行驱动：PRESET 环境变量选强度；SPLIT=1 开启类拆分与重定向；参数: 输入 输出 [排除正则...] */
public class Harness {
    public static void main(String[] args) throws Exception {
        ObfConfig cfg = new ObfConfig();
        cfg.inputJar = args[0];
        cfg.outputJar = args[1];
        String preset = System.getenv("PRESET");
        if (preset == null) preset = "AGGRESSIVE";
        cfg.applyPreset(ObfConfig.Preset.valueOf(preset));
        String harden = System.getenv("HARDEN");
        if ("0".equals(harden)) {
            cfg.decompilerHardening = false;
        } else if ("1".equals(harden)) {
            cfg.decompilerHardening = true;
        }
        String hardenPasses = System.getenv("HARDEN_PASSES");
        if (hardenPasses != null) {
            cfg.decompilerHardeningPasses = Math.max(1, Math.min(3,
                    Integer.parseInt(hardenPasses.trim())));
        }
        if ("1".equals(System.getenv("SPLIT"))) {
            cfg.deadCodeClasses = true;
            if (cfg.deadClassCount == 0) cfg.deadClassCount = 6;
            cfg.splitRedirect = true;
        }
        String deadCountEnv = System.getenv("DEADCOUNT");
        if (deadCountEnv != null) {
            int n = Integer.parseInt(deadCountEnv.trim());
            cfg.deadCodeClasses = n > 0;
            cfg.deadClassCount = Math.max(0, n);
        }
        if ("1".equals(System.getenv("BRAINDEAD"))) {
            cfg.renameStyle = ObfConfig.RenameStyle.BRAINDEAD;
        }
        if ("1".equals(System.getenv("SHIT"))) {
            cfg.shitBloat = true;
        }
        if ("0".equals(System.getenv("DISPERSE"))) {
            cfg.disperseLogic = false;
        }
        if ("1".equals(System.getenv("DISPERSE"))) {
            cfg.disperseLogic = true;
        }
        String shitN = System.getenv("SHITN");
        if (shitN != null) {
            cfg.shitMethodsPerClass = Math.max(0, Math.min(400,
                    Integer.parseInt(shitN.trim())));
        }
        if ("1".equals(System.getenv("J2C"))) {
            cfg.j2c = true;
        }
        if ("1".equals(System.getenv("VMP"))) {
            cfg.vmpPack = true;
        }
        String j2cName = System.getenv("J2C_NATIVE_NAME");
        if (j2cName != null) {
            cfg.j2cNativeName = j2cName;
        }
        StringBuilder regex = new StringBuilder();
        for (int i = 2; i < args.length; i++) {
            if (regex.length() > 0) regex.append('\n');
            regex.append(args[i]);
        }
        cfg.exclusionRegexText = regex.toString();
        new Obfuscator(cfg, new Obfuscator.Listener() {
            public void log(String m) { System.out.println(m); }
            public void progress(int d, int t) { }
            public boolean cancelled() { return false; }
        }).run();
    }
}
