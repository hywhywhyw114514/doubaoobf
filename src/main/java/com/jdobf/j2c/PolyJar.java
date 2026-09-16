package com.jdobf.j2c;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

/**
 * PE/ZIP 多态文件工具：把一个明文 PE（j2c 的通用 loader）前置到普通 jar
 * 文件头，并把 ZIP 中央目录里所有本地文件头偏移、以及 EOCD 中的中央目录
 * 起始偏移整体平移 PE 长度。
 *
 * <p>产物同时是：
 * <ul>
 *   <li>合法 ZIP/JAR：{@code java -jar}、ZipFile/ZipInputStream 照常工作
 *       （它们只经中央目录定位本地头，本地头内容不依赖文件绝对偏移）；</li>
 *   <li>合法 PE：操作系统可对该文件本身 {@code LoadLibrary/System.load}，
 *       PE 加载器只看文件头的 DOS/NT 头与节表，尾部 ZIP overlay 被忽略。</li>
 * </ul>
 *
 * <p>这样运行时无需在磁盘上释放任何临时 DLL：{@code System.load} 的目标
 * 就是用户手里的 jar 文件本身。本工具只在混淆器构建机上执行一次。
 */
public final class PolyJar {

    private static final int SIG_LOCAL = 0x04034b50;
    private static final int SIG_CENTRAL = 0x02014b50;
    private static final int SIG_EOCD = 0x06054b50;

    /** EOCD 固定头 22 字节；注释最长 65535。 */
    private static final int EOCD_FIXED = 22;
    private static final int EOCD_MAX_SCAN = 65557;

    private PolyJar() {
    }

    /**
     * 就地改造 {@code jar}：前置 {@code pe} 并重定位 ZIP 偏移。
     *
     * @throws IOException 文件不是预期的普通单盘 ZIP（ZIP64/分盘不支持）
     *                     或改写后校验失败
     */
    public static void prefixPe(File jar, byte[] pe) throws IOException {
        if (pe == null || pe.length < 2
                || (pe[0] & 0xFF) != 'M' || (pe[1] & 0xFF) != 'Z') {
            throw new IOException("loader PE must start with MZ");
        }
        byte[] zip = readAll(jar);
        byte[] out = build(zip, pe);
        FileOutputStream fos = new FileOutputStream(jar);
        try {
            fos.write(out);
        } finally {
            fos.close();
        }
        verify(jar, zip.length + pe.length);
    }

    /** 纯字节变换（测试/复用方便）：返回 pe + 偏移重定位后的 zip。 */
    static byte[] build(byte[] zip, byte[] pe) throws IOException {
        int prefix = pe.length;
        int eocd = findEocd(zip);
        int totalEntries = u16(zip, eocd + 10);
        if (u16(zip, eocd + 8) != totalEntries
                || (totalEntries & 0xFFFF) == 0xFFFF) {
            // 本项目写出的是普通单盘 jar；分盘/ZIP64 交给上层明确失败，
            // 不静默产出坏文件
            throw new IOException("unsupported zip (split archive or ZIP64)");
        }
        int cdSize = u32(zip, eocd + 12);
        int cdOff = u32(zip, eocd + 16);
        if (cdSize == 0xFFFFFFFFL || cdOff == 0xFFFFFFFFL) {
            throw new IOException("unsupported ZIP64 central directory");
        }
        if (cdOff < 0 || (long) cdOff + cdSize > eocd) {
            throw new IOException("bad central directory bounds");
        }

        byte[] out = new byte[prefix + zip.length];
        System.arraycopy(pe, 0, out, 0, prefix);
        System.arraycopy(zip, 0, out, prefix, zip.length);

        // 遍历中央目录：每条 +42 的本地头偏移 +prefix
        int p = cdOff;
        for (int i = 0; i < totalEntries; i++) {
            int o = prefix + p;
            if (u32(out, o) != SIG_CENTRAL) {
                throw new IOException("bad central file header at entry " + i);
            }
            int nameLen = u16(out, o + 28);
            int extraLen = u16(out, o + 30);
            int commentLen = u16(out, o + 32);
            int localOff = u32(out, o + 42);
            int newLocalOff = localOff + prefix;
            if (newLocalOff < 0) {
                throw new IOException("local header offset overflow");
            }
            putU32(out, o + 42, newLocalOff);
            p += 46 + nameLen + extraLen + commentLen;
        }
        if (p != cdOff + cdSize) {
            throw new IOException("central directory size mismatch");
        }

        // EOCD 中央目录起始偏移 +prefix（local headers 自身不动）
        putU32(out, prefix + eocd + 16, cdOff + prefix);
        return out;
    }

    private static int findEocd(byte[] zip) throws IOException {
        int start = Math.max(0, zip.length - EOCD_MAX_SCAN);
        for (int i = zip.length - EOCD_FIXED; i >= start; i--) {
            if (u32(zip, i) == SIG_EOCD) {
                return i;
            }
        }
        throw new IOException("EOCD signature not found");
    }

    /** 改写后回读校验：所有条目可经新中央目录定位并完整读取。 */
    private static void verify(File jar, int expectedLen) throws IOException {
        if (jar.length() != expectedLen) {
            throw new IOException("output length mismatch");
        }
        ZipFile zf = new ZipFile(jar);
        try {
            Enumeration<? extends ZipEntry> en = zf.entries();
            while (en.hasMoreElements()) {
                ZipEntry e = en.nextElement();
                InputStream is = zf.getInputStream(e);
                try {
                    byte[] buf = new byte[8192];
                    long total = 0;
                    int n;
                    while ((n = is.read(buf)) > 0) {
                        total += n;
                    }
                    if (total != e.getSize() && e.getSize() >= 0) {
                        throw new IOException("entry size mismatch: " + e.getName());
                    }
                } finally {
                    is.close();
                }
            }
        } finally {
            zf.close();
        }
    }

    private static byte[] readAll(File f) throws IOException {
        java.io.FileInputStream fis = new java.io.FileInputStream(f);
        try {
            ByteArrayOutputStream bos = new ByteArrayOutputStream(
                    (int) Math.max(64, f.length()));
            byte[] buf = new byte[65536];
            int n;
            while ((n = fis.read(buf)) > 0) {
                bos.write(buf, 0, n);
            }
            return bos.toByteArray();
        } finally {
            fis.close();
        }
    }

    private static int u16(byte[] b, int off) {
        return (b[off] & 0xFF) | ((b[off + 1] & 0xFF) << 8);
    }

    private static int u32(byte[] b, int off) {
        return (b[off] & 0xFF) | ((b[off + 1] & 0xFF) << 8)
                | ((b[off + 2] & 0xFF) << 16) | ((b[off + 3] & 0xFF) << 24);
    }

    private static void putU32(byte[] b, int off, int v) {
        b[off] = (byte) v;
        b[off + 1] = (byte) (v >>> 8);
        b[off + 2] = (byte) (v >>> 16);
        b[off + 3] = (byte) (v >>> 24);
    }
}
