import java.io.File;
import java.io.PrintWriter;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Enumeration;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.util.CheckClassAdapter;

public final class CheckJar {
    public static void main(String[] args) throws Exception {
        File jar = new File(args[0]);
        int count = 0;
        try (URLClassLoader loader = new URLClassLoader(
                new URL[] { jar.toURI().toURL() }, CheckJar.class.getClassLoader());
             ZipFile zip = new ZipFile(jar)) {
            Enumeration<? extends ZipEntry> entries = zip.entries();
            while (entries.hasMoreElements()) {
                ZipEntry entry = entries.nextElement();
                if (!entry.getName().endsWith(".class")) {
                    continue;
                }
                ClassReader reader = new ClassReader(zip.getInputStream(entry));
                reader.accept(new CheckClassAdapter(new ClassVisitor(Opcodes.ASM9) {
                }), 0);
                CheckClassAdapter.verify(reader, loader, false, new PrintWriter(System.err));
                count++;
            }
        }
        System.out.println("CHECKED:" + count);
    }
}
