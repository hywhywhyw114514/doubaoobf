/*
 * Generic reflective image stage for the j2c bridge (dual-image edition).
 *
 * This loader itself is mapped by the OS directly from the running jar file:
 * the jar is a PE/ZIP polyglot -- this DLL sits in plaintext at the head of
 * the file while the ZIP central directory has been relocated past it, so
 * `java -jar x.jar` and System.load(x.jar's own path) both work on the very
 * same file. NOTHING is ever written to disk: no temp image is created.
 *
 * The two payload images never touch disk either: each arrives here as an
 * encrypted byte array, is decrypted in a scratch buffer, manually mapped
 * into the current process (sections, relocations, imports, unwind info,
 * TLS callbacks, entry point) into its own VirtualAlloc region, and its two
 * registration entries are resolved from the export table. The scratch
 * buffer is wiped immediately. Payload #2 is mapped on demand (the first
 * time a shell class belonging to that partition binds).
 *
 * Compiles as C (MSVC cl /TC-by-extension) and as C++ (MinGW g++ driver).
 * Exported JNI names are injected per build through j2cconf.h.
 */
#include "j2cconf.h"
#include "vmpmark.h"
#include <jni.h>
#include <windows.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>

/* 诊断追踪：设置环境变量 J2C_DEBUG_MAP 后写 %TEMP%\j2c_map_dbg.txt */
static void jtrace(const char *s) {
    static int on = -1;
    const char *dir;
    char path[1024];
    FILE *f;
    if (on < 0) {
        on = getenv("J2C_DEBUG_MAP") != 0 ? 1 : 0;
    }
    if (!on) {
        return;
    }
    dir = getenv("TEMP");
    if (!dir || !*dir) {
        dir = "C:\\Windows\\Temp";
    }
    snprintf(path, sizeof(path), "%s\\j2c_map_dbg.txt", dir);
    f = fopen(path, "a");
    if (f) {
        fputs(s, f);
        fputc('\n', f);
        fclose(f);
    }
}

#ifdef __cplusplus
extern "C" {
#endif

#ifndef J2C_MAPFN
#error j2cconf.h missing
#endif

typedef jint (JNICALL *arm_fn)(JavaVM *vm, void *reserved);
typedef jint (JNICALL *bind_fn)(JNIEnv *env, jclass cls, jobject shell);

BOOL WINAPI DllMain(HINSTANCE hinstDLL, DWORD fdwReason, LPVOID lpvReserved) {
    (void)lpvReserved;
    if (fdwReason == DLL_PROCESS_ATTACH) {
        /* 这个镜像就是用户手里的 jar 本身：绝不能删除/移动/改名它，
         * 也没有任何临时文件需要清理 */
        DisableThreadLibraryCalls(hinstDLL);
    }
    return TRUE;
}

/* 两个独立内存映射区：0 = 首映射 payload，1 = 按需 payload。
 * g_arm/g_bin 在调用 arm 之前就位，使镜像2 arm 内重入 mapM2 安全。 */
static volatile void *g_img[2];
static volatile void *g_arm[2];
static volatile void *g_bin[2];

/* scratch obfuscation tables: harmless mixing used on the hot path */
static volatile unsigned long g_seq;
static const unsigned char g_tap[32] = {
    0x21u, 0x7cu, 0x43u, 0x09u, 0x5eu, 0xa6u, 0x37u, 0xc8u,
    0x12u, 0x6bu, 0x94u, 0x0du, 0xf5u, 0x46u, 0x83u, 0x2au,
    0x51u, 0x1cu, 0xdeu, 0x64u, 0x9fu, 0x08u, 0x72u, 0x39u,
    0xb6u, 0x4du, 0xe0u, 0x15u, 0xa2u, 0x67u, 0x8cu, 0x33u
};

static unsigned long jmix(unsigned long v, unsigned long n) {
    unsigned long r = (v + 0x9e3779b1u) ^ (n * 0x85ebca77u);
    r ^= (r >> 13) + g_tap[n & 31];
    r += (r << 7) | (r >> 25);
    return r - ((v + 0x9e3779b1u) ^ (n * 0x85ebca77u)) + v; /* identity fold */
}

static void jfail(JNIEnv *env, const char *msg) {
    jclass cls = env->FindClass("java/lang/UnsatisfiedLinkError");
    if (cls) {
        env->ThrowNew(cls, msg);
    }
}

static unsigned char *j_in_image(const unsigned char *base, unsigned long isize,
                                 DWORD rva) {
    if (rva == 0 || (unsigned long)rva >= isize) {
        return NULL;
    }
    return (unsigned char *)(base + rva);
}

static DWORD j_protect(DWORD ch) {
    int x = (ch & IMAGE_SCN_MEM_EXECUTE) != 0;
    int w = (ch & IMAGE_SCN_MEM_WRITE) != 0;
    int r = (ch & IMAGE_SCN_MEM_READ) != 0;
    if (x && w) return PAGE_EXECUTE_READWRITE;
    if (x && r) return PAGE_EXECUTE_READ;
    if (x) return PAGE_EXECUTE;
    if (w && r) return PAGE_READWRITE;
    if (w) return PAGE_WRITECOPY;
    if (r) return PAGE_READONLY;
    return PAGE_NOACCESS;
}

static int j_map(unsigned char *file, size_t flen, const char *armn,
                 const char *binn, int slot) {
    VMP_BEGIN_ULTRA("j_map");
    jtrace("map-enter");
    IMAGE_DOS_HEADER *dos;
    IMAGE_NT_HEADERS64 *nt;
    IMAGE_OPTIONAL_HEADER64 *oh;
    IMAGE_SECTION_HEADER *sec;
    unsigned char *base;
    unsigned long isize;
    unsigned int i, j;
    int64_t delta;
    DWORD oldp;
    void *epa = NULL;
    void *epb = NULL;

    if (flen < 0x400 || file[0] != 'M' || file[1] != 'Z') {
        jtrace("fail-hdr-mz");
        return 0;
    }
    dos = (IMAGE_DOS_HEADER *)file;
    if ((size_t)dos->e_lfanew + sizeof(IMAGE_NT_HEADERS64) > flen) {
        jtrace("fail-hdr-lfanew");
        return 0;
    }
    nt = (IMAGE_NT_HEADERS64 *)(file + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE) {
        jtrace("fail-hdr-sig");
        return 0;
    }
    oh = &nt->OptionalHeader;
    if (oh->Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC
            || nt->FileHeader.Machine != IMAGE_FILE_MACHINE_AMD64) {
        jtrace("fail-hdr-magic");
        return 0;
    }
    isize = (unsigned long)oh->SizeOfImage;
    if (isize < 0x200 || (size_t)oh->SizeOfHeaders > flen) {
        jtrace("fail-hdr-size");
        return 0;
    }
    jtrace("hdr-ok");

    base = (unsigned char *)VirtualAlloc(NULL, isize,
            MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!base) {
        return 0;
    }
    memset(base, 0, isize);
    memcpy(base, file, oh->SizeOfHeaders);

    sec = IMAGE_FIRST_SECTION(nt);
    for (i = 0; i < nt->FileHeader.NumberOfSections; i++) {
        size_t sr = sec[i].SizeOfRawData;
        size_t va = sec[i].VirtualAddress;
        if (sr == 0 || sec[i].PointerToRawData == 0) {
            continue;
        }
        if ((size_t)sec[i].PointerToRawData >= flen) {
            continue;
        }
        if ((size_t)sec[i].PointerToRawData + sr > flen) {
            sr = flen - sec[i].PointerToRawData;
        }
        if (va >= isize) {
            continue;
        }
        if (sr > isize - va) {
            sr = isize - va;
        }
        memcpy(base + va, file + sec[i].PointerToRawData, sr);
    }

    /* base relocations */
    delta = (int64_t)(uintptr_t)base - (int64_t)oh->ImageBase;
    if (delta != 0) {
        DWORD rrva = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC].VirtualAddress;
        DWORD rsize = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC].Size;
        if (rrva && rsize && (unsigned long)rrva + rsize <= isize) {
            DWORD walk = 0;
            while (walk + sizeof(IMAGE_BASE_RELOCATION) <= rsize) {
                IMAGE_BASE_RELOCATION *br =
                        (IMAGE_BASE_RELOCATION *)(base + rrva + walk);
                DWORD cnt;
                WORD *items;
                if (br->SizeOfBlock == 0) {
                    break;
                }
                cnt = (br->SizeOfBlock - sizeof(IMAGE_BASE_RELOCATION)) / 2;
                items = (WORD *)((unsigned char *)br + sizeof(IMAGE_BASE_RELOCATION));
                for (j = 0; j < cnt; j++) {
                    WORD type = items[j] >> 12;
                    WORD off = items[j] & 0x0FFF;
                    if (type == IMAGE_REL_BASED_DIR64
                            && (unsigned long)br->VirtualAddress + off + 8 <= isize) {
                        uintptr_t *slotp =
                                (uintptr_t *)(base + br->VirtualAddress + off);
                        *slotp += (uintptr_t)delta;
                    }
                }
                walk += br->SizeOfBlock;
            }
        }
    }

    /* imports */
    {
        DWORD irva = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT].VirtualAddress;
        if (irva && (unsigned long)irva + sizeof(IMAGE_IMPORT_DESCRIPTOR) <= isize) {
            IMAGE_IMPORT_DESCRIPTOR *d =
                    (IMAGE_IMPORT_DESCRIPTOR *)(base + irva);
            for (i = 0; ; i++) {
                uintptr_t *nameThunk;
                uintptr_t *addrThunk;
                HMODULE mod;
                char *dn;
                if (d[i].OriginalFirstThunk == 0 && d[i].FirstThunk == 0
                        && d[i].Name == 0) {
                    break;
                }
                dn = (char *)j_in_image(base, isize, d[i].Name);
                if (!dn) {
                    jtrace("fail-imp-name");
                    VirtualFree(base, 0, MEM_RELEASE);
                    return 0;
                }
                mod = LoadLibraryA(dn);
                if (!mod) {
                    char tb[300];
                    snprintf(tb, sizeof(tb),
                            "fail-imp-loadlib err=%lu dll=%.120s",
                            (unsigned long)GetLastError(), dn);
                    jtrace(tb);
                    VirtualFree(base, 0, MEM_RELEASE);
                    return 0;
                }
                nameThunk = (uintptr_t *)j_in_image(base, isize,
                        d[i].OriginalFirstThunk ? d[i].OriginalFirstThunk
                                               : d[i].FirstThunk);
                addrThunk = (uintptr_t *)j_in_image(base, isize, d[i].FirstThunk);
                if (!nameThunk || !addrThunk) {
                    jtrace("fail-imp-thunk");
                    VirtualFree(base, 0, MEM_RELEASE);
                    return 0;
                }
                for (j = 0; nameThunk[j]; j++) {
                    FARPROC fp;
                    if (nameThunk[j] & IMAGE_ORDINAL_FLAG64) {
                        fp = GetProcAddress(mod,
                                (LPCSTR)(uintptr_t)(nameThunk[j] & 0xFFFF));
                    } else {
                        IMAGE_IMPORT_BY_NAME *im =
                                (IMAGE_IMPORT_BY_NAME *)j_in_image(base, isize,
                                           (DWORD)(nameThunk[j] & 0xFFFFFFFF));
                        if (!im) {
                            jtrace("fail-imp-im");
                            VirtualFree(base, 0, MEM_RELEASE);
                            return 0;
                        }
                        fp = GetProcAddress(mod, (LPCSTR)im->Name);
                    }
                    if (!fp) {
                        jtrace("fail-imp-proc");
                        VirtualFree(base, 0, MEM_RELEASE);
                        return 0;
                    }
                    addrThunk[j] = (uintptr_t)fp;
                }
            }
        }
    }
    jtrace("imports-ok");

    /* TLS callbacks may live in executable sections. The image was just
     * allocated PAGE_READWRITE, so make the whole mapping executable before
     * invoking any callback; the per-section protection pass below restores
     * the final rights before the entry point runs. DBP-packed payloads put
     * a runtime TLS callback in a code section and would otherwise hit DEP. */
    VirtualProtect(base, isize, PAGE_EXECUTE_READWRITE, &oldp);

    /* x64 unwind data for the mapped image */
    {
        DWORD xrva = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION].VirtualAddress;
        DWORD xsize = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION].Size;
        if (xrva && xsize >= sizeof(RUNTIME_FUNCTION)) {
            RtlAddFunctionTable((PRUNTIME_FUNCTION)(base + xrva),
                                xsize / (DWORD)sizeof(RUNTIME_FUNCTION),
                                (DWORD64)(uintptr_t)base);
        }
    }

    /* static TLS callbacks (CRT pre-init), before the entry point */
    {
        DWORD trva = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_TLS].VirtualAddress;
        if (trva) {
            IMAGE_TLS_DIRECTORY64 *td =
                    (IMAGE_TLS_DIRECTORY64 *)j_in_image(base, isize, trva);
            if (td && td->AddressOfCallBacks) {
                PIMAGE_TLS_CALLBACK *cb =
                        (PIMAGE_TLS_CALLBACK *)(uintptr_t)td->AddressOfCallBacks;
                while (*cb) {
                    (*cb)((LPVOID)base, DLL_PROCESS_ATTACH, NULL);
                    cb++;
                }
            }
        }
    }

    /* section protection */
    VirtualProtect(base, oh->SizeOfHeaders, PAGE_READONLY, &oldp);
    for (i = 0; i < nt->FileHeader.NumberOfSections; i++) {
        DWORD sz = sec[i].Misc.VirtualSize;
        DWORD prot = j_protect(sec[i].Characteristics);
        DWORD tmp;
        if (sz == 0) {
            sz = sec[i].SizeOfRawData;
        }
        if (sz && sec[i].VirtualAddress + sz <= isize) {
            VirtualProtect(base + sec[i].VirtualAddress, sz, prot, &tmp);
        }
    }

    /* entry point (CRT DllMain startup) */
    if (oh->AddressOfEntryPoint) {
        BOOL (WINAPI *ep)(HINSTANCE, DWORD, LPVOID);
        ep = (BOOL (WINAPI *)(HINSTANCE, DWORD, LPVOID))
                (base + oh->AddressOfEntryPoint);
        if (!ep((HINSTANCE)base, DLL_PROCESS_ATTACH, NULL)) {
            jtrace("fail-entrypoint");
            VirtualFree(base, 0, MEM_RELEASE);
            return 0;
        }
    }
    jtrace("entry-ok");

    /* resolve the two registration entries */
    {
        DWORD erva = oh->DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].VirtualAddress;
        if (erva) {
            IMAGE_EXPORT_DIRECTORY *ed =
                    (IMAGE_EXPORT_DIRECTORY *)j_in_image(base, isize, erva);
            if (ed) {
                DWORD *names = (DWORD *)j_in_image(base, isize,
                                                   ed->AddressOfNames);
                WORD *ords = (WORD *)j_in_image(base, isize,
                                                ed->AddressOfNameOrdinals);
                DWORD *funs = (DWORD *)j_in_image(base, isize,
                                                  ed->AddressOfFunctions);
                if (names && ords && funs) {
                    unsigned int got = 0;
                    for (j = 0; j < ed->NumberOfNames && got != 3u; j++) {
                        char *nm = (char *)j_in_image(base, isize, names[j]);
                        void *fp;
                        if (!nm || ords[j] >= ed->NumberOfFunctions) {
                            continue;
                        }
                        fp = (void *)(base + funs[ords[j]]);
                        if (strcmp(nm, armn) == 0) {
                            epa = fp;
                            got |= 1u;
                        } else if (strcmp(nm, binn) == 0) {
                            epb = fp;
                            got |= 2u;
                        }
                    }
                }
            }
        }
    }
    if (!epa || !epb) {
        jtrace("fail-exports");
        VirtualFree(base, 0, MEM_RELEASE);
        return 0;
    }
    jtrace("exports-ok");
    /* 先发布全局状态再调 arm：镜像2 arm 内可经 Java stage2 重入
     * mapM2，此时必须表现为已映射（幂等返回） */
    g_img[slot] = base;
    g_arm[slot] = epa;
    g_bin[slot] = epb;
    jtrace("map-ok");
    VMP_END();
    return 1;
}

/**
 * 共用映射入口：解密 XOR73 载荷 -> j_map 入槽 -> 调 arm（payload 自行
 * 多趟 DefineClass 复活本区隐藏类）。重复调用幂等返回 1，使「镜像 arm
 * 内回调 stage2 重入」与「stage2 被路由多次调用」都安全。
 */
static jint j_stage(JNIEnv *env, jclass cls, jbyteArray data, jint key,
                    jstring armn, jstring binn, int slot) {
    jsize n;
    jbyte *raw;
    unsigned char *buf;
    jsize i;
    const char *an;
    const char *bn;
    arm_fn arm;
    JavaVM *vm;
    jint rc;
    (void)cls;

    VMP_BEGIN_ULTRA("j_stage");
    jtrace("stage-enter");
    if (g_arm[slot]) {
        return 1;
    }
    if (!data || !armn || !binn) {
        jtrace("stage-fail-args");
        jfail(env, "stage failed");
        return 0;
    }
    n = env->GetArrayLength(data);
    if (n <= 0 || n > 64 * 1024 * 1024) {
        char tb[64];
        snprintf(tb, sizeof(tb), "stage-fail-range n=%ld", (long)n);
        jtrace(tb);
        jfail(env, "stage failed");
        return 0;
    }
    an = env->GetStringUTFChars(armn, NULL);
    bn = env->GetStringUTFChars(binn, NULL);
    raw = env->GetByteArrayElements(data, NULL);
    if (!an || !bn || !raw) {
        jtrace("stage-fail-jnigets");
        if (an) env->ReleaseStringUTFChars(armn, an);
        if (bn) env->ReleaseStringUTFChars(binn, bn);
        if (raw) env->ReleaseByteArrayElements(data, raw, JNI_ABORT);
        jfail(env, "stage failed");
        return 0;
    }
    buf = (unsigned char *)malloc((size_t)n);
    if (!buf) {
        jtrace("stage-fail-malloc");
        env->ReleaseStringUTFChars(armn, an);
        env->ReleaseStringUTFChars(binn, bn);
        env->ReleaseByteArrayElements(data, raw, JNI_ABORT);
        jfail(env, "stage failed");
        return 0;
    }
    {
        char tb[128];
        snprintf(tb, sizeof(tb), "stage-decrypt n=%ld key=%d an=%.32s",
                (long)n, (int)key, an);
        jtrace(tb);
    }
    memcpy(buf, raw, (size_t)n);
    env->ReleaseByteArrayElements(data, raw, JNI_ABORT);
    VMP_END();
    /* MB 级 XOR 解密循环刻意留在虚拟化区外（VM 解释逐条指令，长循环会
     * 慢到近似挂起）；循环本身只是密钥流异或，不值得虚拟化 */
    VMP_NOVEC
    for (i = 0; i < n; i++) {
        buf[i] = (unsigned char)(buf[i]
                ^ (unsigned char)((key + (jint)i * 73) & 255));
    }
    VMP_BEGIN_ULTRA("j_stage_map");
    /* opaque scratch work, result unused */
    g_seq += jmix((unsigned long)n ^ (unsigned long)key,
                  (unsigned long)(buf[n - 1] & 255));
    if (!j_map(buf, (size_t)n, an, bn, slot)) {
        jtrace("stage-map-failed");
        SecureZeroMemory(buf, (size_t)n);
        free(buf);
        env->ReleaseStringUTFChars(armn, an);
        env->ReleaseStringUTFChars(binn, bn);
        jfail(env, "stage failed");
        return 0;
    }
    jtrace("stage-map-ok");
    SecureZeroMemory(buf, (size_t)n);
    free(buf);
    env->ReleaseStringUTFChars(armn, an);
    env->ReleaseStringUTFChars(binn, bn);

    if (env->GetJavaVM(&vm) != 0) {
        jtrace("stage-getjavavm-failed");
        jfail(env, "stage failed");
        return 0;
    }
    arm = (arm_fn)g_arm[slot];
    rc = arm(vm, NULL);
    if (rc != JNI_VERSION_1_8) {
        jtrace("stage-arm-rc");
        jfail(env, "stage failed");
        return 0;
    }
    jtrace("stage-ok");
    VMP_END();
    return 1;
}

JNIEXPORT jint JNICALL J2C_MAPFN(JNIEnv *env, jclass cls,
                                 jbyteArray data, jint key,
                                 jstring armn, jstring binn) {
    VMP_BEGIN_MUT("mapfn");
    jint r = j_stage(env, cls, data, key, armn, binn, 0);
    VMP_END();
    return r;
}

JNIEXPORT jint JNICALL J2C_MAPFN2(JNIEnv *env, jclass cls,
                                  jbyteArray data, jint key,
                                  jstring armn, jstring binn) {
    VMP_BEGIN_MUT("mapfn2");
    jint r = j_stage(env, cls, data, key, armn, binn, 1);
    VMP_END();
    return r;
}

/*
 * bind 三态直通 Java 路由层：1 = 已在本区注册；0 = 本区注册失败
 * （致命）；2 = 该 shell 不属本区，Java 改调另一镜像。
 */
JNIEXPORT jint JNICALL J2C_BINDFN(JNIEnv *env, jclass cls, jobject shell) {
    VMP_BEGIN_MUT("bindfn");
    jint r = 0;
    if (!g_bin[0]) {
        jfail(env, "bind failed");
    } else {
        bind_fn fn = (bind_fn)g_bin[0];
        r = fn(env, cls, shell);
    }
    VMP_END();
    return r;
}

JNIEXPORT jint JNICALL J2C_BINDFN2(JNIEnv *env, jclass cls, jobject shell) {
    VMP_BEGIN_MUT("bindfn2");
    jint r = 0;
    if (!g_bin[1]) {
        jfail(env, "bind failed");
    } else {
        bind_fn fn = (bind_fn)g_bin[1];
        r = fn(env, cls, shell);
    }
    VMP_END();
    return r;
}

JNIEXPORT jint JNICALL J2C_PINGFN(JNIEnv *env, jclass cls, jint x) {
    (void)env;
    (void)cls;
    VMP_BEGIN_MUT("pingfn");
    jint r = (jint)(x ^ 0x3579);
    VMP_END();
    return r;
}

#ifdef __cplusplus
}
#endif
