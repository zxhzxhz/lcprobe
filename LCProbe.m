//
//  LCProbe.m  v4  -  TXM exec-permission policy probe
//  v3 result: mach_vm_remap(OVERWRITE) over a signed __TEXT page = KERN_PROTECTION_FAILURE.
//  v4 asks the remaining question: can any path give us an EXECUTABLE page at all,
//  and can we patch the signed page via RWX instead of RW->write->RX?
//

#import <Foundation/Foundation.h>
#import <mach/mach.h>
#import <mach/vm_region.h>
#import <mach-o/dyld.h>
#import <mach-o/loader.h>
#import <libkern/OSCacheControl.h>
#import <sys/mman.h>
#import <sys/stat.h>
#import <sys/fcntl.h>
#import <sys/ucontext.h>
#import <sys/utsname.h>
#import <signal.h>
#import <unistd.h>
#import <errno.h>
#include <stdarg.h>
#include <string.h>

extern kern_return_t mach_vm_allocate(vm_map_t, mach_vm_address_t *, mach_vm_size_t, int);
extern kern_return_t mach_vm_deallocate(vm_map_t, mach_vm_address_t, mach_vm_size_t);
extern kern_return_t mach_vm_protect(vm_map_t, mach_vm_address_t, mach_vm_size_t, boolean_t, vm_prot_t);
extern kern_return_t mach_vm_region_recurse(vm_map_t, mach_vm_address_t *, mach_vm_size_t *, natural_t *,
                                            vm_region_recurse_info_t, mach_msg_type_number_t *);
extern int csops(pid_t pid, unsigned int ops, void *useraddr, size_t usersize);

#ifndef VM_FLAGS_ANYWHERE
#define VM_FLAGS_ANYWHERE 0x1
#endif
#ifndef VM_PROT_COPY
#define VM_PROT_COPY 0x10
#endif

static int gFd = -1;
static uint64_t gPS = 0x4000;

static void lg(NSString *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    NSString *s = [[NSString alloc] initWithFormat:fmt arguments:ap];
    va_end(ap);
    NSLog(@"[LCProbe] %@", s);
    if (gFd >= 0) {
        NSString *line = [s stringByAppendingString:@"\n"];
        const char *c = line.UTF8String;
        if (c) { ssize_t w = write(gFd, c, strlen(c)); (void)w; fsync(gFd); }
    }
}

static NSString *regionDesc(mach_vm_address_t addr) {
    mach_vm_address_t a = addr; mach_vm_size_t sz = 0; natural_t depth = 0;
    vm_region_submap_info_data_64_t info;
    mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
    kern_return_t kr = mach_vm_region_recurse(mach_task_self(), &a, &sz, &depth,
                                              (vm_region_recurse_info_t)&info, &cnt);
    if (kr != KERN_SUCCESS) return [NSString stringWithFormat:@"<region kr=%d>", kr];
    return [NSString stringWithFormat:@"cur=%d max=%d share=%d size=0x%llx",
            info.protection, info.max_protection, info.share_mode, sz];
}

static uint64_t pageOf(uint64_t a) { return a & ~(gPS - 1); }

typedef struct {
    const struct mach_header_64 *mh;
    uint64_t base, minVmaddr, slide, totalSize, execOff, execVmsize, execFileoff;
} LCImage;

static const struct mach_header_64 *imageByName(const char *needle, NSString **pathOut) {
    uint32_t n = _dyld_image_count();
    for (uint32_t i = 0; i < n; i++) {
        const char *p = _dyld_get_image_name(i);
        if (p && strstr(p, needle)) {
            if (pathOut) *pathOut = @(p);
            return (const struct mach_header_64 *)_dyld_get_image_header(i);
        }
    }
    return NULL;
}

static BOOL describeImage(const struct mach_header_64 *mh, LCImage *out) {
    if (!mh || mh->magic != MH_MAGIC_64) return NO;
    memset(out, 0, sizeof(*out));
    out->mh = mh; out->base = (uint64_t)(uintptr_t)mh;
    uint64_t minVm = UINT64_MAX, maxEnd = 0, execVm = 0, execSize = 0, execFile = 0;
    const uint8_t *p = (const uint8_t *)(mh + 1);
    for (uint32_t i = 0; i < mh->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)p;
        if (lc->cmd == LC_SEGMENT_64 && lc->cmdsize >= sizeof(struct segment_command_64)) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
            if (seg->vmsize == 0) { p += lc->cmdsize; continue; }
            if (seg->vmaddr < minVm) minVm = seg->vmaddr;
            if (seg->vmaddr + seg->vmsize > maxEnd) maxEnd = seg->vmaddr + seg->vmsize;
            if ((seg->initprot & VM_PROT_EXECUTE) && execSize == 0) {
                execVm = seg->vmaddr; execSize = seg->vmsize; execFile = seg->fileoff;
            }
        }
        p += lc->cmdsize;
    }
    if (minVm == UINT64_MAX || maxEnd <= minVm) return NO;
    out->minVmaddr = minVm; out->totalSize = maxEnd - minVm; out->slide = out->base - minVm;
    out->execOff = execVm - minVm; out->execVmsize = execSize; out->execFileoff = execFile;
    return YES;
}

__attribute__((naked, noinline))
static void *jit_bridge(void *addr, size_t len) {
    __asm__ __volatile__("mov x16, #1\n\t" "brk #0xf00d\n\t" "ret\n\t");
}

static void onSignal(int sig, siginfo_t *si, void *uctx) {
    ucontext_t *uc = (ucontext_t *)uctx;
    uint64_t pc = 0;
#if defined(__arm64__)
    if (uc) pc = (uint64_t)__darwin_arm_thread_state64_get_pc(uc->uc_mcontext->__ss);
#endif
    lg(@"!! SIGNAL %d (%s) pc=0x%llx addr=%p", sig, strsignal(sig), pc, si ? si->si_addr : NULL);
    if (sig == SIGTRAP && uc) {
        uint32_t insn = *(uint32_t *)(uintptr_t)pc;
        if ((insn & 0xFFE0001F) == 0xD4200000) {
            lg(@"!! brk #0x%x unserviced -> skip", (insn >> 5) & 0xFFFF);
#if defined(__arm64__)
            __darwin_arm_thread_state64_set_pc_fptr(uc->uc_mcontext->__ss, (void *)(uintptr_t)(pc + 4));
            return;
#endif
        }
    }
    signal(sig, SIG_DFL); raise(sig);
}

// ---- T3: can ANY anonymous page keep PROT_EXEC on TXM?
static void test_jit_and_anon(void) {
    lg(@"---- T3 page-pool viability");

    mach_vm_address_t anon = 0;
    kern_return_t kr = mach_vm_allocate(mach_task_self(), &anon, gPS, VM_FLAGS_ANYWHERE);
    if (kr == KERN_SUCCESS) {
        lg(@"     anon alloc 0x%llx %@", anon, regionDesc(anon));
        kr = mach_vm_protect(mach_task_self(), anon, gPS, false, VM_PROT_READ | VM_PROT_EXECUTE);
        lg(@"     anon mach_vm_protect(RX) -> %d %@ -- %@", kr, regionDesc(anon),
           (kr == 0) ? @"kr ok" : @"kr fail");
        int mr = mprotect((void *)(uintptr_t)anon, gPS, PROT_READ | PROT_WRITE | PROT_EXEC);
        lg(@"     anon mprotect(RWX)       -> %d (errno=%d) %@", mr, errno, regionDesc(anon));
        mach_vm_deallocate(mach_task_self(), anon, gPS);
    }

    void *jit = jit_bridge(NULL, (size_t)gPS);
    lg(@"     jit_bridge(NULL,0x%llx) -> %p", gPS, jit);
    if (jit) lg(@"     jit page %@", regionDesc((mach_vm_address_t)jit));
    else lg(@"     JIT channel unavailable (brk 0xf00d unserviced)");
}

// ---- T5: ask for RWX BEFORE any downgrade happens (max_prot is still 7)
static void test_patch_rwx(mach_vm_address_t target, const char *label,
                           BOOL writePatch) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);
    kern_return_t kr;

    lg(@"---- T5 mprotect(RWX) on the signed page @ %s", label);
    lg(@"     page=0x%llx off=0x%x BEFORE %@", page, off, regionDesc(page));

    errno = 0;
    int r = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE | PROT_EXEC);
    lg(@"     mprotect(RWX)                    -> %d (errno=%d %s) %@",
       r, errno, strerror(errno), regionDesc(page));

    if (r != 0) {
        errno = 0;
        int r2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
        lg(@"     fallback mprotect(RX)           -> %d (errno=%d) %@", r2, errno, regionDesc(page));
        kr = mach_vm_protect(mach_task_self(), page, gPS, false,
                             VM_PROT_READ | VM_PROT_WRITE | VM_PROT_EXECUTE);
        lg(@"     mach_vm_protect(RWX)            -> %d (%s) %@", kr,
           mach_error_string(kr), regionDesc(page));
        kr = mach_vm_protect(mach_task_self(), page, gPS, false,
                             VM_PROT_READ | VM_PROT_WRITE);
        lg(@"     mach_vm_protect(RW)             -> %d (%s) %@", kr,
           mach_error_string(kr), regionDesc(page));
        lg(@"     ==> no writable path to this page");
        return;
    }

    uint32_t orig; memcpy(&orig, (void *)(uintptr_t)(page + off), 4);
    uint32_t orig2; memcpy(&orig2, (void *)(uintptr_t)(page + off + 4), 4);
    lg(@"     original bytes %08x %08x", orig, orig2);

    if (!writePatch) {
        lg(@"     (probe only, content untouched)");
        return;
    }

    // exactly what the tweak does: mov w0,#1 ; ret
    uint32_t patch[2] = { 0x52800020, 0xD65F03C0 };
    memcpy((void *)(uintptr_t)(page + off), patch, 8);
    uint32_t rb[2]; memcpy(rb, (void *)(uintptr_t)(page + off), 8);
    lg(@"     wrote 52800020 d65f03c0 -> readback %08x %08x %@", rb[0], rb[1],
       (rb[0] == patch[0] && rb[1] == patch[1]) ? @"(PATCH LIVE)" : @"(WRITE FAILED)");
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    lg(@"     AFTER PATCH %@", regionDesc(page));
    lg(@"     ==> if the guest keeps running AND the feature is unlocked,");
    lg(@"         RWX in-place patching works on this OS. If it dies with");
    lg(@"         CODESIGNING, TXM hash-checks the page at exec time.");
}

// ---- T6: replace the page with a private anonymous RWX mapping
static void test_mmap_fixed(mach_vm_address_t target, const char *label) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);
    lg(@"---- T6 mmap(MAP_FIXED, RWX, ANON) over the signed page @ %s", label);
    lg(@"     BEFORE %@", regionDesc(page));

    void *snap = malloc(gPS);
    if (!snap) { lg(@"     !! malloc failed"); return; }
    memcpy(snap, (void *)(uintptr_t)page, gPS);

    void *got = mmap((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE | PROT_EXEC,
                     MAP_FIXED | MAP_ANON | MAP_PRIVATE, -1, 0);
    errno = 0;
    lg(@"     mmap(MAP_FIXED) -> %p (errno=%d %s)", got, errno, strerror(errno));
    if (got == MAP_FAILED) { free(snap); return; }

    memcpy((void *)(uintptr_t)page, snap, gPS);
    free(snap);
    uint32_t patch[2] = { 0x52800020, 0xD65F03C0 };
    memcpy((void *)(uintptr_t)(page + off), patch, 8);
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    lg(@"     AFTER  %@ patch@+0x%x live", regionDesc(page), off);
    lg(@"     ==> watch for CODESIGNING kill");
}

static uint64_t defaultRvaForPath(NSString *path) {
    NSString *p = path.lowercaseString;
    if ([p containsString:@"ohgihime"]) return 0x15a6b8cULL;
    if ([p containsString:@"kamitsubaki"]) return 0x41771f8ULL;
    if ([p containsString:@"dynamix"]) return 0x14a78e4ULL;
    return 0;
}

static void runTests(int attempt) {
    NSString *unityPath = nil;
    const struct mach_header_64 *unity = imageByName("UnityFramework", &unityPath);
    if (!unity) {
        if (attempt < 90) {
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 1 * NSEC_PER_SEC),
                           dispatch_get_main_queue(), ^{ @autoreleasepool { runTests(attempt + 1); } });
            return;
        }
        lg(@"!! UnityFramework never appeared");
        return;
    }
    LCImage img;
    if (!describeImage(unity, &img)) { lg(@"!! cannot parse image"); return; }

    lg(@"--------------------------------------------------------");
    lg(@"image   : %@", unityPath);
    lg(@"base=0x%llx slide=0x%llx total=0x%llx exec=+0x%llx/0x%llx", img.base,
       img.slide, img.totalSize, img.execOff, img.execVmsize);

    NSString *docDir = [NSHomeDirectory() stringByAppendingPathComponent:@"Documents"];
    uint64_t rvas[4] = {0,0,0,0}; int nRva = 0;
    NSString *cfgText = [NSString stringWithContentsOfFile:
        [docDir stringByAppendingPathComponent:@"lcprobe_targets.txt"]
        encoding:NSUTF8StringEncoding error:nil];
    if (cfgText.length) {
        for (NSString *raw in [cfgText componentsSeparatedByString:@"\n"]) {
            NSString *t = [raw stringByTrimmingCharactersInSet:
                           NSCharacterSet.whitespaceAndNewlineCharacterSet];
            if (t.length == 0 || [t hasPrefix:@"#"] || nRva >= 4) continue;
            if ([t hasPrefix:@"0x"] || [t hasPrefix:@"0X"]) t = [t substringFromIndex:2];
            uint64_t v = strtoull(t.UTF8String, NULL, 16);
            if (v) rvas[nRva++] = v;
        }
        lg(@"targets from file: %d", nRva);
    }
    if (nRva == 0) {
        uint64_t d = defaultRvaForPath(unityPath);
        if (d) { rvas[nRva++] = d; lg(@"targets: crashlog RVA 0x%llx for this app", d); }
        else {
            uint64_t mid = img.execOff + (img.execVmsize / 2);
            rvas[nRva++] = (mid & ~(gPS - 1)) + 0x800;
            lg(@"targets: auto +0x%llx", rvas[0]);
        }
    }

    mach_vm_address_t tA = 0;
    for (int i = 0; i < nRva; i++) {
        if (rvas[i] < img.execOff || rvas[i] >= img.execOff + img.execVmsize) {
            lg(@"target[%d] rva 0x%llx outside exec seg [0x%llx,0x%llx)", i, rvas[i],
               img.execOff, img.execOff + img.execVmsize);
            continue;
        }
        mach_vm_address_t a = img.base + rvas[i];
        lg(@"target[%d] +0x%llx -> 0x%llx %@", i, rvas[i], a, regionDesc(a));
        uint32_t w[2]; memcpy(w, (const void *)(uintptr_t)a, 8);
        lg(@"       bytes %08x %08x", w[0], w[1]);
        if (!tA) tA = a;
    }
    if (!tA) { lg(@"!! no usable target"); return; }
    lg(@"--------------------------------------------------------");

    test_jit_and_anon();

    NSString *markerMMAP = [docDir stringByAppendingPathComponent:@"lcprobe_mmap"];
    if ([NSFileManager.defaultManager fileExistsAtPath:markerMMAP]) {
        test_mmap_fixed(tA, "target0");
        return;
    }

    NSString *markerProbe = [docDir stringByAppendingPathComponent:@"lcprobe_probeonly"];
    BOOL writePatch = ![NSFileManager.defaultManager fileExistsAtPath:markerProbe];
    test_patch_rwx(tA, "target0", writePatch);

    lg(@"========================================================");
    lg(@"probe done");
    lg(@"========================================================");
    if (gFd >= 0) { close(gFd); gFd = -1; }
}

__attribute__((constructor))
static void LCProbeInit(void) {
    @autoreleasepool {
        gPS = (uint64_t)vm_page_size; if (gPS < 0x4000) gPS = 0x4000;
        NSString *docDir = [NSHomeDirectory() stringByAppendingPathComponent:@"Documents"];
        [NSFileManager.defaultManager createDirectoryAtPath:docDir
                               withIntermediateDirectories:YES attributes:nil error:nil];
        gFd = open([docDir stringByAppendingPathComponent:@"LCProbe-result.txt"].fileSystemRepresentation,
                   O_CREAT | O_WRONLY | O_TRUNC, 0644);

        static char altStack[64 * 1024];
        stack_t ss = {0}; ss.ss_sp = altStack; ss.ss_size = sizeof(altStack); sigaltstack(&ss, NULL);
        struct sigaction sa = {0}; sa.sa_sigaction = onSignal; sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
        sigaction(SIGBUS,&sa,NULL); sigaction(SIGSEGV,&sa,NULL);
        sigaction(SIGILL,&sa,NULL); sigaction(SIGTRAP,&sa,NULL);

        lg(@"========================================================");
        lg(@"LCProbe v4  (TXM exec-permission policy)");
        lg(@"========================================================");
        lg(@"os   : %@", NSProcessInfo.processInfo.operatingSystemVersionString);
        struct utsname u; if (uname(&u) == 0) lg(@"hw   : %s", u.machine);
        lg(@"pid  : %d pagesize=0x%llx", getpid(), gPS);
        uint32_t flags = 0;
        if (csops(getpid(), 0, &flags, sizeof(flags)) == 0)
            lg(@"csflags 0x%08x CS_DEBUGGED=%@", flags, (flags & 0x10000000) ? @"YES" : @"NO");

        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(3 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{ @autoreleasepool { runTests(0); } });
    }
}
