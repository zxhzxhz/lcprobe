//
//  LCProbe.m  v6  -  FINAL open question on iOS 26/27 TXM
//
//  Established (v3/v5):
//    T1  mprotect(RW) -> write -> mprotect(RX)   : RX returns EACCES(13), max stuck rw-
//    T2  mach_vm_remap(FIXED|OVERWRITE) over __TEXT : KERN_PROTECTION_FAILURE(2)
//    T3  anon page + mach_vm_protect(RX) = 0 but cur=r--, exec -> SIGBUS
//
//  Remaining: is the max_prot downgrade triggered by ASKING for W, or by WRITING?
//    T5a  single-call mprotect(RWX) then write        <- decisive
//    T5b  mprotect(RW) then mprotect(RWX) then write  <- control
//  T3 is now opt-in (Documents/lcprobe_anonexec) so it can never mask T5.
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
    return [NSString stringWithFormat:@"cur=%d max=%d share=%d",
            info.protection, info.max_protection, info.share_mode];
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

static void onSignal(int sig, siginfo_t *si, void *uctx) {
    ucontext_t *uc = (ucontext_t *)uctx;
    uint64_t pc = 0;
#if defined(__arm64__)
    if (uc) pc = (uint64_t)__darwin_arm_thread_state64_get_pc(uc->uc_mcontext->__ss);
#endif
    lg(@"!! SIGNAL %d (%s) pc=0x%llx addr=%p", sig, strsignal(sig), pc, si ? si->si_addr : NULL);
    signal(sig, SIG_DFL);
}

// ---------- T5a: single-call RWX, then write ----------
static BOOL t5_singleRWX(mach_vm_address_t target, const char *label) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);

    lg(@"---- T5a SINGLE-CALL mprotect(RWX) @ %s", label);
    lg(@"     page=0x%llx off=0x%x BEFORE %@", page, off, regionDesc(page));
    uint32_t orig[2]; memcpy(orig, (const void *)(uintptr_t)(page + off), 8);
    lg(@"     original %08x %08x", orig[0], orig[1]);

    errno = 0;
    int r = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE | PROT_EXEC);
    lg(@"     mprotect(RWX) -> %d (errno=%d %s)  AFTER-CALL %@",
       r, errno, strerror(errno), regionDesc(page));

    if (r != 0) {
        lg(@"     ==> REJECTED at the mprotect() call: no RWX request is honoured");
        return NO;
    }

    uint32_t patch[2] = { 0x52800020, 0xD65F03C0 };
    memcpy((void *)(uintptr_t)(page + off), patch, 8);
    uint32_t rb[2]; memcpy(rb, (void *)(uintptr_t)(page + off), 8);
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    lg(@"     wrote %08x %08x / read %08x %08x  %@", patch[0], patch[1], rb[0], rb[1],
       (rb[0] == patch[0] && rb[1] == patch[1]) ? @"(WRITE OK)" : @"(WRITE FAILED)");
    lg(@"     AFTER-WRITE %@", regionDesc(page));

    errno = 0;
    int r2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
    lg(@"     shrink to RX -> %d (errno=%d %s)  AFTER %@", r2, errno, strerror(errno),
       regionDesc(page));

    if (r != 0) return NO;
    kern_return_t kr = mach_vm_protect(mach_task_self(), page, gPS, false,
                                       VM_PROT_READ | VM_PROT_WRITE | VM_PROT_EXECUTE);
    lg(@"     mach_vm_protect(RWX) -> %d (%s) %@", kr, mach_error_string(kr), regionDesc(page));

    lg(@"     ==> patch is LIVE. If the guest survives and the feature is unlocked,");
    lg(@"         single-call RWX is the fix. A CODESIGNING kill means no.");
    return YES;
}

// ---------- T5b: RW first (control), then W+X together ----------
static void t5_splitRWX(mach_vm_address_t target, const char *label) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);

    lg(@"---- T5b control: RW then RWX (two calls) @ %s", label);
    lg(@"     BEFORE %@", regionDesc(page));

    errno = 0;
    int r1 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE);
    lg(@"     mprotect(RW)  -> %d (errno=%d)  %@", r1, errno, regionDesc(page));

    errno = 0;
    int r2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE | PROT_EXEC);
    lg(@"     mprotect(RWX) -> %d (errno=%d)  %@", r2, errno, regionDesc(page));

    uint32_t orig[2]; memcpy(orig, (const void *)(uintptr_t)(page + off), 8);
    uint32_t patch[2] = { 0x52800020, 0xD65F03C0 };
    memcpy((void *)(uintptr_t)(page + off), patch, 8);
    uint32_t rb[2]; memcpy(rb, (void *)(uintptr_t)(page + off), 8);
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    lg(@"     wrote %08x %08x / read %08x %08x", patch[0], patch[1], rb[0], rb[1]);
    lg(@"     AFTER %@", regionDesc(page));
    lg(@"     ==> if max already dropped to rw- here, the downgrade happens on the W REQUEST");
    (void)orig;
}

// ---------- T3 (opt-in): anonymous page exec ----------
static void t3_anonExec(void) {
    lg(@"---- T3 (opt-in) anonymous page exec");
    mach_vm_address_t page = 0;
    if (mach_vm_allocate(mach_task_self(), &page, gPS, VM_FLAGS_ANYWHERE) != KERN_SUCCESS) {
        lg(@"     alloc failed"); return;
    }
    uint32_t stub[2] = { 0x52800020, 0xD65F03C0 };
    memcpy((void *)(uintptr_t)page, stub, 8);
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    kern_return_t kr = mach_vm_protect(mach_task_self(), page, gPS, false,
                                       VM_PROT_READ | VM_PROT_EXECUTE);
    lg(@"     page=0x%llx mach_vm_protect(RX) -> %d %@", page, kr, regionDesc(page));
    lg(@"     calling … (SIGBUS here is the expected result on TXM)");
    int (*f)(void) = (int (*)(void))(uintptr_t)page;
    int ret = f();
    lg(@"     returned %d", ret);
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
    NSString *docDir = [NSHomeDirectory() stringByAppendingPathComponent:@"Documents"];

    if (!unity) {
        if (attempt < 90) {
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 1 * NSEC_PER_SEC),
                           dispatch_get_main_queue(), ^{ @autoreleasepool { runTests(attempt + 1); } });
            return;
        }
        lg(@"!! UnityFramework never appeared"); return;
    }

    LCImage img;
    if (!describeImage(unity, &img)) { lg(@"!! cannot parse image"); return; }
    lg(@"--------------------------------------------------------");
    lg(@"image   : %@", unityPath);
    lg(@"base=0x%llx exec=+0x%llx/0x%llx", img.base, img.execOff, img.execVmsize);

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
    }
    if (nRva == 0) {
        uint64_t d = defaultRvaForPath(unityPath);
        if (d) { rvas[nRva++] = d; }
        else { uint64_t mid = img.execOff + (img.execVmsize / 2);
               rvas[nRva++] = (mid & ~(gPS - 1)) + 0x800; }
    }

    // two DISTINCT pages so T5a and T5b do not poison each other
    mach_vm_address_t pages[4] = {0,0,0,0};
    int nPage = 0;
    for (int i = 0; i < nRva; i++) {
        if (rvas[i] < img.execOff || rvas[i] >= img.execOff + img.execVmsize) {
            lg(@"target[%d] +0x%llx outside exec seg", i, rvas[i]); continue; }
        mach_vm_address_t a = img.base + rvas[i];
        lg(@"target[%d] +0x%llx -> 0x%llx %@", i, rvas[i], a, regionDesc(a));
        BOOL dup = NO;
        for (int k = 0; k < nPage; k++) if (pageOf(pages[k]) == pageOf(a)) dup = YES;
        if (!dup && nPage < 4) pages[nPage++] = a;
    }
    if (nPage == 0) {
        // fall back to a second page inside the segment
        uint64_t q = (img.execOff + (img.execVmsize / 2)) & ~(gPS - 1);
        pages[nPage++] = img.base + q + 0x800;
        lg(@"fallback target 0x%llx %@", pages[0], regionDesc(pages[0]));
    }
    lg(@"--------------------------------------------------------");

    // ---------- DECISIVE: T5a on the first page ----------
    BOOL t5aOK = t5_singleRWX(pages[0], "page0");

    // ---------- control: T5b on a second page (only if it exists) ----------
    if (nPage > 1) {
        t5_splitRWX(pages[1], "page1");
    } else {
        lg(@"---- T5b skipped (only one target page)");
        lg(@"     create Documents/lcprobe_targets.txt with a second RVA to run it");
    }

    // ---------- opt-in extras ----------
    if ([NSFileManager.defaultManager fileExistsAtPath:
         [docDir stringByAppendingPathComponent:@"lcprobe_anonexec"]]) {
        t3_anonExec();
    } else {
        lg(@"---- T3 skipped (create Documents/lcprobe_anonexec to run)");
    }

    lg(@"========================================================");
    lg(@"VERDICT: T5a=%@", t5aOK ? @"RWX ACCEPTED" : @"RWX REJECTED");
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
        sigaction(SIGBUS,&sa,NULL); sigaction(SIGSEGV,&sa,NULL); sigaction(SIGILL,&sa,NULL);

        lg(@"========================================================");
        lg(@"LCProbe v6  (final: is the max_prot downgrade on W-request or on write?)");
        lg(@"========================================================");
        lg(@"os   : %@", NSProcessInfo.processInfo.operatingSystemVersionString);
        struct utsname u; if (uname(&u) == 0) lg(@"hw   : %s", u.machine);
        lg(@"pid  : %d pagesize=0x%llx", getpid(), gPS);
        uint32_t flags = 0;
        if (csops(getpid(), 0, &flags, sizeof(flags)) == 0)
            lg(@"csflags 0x%08x CS_DEBUGGED=%@", flags, (flags & 0x10000000) ? @"YES" : @"NO");

        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(4 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{ @autoreleasepool { runTests(0); } });
    }
}
