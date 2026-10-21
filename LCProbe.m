//
//  LCProbe.m  -  TXM / signed-code-page write probe for LiveContainer guest apps
//  Diagnostic only. A crash AFTER the probe output is expected - that is the point.
//

#import <Foundation/Foundation.h>
#import <mach/mach.h>
#import <mach/mach_vm.h>
#import <mach/vm_region.h>
#import <mach/vm_prot.h>
#import <mach-o/dyld.h>
#import <mach-o/loader.h>
#import <libkern/OSCacheControl.h>
#import <sys/mman.h>
#import <sys/stat.h>
#import <sys/fcntl.h>
#import <signal.h>
#import <unistd.h>
#import <errno.h>
#import <IOKit/IOKitLib.h>
#include <stdarg.h>
#include <string.h>

static int gFd = -1;
static uint64_t gPS = 0;

extern int csops(pid_t pid, unsigned int ops, void *useraddr, size_t usersize);

#pragma mark - logging (fd stays open so a fatal crash still leaves the log)

static void lg(NSString *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    NSString *s = [[NSString alloc] initWithFormat:fmt arguments:ap];
    va_end(ap);
    NSLog(@"[LCProbe] %@", s);
    if (gFd >= 0) {
        NSString *line = [s stringByAppendingString:@"\n"];
        const char *c = line.UTF8String;
        if (c) {
            ssize_t w = write(gFd, c, strlen(c));
            (void)w;
            fsync(gFd);
        }
    }
}

#pragma mark - region info

static NSString *regionDesc(mach_vm_address_t addr) {
    mach_vm_address_t a = addr;
    mach_vm_size_t sz = 0;
    natural_t depth = 0;
    vm_region_submap_info_data_64_t info;
    mach_msg_type_number_t cnt = VM_REGION_SUBMAP_INFO_COUNT_64;
    kern_return_t kr = mach_vm_region_recurse(mach_task_self(), &a, &sz, &depth,
                                              (vm_region_recurse_info_t)&info, &cnt);
    if (kr != KERN_SUCCESS) return [NSString stringWithFormat:@"<region kr=%d>", kr];
    return [NSString stringWithFormat:@"cur=%d max=%d share=%d size=0x%llx",
            info.protection, info.max_protection, info.share_mode, sz];
}

static NSString *protStr(vm_prot_t p) {
    NSMutableString *s = [NSMutableString string];
    [s appendString:(p & VM_PROT_READ) ? @"r" : @"-"];
    [s appendString:(p & VM_PROT_WRITE) ? @"w" : @"-"];
    [s appendString:(p & VM_PROT_EXECUTE) ? @"x" : @"-"];
    return s;
}

#pragma mark - image lookup

static const struct mach_header_64 *findImage(const char *needle, NSString **pathOut) {
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

static uint64_t imageVMSize(const struct mach_header_64 *mh) {
    if (!mh) return 0;
    uint64_t end = 0;
    const uint8_t *p = (const uint8_t *)(mh + 1);
    for (uint32_t i = 0; i < mh->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)p;
        if (lc->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
            uint64_t e = seg->vmaddr + seg->vmsize;
            if (e > end) end = e;
        }
        p += lc->cmdsize;
    }
    uint64_t base = (uint64_t)(uintptr_t)mh;
    return end > base ? end - base : 0;
}

#pragma mark - JIT bridge (universal.js: mov x16,#1 ; brk #0xf00d ; ret)

__attribute__((naked, noinline))
static void *jit_bridge(void *addr, size_t len) {
    __asm__ __volatile__(
        "mov x16, #1\n\t"
        "brk #0xf00d\n\t"
        "ret\n\t");
}

#pragma mark - signal fallback (skips a brk that no JIT script is servicing)

static char gAltStack[64 * 1024];

static void onSignal(int sig, siginfo_t *si, void *uctx) {
    ucontext_t *uc = (ucontext_t *)uctx;
    uint64_t pc = 0;
#if defined(__arm64__)
    if (uc) pc = (uint64_t)__darwin_arm_thread_state64_get_pc(uc->uc_mcontext->__ss);
#endif
    lg(@"!! SIGNAL %d (%s) pc=0x%llx addr=%p", sig, strsignal(sig), pc,
       si ? si->si_addr : NULL);

    if (sig == SIGTRAP && uc) {
        uint32_t insn = *(uint32_t *)(uintptr_t)pc;
        if ((insn & 0xFFE0001F) == 0xD4200000) {
            uint32_t imm = (insn >> 5) & 0xFFFF;
            lg(@"!! brk #0x%x was not serviced by any JIT script -> skip it, x0 untouched", imm);
#if defined(__arm64__)
            __darwin_arm_thread_state64_set_pc_fptr(uc->uc_mcontext->__ss,
                                                   (void *)(uintptr_t)(pc + 4));
            return;
#endif
        }
    }
    signal(sig, SIG_DFL);
    raise(sig);
}

#pragma mark - T1: naive in-place patch

static void test_naive_inplace(mach_vm_address_t target, const char *label) {
    mach_vm_address_t page = target & ~(mach_vm_address_t)(gPS - 1);
    uint32_t off = (uint32_t)(target - page);
    kern_return_t kr;

    lg(@"---- T1 naive in-place patch @ %s", label);
    lg(@"     target=0x%llx page=0x%llx off=0x%x", target, page, off);
    lg(@"     BEFORE  %s", regionDesc(page));

    errno = 0;
    int r1 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE);
    lg(@"     mprotect(RW)             -> %d (errno=%d %s)", r1, errno, strerror(errno));

    kern_return_t kr_rw = mach_vm_protect(mach_task_self(), page, gPS, false,
                                          VM_PROT_READ | VM_PROT_WRITE | VM_PROT_COPY);
    lg(@"     mach_vm_protect(RW|COPY) -> %d (%s)", kr_rw, mach_error_string(kr_rw));
    lg(@"     AFTER-W %s", regionDesc(page));

    if (r1 == 0 || kr_rw == KERN_SUCCESS) {
        uintptr_t dst = (uintptr_t)(page + off);
        uint32_t orig;
        memcpy(&orig, (void *)dst, 4);
        uint32_t nop = 0xD503201F;
        memcpy((void *)dst, &nop, 4);
        uint32_t readback;
        memcpy(&readback, (void *)dst, 4);
        lg(@"     wrote NOP @+0x%x readback=0x%08x %s", off, readback,
           readback == nop ? @"(WRITE OK)" : @"(WRITE MISMATCH)");
        memcpy((void *)dst, &orig, 4);   // restore original bytes so the hash stays valid
        uint32_t restored;
        memcpy(&restored, (void *)dst, 4);
        lg(@"     restored readback=0x%08x %s", restored,
           restored == orig ? @"(CONTENT INTACT)" : @"(RESTORE FAILED)");
    } else {
        lg(@"     !! page never became writable, skipping the write step");
    }

    sys_icache_invalidate((void *)(uintptr_t)page, gPS);

    errno = 0;
    int r2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
    lg(@"     mprotect(RX) [restore]   -> %d (errno=%d %s)", r2, errno, strerror(errno));
    if (r2 != 0) {
        kr = mach_vm_protect(mach_task_self(), page, gPS, false,
                             VM_PROT_READ | VM_PROT_EXECUTE);
        lg(@"     mach_vm_protect(RX)      -> %d (%s)", kr, mach_error_string(kr));
    }
    lg(@"     AFTER   %s", regionDesc(page));
    lg(@"     ==> %s", (r2 == 0) ? @"X RESTORED (naive hook viable here)"
                                 : @"X LOST  <== root cause of the SIGBUS confirmed");
}

#pragma mark - T2/T3: replace the signed page through mach_vm_remap

static void test_remap(mach_vm_address_t target, mach_vm_address_t srcPage,
                       const char *label, const char *srcKind) {
    mach_vm_address_t page = target & ~(mach_vm_address_t)(gPS - 1);
    uint32_t off = (uint32_t)(target - page);
    kern_return_t kr;
    vm_prot_t cur = 0, mx = 0;

    lg(@"---- %s remap-overwrite @ %s", srcKind, label);
    lg(@"     target=0x%llx page=0x%llx src=0x%llx", target, page, srcPage);
    lg(@"     BEFORE  %s", regionDesc(page));
    lg(@"     src     %s", regionDesc(srcPage));

    kern_return_t krw = mach_vm_protect(mach_task_self(), srcPage, gPS, false,
                                        VM_PROT_READ | VM_PROT_WRITE);
    if (krw != KERN_SUCCESS) {
        krw = mach_vm_protect(mach_task_self(), srcPage, gPS, false,
                              VM_PROT_READ | VM_PROT_WRITE | VM_PROT_COPY);
    }
    lg(@"     src -> RW                -> %d (%s)", krw, mach_error_string(krw));
    if (krw != KERN_SUCCESS) {
        lg(@"     !! source page not writable, aborting this test");
        return;
    }

    memcpy((void *)(uintptr_t)srcPage, (const void *)(uintptr_t)page, gPS);
    uint32_t nop = 0xD503201F;
    memcpy((void *)(uintptr_t)(srcPage + off), &nop, 4);
    uint32_t chk;
    memcpy(&chk, (void *)(uintptr_t)(srcPage + off), 4);
    lg(@"     patched src +0x%x = 0x%08x %s", off, chk, chk == nop ? @"OK" : @"MISMATCH");

    kern_return_t krx = mach_vm_protect(mach_task_self(), srcPage, gPS, false,
                                        VM_PROT_READ | VM_PROT_EXECUTE);
    lg(@"     src -> RX                -> %d (%s)", krx, mach_error_string(krx));
    lg(@"     src after RX %s", regionDesc(srcPage));
    sys_icache_invalidate((void *)(uintptr_t)srcPage, gPS);

    mach_vm_address_t dst = page;
    kr = mach_vm_remap(mach_task_self(), &dst, gPS, 0,
                       VM_FLAGS_FIXED | VM_FLAGS_OVERWRITE,
                       mach_task_self(), srcPage, TRUE,
                       &cur, &mx, VM_INHERIT_COPY);
    lg(@"     *** mach_vm_remap(FIXED|OVERWRITE) -> %d (%s) cur=%s max=%s",
       kr, mach_error_string(kr), protStr(cur).UTF8String, protStr(mx).UTF8String);

    if (kr != KERN_SUCCESS) {
        lg(@"     ==> prediction A: kernel refuses to overwrite a signed code page");
        return;
    }

    lg(@"     AFTER   %s", regionDesc(page));
    uint32_t got;
    memcpy(&got, (void *)(uintptr_t)(page + off), 4);
    lg(@"     readback page+0x%x = 0x%08x %s", off, got,
       got == nop ? @"(PATCH LIVE)" : @"(UNEXPECTED CONTENT)");
    lg(@"     ==> remap ACCEPTED: now watch for a delayed CODESIGNING kill");

    errno = 0;
    int rr1 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE);
    lg(@"     re-patch mprotect(RW)    -> %d (errno=%d)", rr1, errno);
    if (rr1 == 0) {
        errno = 0;
        int rr2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
        lg(@"     re-patch mprotect(RX)    -> %d (errno=%d %s)", rr2, errno, strerror(errno));
    }
    lg(@"     AFTER-REPATCH %s", regionDesc(page));
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
}

#pragma mark - environment

static BOOL hasTXM(void) {
    io_registry_entry_t mm = IORegistryEntryFromPath(0, "IODeviceTree:/chosen/memory-map");
    if (mm == IO_OBJECT_NULL) return NO;
    NSArray *keys = (__bridge_transfer NSArray *)IORegistryEntryCreateCFProperty(
        mm, CFSTR(kIORegistryEntryPropertyKeysKey), 0, 0);
    IOObjectRelease(mm);
    return keys && [keys containsObject:@"TXM"];
}

static void dumpEnvironment(void) {
    lg(@"========================================================");
    lg(@"LCProbe  (TXM / signed-code-page diagnostic)");
    lg(@"========================================================");
    lg(@"os      : %@", NSProcessInfo.processInfo.operatingSystemVersionString);
    lg(@"pid     : %d   pagesize=0x%llx", getpid(), gPS);
    lg(@"HOME    : %s", getenv("HOME") ?: "(null)");
    lg(@"TXM key : %@", hasTXM() ? @"PRESENT (codeSigningMonitor expected = 2)" : @"absent");

    uint32_t flags = 0;
    if (csops(getpid(), 0, &flags, sizeof(flags)) == 0) {
        lg(@"csflags : 0x%08x  CS_DEBUGGED=%@ CS_HARD=%@ CS_KILL=%@", flags,
           (flags & 0x10000000) ? @"YES" : @"NO",
           (flags & 0x00000100) ? @"YES" : @"NO",
           (flags & 0x00000200) ? @"YES" : @"NO");
    }

    const char *tweakDir = getenv("LC_GLOBAL_TWEAKS_FOLDER");
    lg(@"tweaks  : %s", tweakDir ?: "(env unset)");

    uint32_t n = _dyld_image_count();
    lg(@"images  : %u", n);
    for (uint32_t i = 0; i < n && i < 40; i++) {
        const char *p = _dyld_get_image_name(i);
        lg(@"   [%2u] %s", i, p ? p : "?");
    }
}

#pragma mark - entry

__attribute__((constructor))
static void LCProbeInit(void) {
    @autoreleasepool {
        gPS = (uint64_t)vm_page_size;
        if (gPS < 0x4000) gPS = 0x4000;

        NSString *docDir = [NSHomeDirectory() stringByAppendingPathComponent:@"Documents"];
        [NSFileManager.defaultManager createDirectoryAtPath:docDir
                               withIntermediateDirectories:YES attributes:nil error:nil];
        NSString *outPath = [docDir stringByAppendingPathComponent:@"LCProbe-result.txt"];
        gFd = open(outPath.fileSystemRepresentation, O_CREAT | O_WRONLY | O_TRUNC, 0644);

        static char altStack[64 * 1024];
        stack_t ss = {0};
        ss.ss_sp = altStack;
        ss.ss_size = sizeof(altStack);
        sigaltstack(&ss, NULL);
        struct sigaction sa = {0};
        sa.sa_sigaction = onSignal;
        sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
        sigaction(SIGBUS, &sa, NULL);
        sigaction(SIGSEGV, &sa, NULL);
        sigaction(SIGILL, &sa, NULL);
        sigaction(SIGTRAP, &sa, NULL);

        dumpEnvironment();
        lg(@"result  : %@", outPath);

        const uint64_t offsets[3] = { 0x15a6b8cULL, 0x41771f8ULL, 0x14a78e4ULL };
        const char *names[3] = { "unity+0x15a6b8c(ohgihime)",
                                 "unity+0x41771f8(kamitsubaki)",
                                 "unity+0x14a78e4(dynamix)" };

        NSString *unityPath = nil;
        const struct mach_header_64 *unity = findImage("UnityFramework", &unityPath);
        if (unity) {
            lg(@"UnityFramework base=0x%llx size=0x%llx",
               (uint64_t)(uintptr_t)unity, imageVMSize(unity));
        } else {
            lg(@"UnityFramework not loaded -> fallback to main image");
            unity = findImage("/LiveContainer", &unityPath);
        }
        if (!unity) {
            lg(@"!! no usable image, aborting");
            return;
        }

        uint64_t base = (uint64_t)(uintptr_t)unity;
        uint64_t size = imageVMSize(unity);

        mach_vm_address_t targets[3] = {0};
        for (int i = 0; i < 3; i++) {
            if (offsets[i] < size) {
                targets[i] = (mach_vm_address_t)(base + offsets[i]);
                lg(@"target[%d] %s -> 0x%llx %s", i, names[i], targets[i],
                   regionDesc(targets[i]).UTF8String);
            } else {
                lg(@"target[%d] %s -> outside image (size=0x%llx), skipped",
                   i, names[i], size);
            }
        }

        if (targets[0]) {
            test_naive_inplace(targets[0], names[0]);
        }

        if (targets[1]) {
            mach_vm_address_t anonSrc = 0;
            kern_return_t kr = mach_vm_allocate(mach_task_self(), &anonSrc, gPS,
                                                VM_FLAGS_ANYWHERE);
            if (kr == KERN_SUCCESS) {
                lg(@"anon source page = 0x%llx %s", anonSrc,
                   regionDesc(anonSrc).UTF8String);
                test_remap(targets[1], anonSrc, names[1], "T2 anon");
            } else {
                lg(@"!! mach_vm_allocate failed: %d", kr);
            }
        }

        NSString *marker = [docDir stringByAppendingPathComponent:@"lcprobe_jit"];
        if (targets[2] && [NSFileManager.defaultManager fileExistsAtPath:marker]) {
            lg(@"---- T3 JIT page acquisition via brk #0xf00d");
            void *jit = jit_bridge(NULL, (size_t)gPS);
            lg(@"     jit_bridge(NULL,0x%llx) -> %p", gPS, jit);
            if (jit) {
                lg(@"     jit page %s", regionDesc((mach_vm_address_t)jit).UTF8String);
                test_remap(targets[2], (mach_vm_address_t)jit, names[2], "T3 jit");
            } else {
                lg(@"     !! no JIT page (universal.js loop is not servicing brk #0xf00d)");
            }
        } else if (targets[2]) {
            lg(@"---- T3 skipped (create Documents/lcprobe_jit to enable)");
        }

        lg(@"========================================================");
        lg(@"probe finished. If the app dies right after this line, the");
        lg(@"crash is the delayed consequence of T1 (page left non-exec).");
        lg(@"========================================================");
        if (gFd >= 0) close(gFd);
    }
}
