//
//  LCProbe.m  -  TXM / signed-code-page policy probe for LiveContainer guest apps
//  v2: correct image sizing, wait for the guest image, non-destructive remap tests.
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

// The iOS SDK ships mach/mach_vm.h as a stub that #errors out; declare what we need.
extern kern_return_t mach_vm_allocate(vm_map_t, mach_vm_address_t *, mach_vm_size_t, int);
extern kern_return_t mach_vm_deallocate(vm_map_t, mach_vm_address_t, mach_vm_size_t);
extern kern_return_t mach_vm_protect(vm_map_t, mach_vm_address_t, mach_vm_size_t, boolean_t, vm_prot_t);
extern kern_return_t mach_vm_remap(vm_map_t, mach_vm_address_t *, mach_vm_size_t, mach_vm_offset_t,
                                   int, vm_map_t, mach_vm_address_t, boolean_t,
                                   vm_prot_t *, vm_prot_t *, vm_inherit_t);
extern kern_return_t mach_vm_region_recurse(vm_map_t, mach_vm_address_t *, mach_vm_size_t *, natural_t *,
                                            vm_region_recurse_info_t, mach_msg_type_number_t *);
extern int csops(pid_t pid, unsigned int ops, void *useraddr, size_t usersize);

#ifndef VM_FLAGS_FIXED
#define VM_FLAGS_FIXED 0x0
#endif
#ifndef VM_FLAGS_ANYWHERE
#define VM_FLAGS_ANYWHERE 0x1
#endif
#ifndef VM_FLAGS_OVERWRITE
#define VM_FLAGS_OVERWRITE 0x4000
#endif
#ifndef VM_PROT_COPY
#define VM_PROT_COPY 0x10
#endif

static int gFd = -1;
static uint64_t gPS = 0x4000;
static int gTest = 0;

#pragma mark - logging

static void lg(NSString *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    NSString *s = [[NSString alloc] initWithFormat:fmt arguments:ap];
    va_end(ap);
    NSLog(@"[LCProbe] %@", s);
    if (gFd >= 0) {
        NSString *line = [s stringByAppendingString:@"\n"];
        const char *c = line.UTF8String;
        if (c) { ssize_t w = write(gFd, c, strlen(c)); (void)w; fsync(gFd); }
    }
}

static void lgh(NSString *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    NSString *s = [[NSString alloc] initWithFormat:fmt arguments:ap];
    va_end(ap);
    lg(@"%@", s);
}

#pragma mark - vm helpers

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

static uint64_t pageOf(uint64_t a) { return a & ~(gPS - 1); }

#pragma mark - image layout

typedef struct {
    const struct mach_header_64 *mh;
    uint64_t base;        // runtime address of the Mach-O header == load address
    uint64_t minVmaddr;   // lowest segment vmaddr
    uint64_t slide;       // base - minVmaddr
    uint64_t totalSize;   // maxVmaddrEnd - minVmaddr
    uint64_t execOff;     // exec segment start, BASE-RELATIVE (crashlog imageOffset space)
    uint64_t execVmsize;
    uint64_t execFileoff;
} LCImage;

static const struct mach_header_64 *imageByName(const char *needle, NSString **pathOut, int *idxOut) {
    uint32_t n = _dyld_image_count();
    for (uint32_t i = 0; i < n; i++) {
        const char *p = _dyld_get_image_name(i);
        if (p && strstr(p, needle)) {
            if (pathOut) *pathOut = @(p);
            if (idxOut) *idxOut = (int)i;
            return (const struct mach_header_64 *)_dyld_get_image_header(i);
        }
    }
    return NULL;
}

static BOOL describeImage(const struct mach_header_64 *mh, LCImage *out) {
    if (!mh || mh->magic != MH_MAGIC_64) return NO;
    memset(out, 0, sizeof(*out));
    out->mh = mh;
    out->base = (uint64_t)(uintptr_t)mh;

    uint64_t minVm = UINT64_MAX, maxEnd = 0;
    uint64_t execVm = 0, execSize = 0, execFile = 0;
    const uint8_t *p = (const uint8_t *)(mh + 1);
    for (uint32_t i = 0; i < mh->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)p;
        if (lc->cmd == LC_SEGMENT_64 && lc->cmdsize >= sizeof(struct segment_command_64)) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
            if (seg->vmsize == 0) { p += lc->cmdsize; continue; }
            if (seg->vmaddr < minVm) minVm = seg->vmaddr;
            if (seg->vmaddr + seg->vmsize > maxEnd) maxEnd = seg->vmaddr + seg->vmsize;
            if ((seg->initprot & VM_PROT_EXECUTE) && execSize == 0) {
                execVm = seg->vmaddr;
                execSize = seg->vmsize;
                execFile = seg->fileoff;
            }
        }
        p += lc->cmdsize;
    }
    if (minVm == UINT64_MAX || maxEnd <= minVm) return NO;
    out->minVmaddr = minVm;
    out->totalSize = maxEnd - minVm;
    out->slide = out->base - minVm;
    out->execOff = execVm - minVm;      // convert to base-relative space
    out->execVmsize = execSize;
    out->execFileoff = execFile;
    return YES;
}

#pragma mark - JIT bridge (universal.js: mov x16,#1 ; brk #0xf00d ; ret)

__attribute__((naked, noinline))
static void *jit_bridge(void *addr, size_t len) {
    __asm__ __volatile__(
        "mov x16, #1\n\t"
        "brk #0xf00d\n\t"
        "ret\n\t");
}

#pragma mark - signal fallback (skip a brk nobody is servicing)

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
            lg(@"!! brk #0x%x unserviced -> skipping it", (insn >> 5) & 0xFFFF);
#if defined(__arm64__)
            __darwin_arm_thread_state64_set_pc_fptr(uc->uc_mcontext->__ss, (void *)(uintptr_t)(pc + 4));
            return;
#endif
        }
    }
    signal(sig, SIG_DFL);
    raise(sig);
}

#pragma mark - T1: naive in-place patch

static void test_naive_inplace(mach_vm_address_t target, const char *label) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);
    kern_return_t kr;

    lg(@"---- T1 naive in-place patch @ %s (destructive)", label);
    lg(@"     target=0x%llx page=0x%llx off=0x%x", target, page, off);
    lg(@"     BEFORE  %@", regionDesc(page));

    errno = 0;
    int r1 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE);
    lg(@"     mprotect(RW)             -> %d (errno=%d %s)", r1, errno, strerror(errno));
    kern_return_t kr_rw = mach_vm_protect(mach_task_self(), page, gPS, false,
                                          VM_PROT_READ | VM_PROT_WRITE | VM_PROT_COPY);
    lg(@"     mach_vm_protect(RW|COPY) -> %d (%s)", kr_rw, mach_error_string(kr_rw));
    lg(@"     AFTER-W %@", regionDesc(page));

    if (r1 == 0 || kr_rw == KERN_SUCCESS) {
        uintptr_t dst = (uintptr_t)(page + off);
        uint32_t orig; memcpy(&orig, (void *)dst, 4);
        uint32_t nop = 0xD503201F;
        memcpy((void *)dst, &nop, 4);
        uint32_t rb; memcpy(&rb, (void *)dst, 4);
        lg(@"     write NOP @+0x%x readback=0x%08x %@", off, rb,
           rb == nop ? @"(WRITE OK)" : @"(WRITE MISMATCH)");
        memcpy((void *)dst, &orig, 4);
        memcpy(&rb, (void *)dst, 4);
        lg(@"     restored readback=0x%08x %@", rb,
           rb == orig ? @"(CONTENT INTACT)" : @"(RESTORE FAILED)");
    } else {
        lg(@"     !! page never became writable; write step skipped");
    }

    sys_icache_invalidate((void *)(uintptr_t)page, gPS);

    errno = 0;
    int r2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
    lg(@"     mprotect(RX) [restore]   -> %d (errno=%d %s)", r2, errno, strerror(errno));
    if (r2 != 0) {
        kr = mach_vm_protect(mach_task_self(), page, gPS, false, VM_PROT_READ | VM_PROT_EXECUTE);
        lg(@"     mach_vm_protect(RX)      -> %d (%s)", kr, mach_error_string(kr));
    }
    lg(@"     AFTER   %@", regionDesc(page));
    lg(@"     ==> %@", (r2 == 0) ? @"X RESTORED (naive hook viable here)"
                                 : @"X LOST <== root cause of the SIGBUS confirmed");
}

#pragma mark - T2/T3: replace the signed page via mach_vm_remap (content identical)

// Returns YES if the remap was accepted (so T4 may run).
static BOOL test_remap(mach_vm_address_t target, mach_vm_address_t srcPage,
                       const char *label, const char *srcKind) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);
    kern_return_t kr;
    vm_prot_t cur = 0, mx = 0;

    lg(@"---- %s remap-overwrite @ %s", srcKind, label);
    lg(@"     target=0x%llx page=0x%llx off=0x%x src=0x%llx", target, page, off, srcPage);
    lg(@"     BEFORE  %@", regionDesc(page));
    lg(@"     src     %@", regionDesc(srcPage));

    kern_return_t krw = mach_vm_protect(mach_task_self(), srcPage, gPS, false,
                                        VM_PROT_READ | VM_PROT_WRITE);
    if (krw != KERN_SUCCESS) {
        krw = mach_vm_protect(mach_task_self(), srcPage, gPS, false,
                              VM_PROT_READ | VM_PROT_WRITE | VM_PROT_COPY);
    }
    lg(@"     src -> RW                -> %d (%s)", krw, mach_error_string(krw));
    if (krw != KERN_SUCCESS) { lg(@"     !! src not writable, abort"); return NO; }

    // content-identical copy of the signed page: no TXM hash mismatch possible
    memcpy((void *)(uintptr_t)srcPage, (const void *)(uintptr_t)page, gPS);
    lg(@"     copied original page (memcmp=%d)", memcmp((void *)(uintptr_t)srcPage, (void *)(uintptr_t)page, gPS));

    kern_return_t krx = mach_vm_protect(mach_task_self(), srcPage, gPS, false,
                                        VM_PROT_READ | VM_PROT_EXECUTE);
    lg(@"     src -> RX                -> %d (%s)", krx, mach_error_string(krx));
    lg(@"     src after RX %@", regionDesc(srcPage));
    sys_icache_invalidate((void *)(uintptr_t)srcPage, gPS);

    mach_vm_address_t dst = page;
    kr = mach_vm_remap(mach_task_self(), &dst, gPS, 0,
                       VM_FLAGS_FIXED | VM_FLAGS_OVERWRITE, mach_task_self(), srcPage, TRUE,
                       &cur, &mx, VM_INHERIT_COPY);
    lg(@"     *** mach_vm_remap(FIXED|OVERWRITE) -> %d (%s) cur=%@ max=%@",
       kr, mach_error_string(kr), protStr(cur), protStr(mx));

    if (kr != KERN_SUCCESS) {
        lg(@"     ==> PREDICTION A: kernel refuses to overwrite a signed code page");
        return NO;
    }

    lg(@"     AFTER   %@", regionDesc(page));
    int cmp = memcmp((void *)(uintptr_t)page, (void *)(uintptr_t)srcPage, gPS);
    lg(@"     content check memcmp=%d %@", cmp, cmp == 0 ? @"(IDENTICAL)" : @"(DIVERGED)");
    uint32_t w0; memcpy(&w0, (void *)(uintptr_t)(page + off), 4);
    lg(@"     word @+0x%x = 0x%08x", off, w0);
    lg(@"     ==> remap ACCEPTED (prediction C so far)");

    // can a hook now patch this page in place?
    errno = 0;
    int rr1 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE);
    lg(@"     re-patch mprotect(RW)    -> %d (errno=%d)", rr1, errno);
    if (rr1 == 0) {
        uint32_t nop = 0xD503201F;
        memcpy((void *)(uintptr_t)(page + off), &nop, 4);
        uint32_t rb; memcpy(&rb, (void *)(uintptr_t)(page + off), 4);
        lg(@"     write NOP @+0x%x readback=0x%08x %@", off, rb,
           rb == nop ? @"(WRITE OK)" : @"(WRITE MISMATCH)");
        memcpy((void *)(uintptr_t)(page + off), &w0, 4);   // keep content identical
        errno = 0;
        int rr2 = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
        lg(@"     re-patch mprotect(RX)    -> %d (errno=%d %s)", rr2, errno, strerror(errno));
        sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    }
    lg(@"     AFTER-REPATCH %@", regionDesc(page));
    return YES;
}

#pragma mark - T4: leave a patch in the remapped page

static void test_patch_persist(mach_vm_address_t target, const char *label) {
    mach_vm_address_t page = pageOf(target);
    uint32_t off = (uint32_t)(target - page);
    lg(@"---- T4 persistent patch on the remapped page @ %s (destructive)", label);
    errno = 0;
    int rw = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_WRITE);
    lg(@"     mprotect(RW) -> %d (errno=%d)", rw, errno);
    if (rw != 0) { lg(@"     !! cannot write, skipping"); return; }
    uint32_t nop = 0xD503201F;
    memcpy((void *)(uintptr_t)(page + off), &nop, 4);
    errno = 0;
    int rx = mprotect((void *)(uintptr_t)page, gPS, PROT_READ | PROT_EXEC);
    lg(@"     NOP written, mprotect(RX) -> %d (errno=%d)", rx, errno);
    sys_icache_invalidate((void *)(uintptr_t)page, gPS);
    lg(@"     NOW OBSERVE: app survives => TXM does not re-verify the remapped page");
    lg(@"                  app killed w/ CODESIGNING => content still validated");
}

#pragma mark - environment

static NSString *hardwareID(void) {
    struct utsname u;
    if (uname(&u) != 0) return @"?";
    return @(u.machine);
}

static void dumpEnvironment(void) {
    lg(@"========================================================");
    lg(@"LCProbe v2  (TXM / signed-code-page policy diagnostic)");
    lg(@"========================================================");
    lg(@"os      : %@", NSProcessInfo.processInfo.operatingSystemVersionString);
    lg(@"hw      : %@", hardwareID());
    lg(@"pid     : %d  pagesize=0x%llx", getpid(), gPS);
    lg(@"HOME    : %s", getenv("HOME") ?: "(null)");

    uint32_t flags = 0;
    if (csops(getpid(), 0, &flags, sizeof(flags)) == 0) {
        lg(@"csflags : 0x%08x  CS_DEBUGGED=%@ CS_HARD=%@ CS_KILL=%@", flags,
           (flags & 0x10000000) ? @"YES" : @"NO",
           (flags & 0x00000100) ? @"YES" : @"NO",
           (flags & 0x00000200) ? @"YES" : @"NO");
    }

    uint32_t n = _dyld_image_count();
    lg(@"images  : %u", n);
    for (uint32_t i = 0; i < n; i++) {
        const char *p = _dyld_get_image_name(i);
        const struct mach_header_64 *mh = (const struct mach_header_64 *)_dyld_get_image_header(i);
        LCImage info;
        if (describeImage(mh, &info)) {
            lg(@"   [%2u] base=0x%llx size=0x%llx exec=%llu/0x%llx %s", i, info.base,
               info.totalSize, (unsigned long long)info.execVmaddr, info.execVmsize,
               p ? p : "?");
        } else {
            lg(@"   [%2u] <unparsed> %s", i, p ? p : "?");
        }
    }
}

#pragma mark - driver

// rva is BASE-RELATIVE, i.e. exactly the "imageOffset" column of an .ips crash log.
static mach_vm_address_t pickTarget(LCImage *img, uint64_t rva, NSString **why) {
    if (rva < img->execOff || rva >= img->execOff + img->execVmsize) {
        *why = [NSString stringWithFormat:
                @"rva 0x%llx outside exec seg [0x%llx,0x%llx)",
                rva, img->execOff, img->execOff + img->execVmsize];
        return 0;
    }
    *why = [NSString stringWithFormat:@"rva 0x%llx inside exec seg", rva];
    return img->base + rva;
}

static void dumpTargetBytes(mach_vm_address_t addr, uint64_t rva) {
    if ((addr & 0xFFF) > 0xFF0) return;
    uint32_t w[4] = {0};
    memcpy(w, (const void *)(uintptr_t)addr, sizeof(w));
    lg(@"       bytes @+0x%llx: %08x %08x %08x %08x", rva, w[0], w[1], w[2], w[3]);
    const char *kind = "unknown";
    uint32_t a = w[0];
    if ((a & 0xFFC07FFF) == 0xA9807BFD || (a & 0xFFC07FFF) == 0xA9007BFD) kind = "stp x29,x30,... (prologue)";
    else if ((a & 0xFFC003FF) == 0xD10003FF) kind = "sub sp,sp,#imm (prologue)";
    else if ((a & 0xFFFFFFE0) == 0xA9BF7BE0) kind = "pacibsp (prologue)";
    else if ((a & 0xFF9FFC1F) == 0xF81F0FFE) kind = "str x30,[sp,#-imm]! (prologue)";
    else if ((a & 0xFC000000) == 0x14000000) kind = "b <branch> (chained/patch)";
    else if ((a & 0xFFE0001F) == 0xD4200000) kind = "brk #imm";
    lg(@"       heuristic: %s", kind);
}

static void runTests(void) {
    gTest++;
    NSString *docDir = [NSHomeDirectory() stringByAppendingPathComponent:@"Documents"];

    NSString *unityPath = nil; int unityIdx = -1;
    const struct mach_header_64 *unity = imageByName("UnityFramework", &unityPath, &unityIdx);
    if (!unity) {
        if (gTest < 90) {
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 1 * NSEC_PER_SEC),
                           dispatch_get_main_queue(), ^{
                @autoreleasepool { runTests(); }
            });
            return;
        }
        lg(@"!! UnityFramework never appeared after 90s; falling back to the main image");
        unity = imageByName("/LiveContainer", &unityPath, &unityIdx);
    } else {
        lg(@"found UnityFramework after %d poll(s)", gTest);
    }
    if (!unity) { lg(@"!! no usable image, abort"); return; }

    LCImage img;
    if (!describeImage(unity, &img)) { lg(@"!! cannot parse image, abort"); return; }

    lg(@"--------------------------------------------------------");
    lg(@"image   : %@", unityPath);
    lg(@"index   : %d  base=0x%llx slide=0x%llx totalSize=0x%llx", unityIdx, img.base,
       img.slide, img.totalSize);
    lg(@"exec seg: base-rel 0x%llx vmsize=0x%llx fileoff=0x%llx", img.execOff,
       img.execVmsize, img.execFileoff);
    lg(@"--------------------------------------------------------");

    if (img.execVmsize == 0) { lg(@"!! image has no executable segment, abort"); return; }

    // Requested targets, BASE-RELATIVE (same space as an .ips "imageOffset").
    // Sources, in order: Documents/lcprobe_targets.txt, else the auto pick.
    uint64_t rvas[4] = {0, 0, 0, 0};
    int nRva = 0;
    NSString *cfg = [docDir stringByAppendingPathComponent:@"lcprobe_targets.txt"];
    NSString *cfgText = [NSString stringWithContentsOfFile:cfg encoding:NSUTF8StringEncoding error:nil];
    if (cfgText.length) {
        for (NSString *raw in [cfgText componentsSeparatedByString:@"\n"]) {
            NSString *t = [raw stringByTrimmingCharactersInSet:
                           NSCharacterSet.whitespaceAndNewlineCharacterSet];
            if (t.length == 0 || [t hasPrefix:@"#"] || nRva >= 4) continue;
            if ([t hasPrefix:@"0x"] || [t hasPrefix:@"0X"]) t = [t substringFromIndex:2];
            uint64_t v = strtoull(t.UTF8String, NULL, 16);
            if (v) { rvas[nRva++] = v; }
        }
        lg(@"targets file: %d rva(s) from %@", nRva, cfg.lastPathComponent);
    }

    if (nRva == 0) {
        // auto: two points inside the exec segment, page-aligned to distinct pages
        uint64_t mid = img.execOff + (img.execVmsize / 2);
        mid &= ~(gPS - 1);
        mid += 0x800;                       // middle of that page
        rvas[0] = mid; rvas[1] = 0; nRva = 1;
        if (img.execVmsize > gPS * 4) {
            uint64_t q = img.execOff + (img.execVmsize / 4);
            q &= ~(gPS - 1);
            q += 0x800;
            if (q != mid) { rvas[1] = q; nRva = 2; }
        }
        lg(@"no targets file -> auto targets +0x%llx,+0x%llx", rvas[0], rvas[1]);
    }

    mach_vm_address_t targets[4] = {0};
    const char *labels[4] = { "target0", "target1", "target2", "target3" };
    int nTarget = 0;
    for (int i = 0; i < nRva; i++) {
        NSString *w = nil;
        mach_vm_address_t a = pickTarget(&img, rvas[i], &w);
        if (a) {
            targets[i] = a;
            nTarget++;
            lg(@"target[%d] %@ -> 0x%llx %@", i, w, a, regionDesc(a));
            dumpTargetBytes(a, rvas[i]);
        } else {
            lg(@"target[%d] skipped: %@", i, w);
        }
    }

    if (nTarget == 0) {
        lg(@"!! no usable target: exec segment is 0x%llx bytes starting at +0x%llx",
           img.execVmsize, img.execOff);
        lg(@"   write one hex BASE-RELATIVE offset per line into");
        lg(@"   Documents/lcprobe_targets.txt and relaunch");
        return;
    }

    // compact the survivors so tA/tB are always valid
    mach_vm_address_t tA = 0, tB = 0;
    for (int i = 0; i < nRva; i++) {
        if (!targets[i]) continue;
        if (!tA) { tA = targets[i]; }
        else if (!tB) { tB = targets[i]; }
    }

    lg(@"selected tA=0x%llx tB=0x%llx", tA, tB);

    // ---- T2 first: non-destructive anon-source remap
    mach_vm_address_t anonSrc = 0;
    kern_return_t kr = mach_vm_allocate(mach_task_self(), &anonSrc, gPS, VM_FLAGS_ANYWHERE);
    BOOL remapped = NO;
    if (kr == KERN_SUCCESS) {
        lg(@"anon source page = 0x%llx %@", anonSrc, regionDesc(anonSrc));
        remapped = test_remap(tA, anonSrc, labels[0], "T2 anon");
        mach_vm_deallocate(mach_task_self(), anonSrc, gPS);
    } else {
        lg(@"!! mach_vm_allocate failed: %d", kr);
    }

    // ---- T3: JIT-sourced page (needs Documents/lcprobe_jit)
    if (tB && [NSFileManager.defaultManager fileExistsAtPath:
               [docDir stringByAppendingPathComponent:@"lcprobe_jit"]]) {
        lg(@"---- T3 JIT page acquisition via brk #0xf00d");
        void *jit = jit_bridge(NULL, (size_t)gPS);
        lg(@"     jit_bridge(NULL,0x%llx) -> %p", gPS, jit);
        if (jit) {
            lg(@"     jit page %@", regionDesc((mach_vm_address_t)jit));
            test_remap(tB, (mach_vm_address_t)jit, labels[1], "T3 jit");
        } else {
            lg(@"     !! no JIT page (universal.js loop not servicing brk #0xf00d)");
        }
    } else if (tB) {
        lg(@"---- T3 skipped (create Documents/lcprobe_jit to enable)");
    }

    // ---- T4: leave a patch behind (destructive); only if the remap was accepted
    if (remapped) {
        test_patch_persist(tA, labels[0]);
    } else {
        lg(@"---- T4 skipped (no remap accepted)");
    }

    // ---- T1 last: destructive in-place patch
    test_naive_inplace(tA, labels[0]);

    lg(@"========================================================");
    lg(@"probe finished. A crash right after this line is the delayed");
    lg(@"consequence of T1 (page left without execute permission).");
    lg(@"========================================================");
    if (gFd >= 0) { close(gFd); gFd = -1; }
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

        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(3 * NSEC_PER_SEC)),
                       dispatch_get_main_queue(), ^{
            @autoreleasepool { runTests(); }
        });
    }
}
