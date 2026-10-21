# LCProbe

Diagnostic dylib answering one question on iPadOS 26 (TXM):

**Can a tweak replace an already-signed `__TEXT` page (e.g. `UnityFramework`) with its own
executable copy, instead of writing into that page?**

Injected exactly like any other LiveContainer tweak.

## Tests

| # | Test | Destructive |
|---|------|-------------|
| T1 | naive inline-hook sequence IN PLACE: `mprotect(RW)` -> write NOP -> restore original bytes -> `mprotect(RX)` | yes: if X cannot be restored the page stays non-executable |
| T2 | `mach_vm_remap(FIXED|OVERWRITE)` over a signed page, source = anonymous page | maybe |
| T3 | same as T2 but the source page comes from the JIT `brk #0xf00d` path (needs `Documents/lcprobe_jit`) | maybe |

Targets are the exact faulting offsets from the reporter's crash logs:

* `UnityFramework+0x15a6b8c`
* `UnityFramework+0x41771f8`
* `UnityFramework+0x14a78e4`

If `UnityFramework` is not loaded the probe falls back to the main image and the
offsets are reported as out of range (not exercised).

## Output

`<guest HOME>/Documents/LCProbe-result.txt`, plus `[LCProbe] ...` lines on
stderr / idevicesyslog. Every line is `fsync`ed, so a crash keeps the evidence.

## Install

1. Copy `LCProbe.dylib` into LiveContainer's global tweak folder
   (`LiveContainer/Documents/Tweaks`).
2. Launch the guest app with JIT.
3. Read the result file from LiveContainer's file browser.
4. Delete the dylib afterwards.

## Reading the result

* `T1 ==> X LOST` together with a failing `mach_vm_protect(RX)`
  => confirmed: an in-place write permanently drops the page's execute right.
* `T2 *** mach_vm_remap(...) -> 12` (`KERN_PROTECTION_FAILURE`)
  => prediction A: the remap idea is dead on TXM.
* `T2 *** mach_vm_remap(...) -> 0` and the app survives
  => prediction C: the JIT-page + remap design is viable.
