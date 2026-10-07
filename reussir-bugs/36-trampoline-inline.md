# 36. A texture's import trampoline has no inline attribute

**Kind:** missed optimization. Not a bug: rrc's output is correct;
patches 36-a and 36-b are an optimization.

## Summary

**Kind:** missed optimization. **Status:** patched (36-a, with the review
fixes in 36-b), not applied in `./reussir` yet (made on branch
`l2r-inline` of a Reussir worktree, on `l2r-anybox` 1eb710b4); reviewed
(review-inline: one high finding, a stack overflow, and smaller ones; all
fixed in 36-b; a second look is pending). Before the patch, lean2rr kept
its read textures small (perf-array-reads); with the one-word `Box` the
read of an `Array` element no longer fitted (below).

**Verdict: missed optimization.** Reussir code calls a texture (an
`#[ffi(import)]` function with a Rust body) through an import trampoline
that rrc defines in the module: it packs the arguments and calls the
texture's `_ffi` boundary function, which comes from the texture's
bitcode. The trampoline gets no inline attribute. LLVM inlines the `_ffi`
function into it (when the texture is compiled for the same CPU, as
lean2rr's driver does), then inlines the trampoline into each caller by
its ordinary cost model: at a call site that it judges cold (a block whose
frequency is below 2% of the caller's entry, deep in branches) only below
a cost of 45, against 250 at an ordinary site at `-O aggressive`. What the
texture's Rust code asks for (`#[inline(always)]`) does not reach the
trampoline. So a texture that costs 46 to 250 is inlined at an ordinary
call site and stays a call at a cold one, with its argument packing and,
in lean2rr's case, the reference counting around the call (the caller's
increment of an argument and the texture's decrement no longer cancel).
Patch 36-a marks a texture and its trampoline `alwaysinline` when LLVM
would inline the texture at an ordinary call site and inlining it
everywhere is safe (36-b: not for a large stack frame or a texture that
cannot return).

## Symptom and repro

Repro [`repros/bug36-trampoline-inline.rr`](repros/bug36-trampoline-inline.rr):
the texture `mix` (some arithmetic and a cold call, cost 70) called once in
`main` and once under seven conditions that LLVM's branch heuristics
expect false.

**Command** (`run.sh bug36`, the textures compiled for the native CPU as
`scripts/l2r.py` compiles them): `rrc bug36-trampoline-inline.rr -o
OUT.ll --emit llvm-ir -O aggressive`.

- *Expected* (an inline attribute on the trampoline): no call of `mix`
  left.
- *Reussir ef922049, l2r-local d79f8b70*: `main`'s call is inlined; the
  cold site keeps `call i64 @_RC3mix(...)`. The inliner's remarks on the
  unoptimized IR (`opt -O3 -mcpu=native -pass-remarks-missed=inline`):
  `'_RC3mix' not inlined into '_RC4deep' because too costly to inline
  (cost=70, threshold=45)`.
- *With 36-a* (`l2r-inline` df9d0677): FIXED, both calls inlined.

In lean2rr: lean-zip's LZ77 loop (perf-array-reads). With the array read
as one texture that checks the bounds and releases the array (cost 80 for
a `ByteArray` read), 279 of the program's array reads stayed calls; a read
that decrements first and checks after, one texture of cost 55, left 41
calls in the LZ77 loop alone. lean2rr's reads are now three textures of
lower cost each (the view protocol,
[docs/implementation/ownership.md](../docs/implementation/ownership.md#reads-give-their-reference-up-first-for-a-view)),
and none stays a call.

## Cause

`rewriteImport` in `lib/Conversion/BasicOpsLowering/BasicOpsLowering.cpp`
(`ReussirTrampolineOpConversionPattern`) replaces the body-less
declaration with a definition that calls the boundary symbol; it creates
the `LLVMFuncOp` with no attributes but the sanitizer passthrough
(`inheritSanitizerPassthrough`). The cold-site threshold is LLVM's
(`-inline-cold-callsite-threshold`, 45; `InlineCostCallAnalyzer::
isColdCallSite`, relative frequency `-cold-callsite-rel-freq`, 2%).

## What lean2rr does

Before 36-a, lean2rr kept the textures of reads small: each cost less
than 45 once the `_ffi` function was inlined into its trampoline (the
runtime's other hot textures are small for the same reason;
`tests/runtime/ffi-inline-check.sh` fails on a texture called through the
packed-argument boundary).

Since `Box` is the one-word `LAny` (every `Array α` is an `RVec<LAny>`),
the read of an array element (`l2r_view_take<LAny>`) no longer fits: the
copy of a box tests the word's low bit and masks its top bits before the
increment (the old enum box's copy was an unguarded increment), which puts
the texture over the cold-site threshold (it was just under). At a call
site LLVM judges cold, such a read stays a call: without 36-a,
`tests/runtime/ffi-inline-check.sh` fails on `RtReadsDeep` (7 calls of
`l2r_view_take<LAny>`; the reads of `ByteArray` and `FloatArray` stay
inline). A branch-free copy (the increment of an immediate sent to the
array header's padding word) did not fit either. With 36-a the check
passes (every test of it, `RtReadsDeep` included), whatever the textures
cost below the ordinary threshold. lean2rr keeps the three read textures
(they are smaller, and the decrement before the bounds check is what lets
LLVM cancel the increments).

## Patch

Patch files
[`patches/36-a-inline-small-textures.patch`](patches/36-a-inline-small-textures.patch)
(commit `df9d0677` on branch `l2r-inline` of a Reussir worktree, made on
`l2r-anybox` 1eb710b4, that is `l2r-local` d79f8b70 + 38-a + 13-d; it
also applies on d79f8b70 and on ef922049 alone) and
[`patches/36-b-inline-guards.patch`](patches/36-b-inline-guards.patch)
(commit `0ea91383` on the same branch, after 03-a: the review's fixes).

- **The mark.** `rewriteImport` gives the trampoline it defines the LLVM
  function attribute `"reussir-import-boundary"="<boundary symbol>"` (an
  MLIR `passthrough` entry). Nothing else reads it.
- **The pass.** `ImportTrampolineInlinePass` (new,
  `lib/LLVMPass/AllocationSimplication/ImportTrampolineInline.cpp`) is the
  first pass of the backend's LLVM pipeline
  (`reussirRunBackendLLVMPipeline`, `lib/CAPI/Jit.cpp`) at `-O default`
  and `-O aggressive`, after the texture bitcode is linked. For each marked
  trampoline whose boundary function has a body in the module, it marks
  both functions `alwaysinline` when all of these hold:
  - LLVM may inline the call of the boundary in the trampoline
    (`getAttributeBasedInliningDecision`: compatible target features and
    attributes, no `noinline`, a boundary the linker cannot replace;
    `isInlineViable`);
  - the boundary is not `cold` and can return: it is not `noreturn` and
    has a `ret` (36-b);
  - the boundary's stack frame is static and at most 1024 bytes (36-b,
    below);
  - the trampoline is not interposable (36-b);
  - the call's inline cost (`getInliningCostEstimate`) is at most the
    pipeline's own inline threshold (`getInlineParamsFromOptLevel`: 225 at
    `-O default`, 250 at `-O aggressive`).
- `-O size` and `-O none` are unchanged. `reussir-llvm-opt` registers the
  pass as `reussir-import-trampoline-inline`.
  `docs/design/polymorphic-ffi.md` describes it.

**Why `alwaysinline`.** LLVM's inliner applies the cold-site threshold
after all its other adjustments. `inlinehint` raises the threshold of an
ordinary call site (to 325) but not that of a cold one: on the lit test's
IR, LLVM 23's `opt -O3` gives `'mix' not inlined into 'deep' because too
costly to inline (cost=70, threshold=45)` with and without `inlinehint`.
Only `alwaysinline` (or profile data) changes the decision at a cold
site. Both functions need it: the always-inliner inlines the trampoline
into each caller first, and the boundary's call is then in the caller,
at the same cold site.

**Why the bound.** A texture gets the attribute only when its cost,
measured at its call in the trampoline, is at most the threshold of an
ordinary call site: each call site gets at most a threshold's worth of
code. The cost at a real call site can differ (constant arguments,
bonuses), so this is close to, not exactly, LLVM's decision at an
ordinary site; at cold sites it changes the decision. Not marked: larger
textures (in the programs of `ffi-inline-check.sh`, 32 of the 509 to 541
trampolines: `l2r_str_lit`, the string hashes, `lean_mk_string`, process
and socket operations, `l2r_run_main`), and with 36-b 10 more that cannot
return (`l2r_internal_panic`, `l2r_array_index_bug_code`, `l2r_exit`,
`l2r_process_exit`, ...).

**Why the frame rule (36-b).** LLVM's inliner does not inline a callee
whose static allocas exceed 1024 bytes
(`InlineConstants::TotalAllocaSizeRecursiveCaller`,
`-recursive-inline-max-stacksize`) into a recursive caller. `alwaysinline`
skips that check, and the pass cannot see whether the trampoline's
callers are recursive. 36-a inlined a texture with a 64 KiB buffer into
every frame of a non-tail recursive function: at depth 2000 the program
overflowed its stack, where the unpatched rrc printed 1 (the review's
repro, now the lit test `frontend/ffi_import_inline_recursive.rr`). 36-b
leaves a texture alone when its static allocas sum to more than 1024
bytes, or when it has a dynamic alloca. No texture of lean2rr's prelude
has such a frame.

**Why it is correct.** Inlining does not change what a program does.
The pass adds the attribute only where LLVM's own checks for this call
pass, the checks of the ordinary inliner, plus its stack limit for
recursive callers (36-b). A texture compiled for other target features is
not forced (LLVM 23 refuses such an `alwaysinline` call anyway:
"conflicting target features"); `noinline` and `cold` textures are left
alone; `alwaysinline` and `noinline` cannot meet on one function. The boundary is `weak_odr`: every definition of it is
equivalent, so inlining this one is the same as calling the one the
linker keeps (the ordinary inliner already inlines it at ordinary call
sites). Both functions stay defined (external and `weak_odr`), so other
modules still link against them.

**Verification.** On the patched Reussir (l2r-inline df9d0677 for 36-a
alone; after the review, 136d9a9f with 36-a, 03-a, 36-b and 03-b), with
lean2rr from deptypes 91fe1e3:

- Lit tests. New `llvmpass/import_trampoline_inline.ll`: which
  trampolines get the attribute (a small texture, a small texture behind
  the packed boundary, a 1024-byte frame: yes; over the threshold,
  `cold`, `noinline`, other target features, a boundary outside the
  module, a 2048-byte frame, no `ret`, a `weak` trampoline: no), and a
  call at a cold site (branch weights 1:2000) inlined after the pass and
  kept without it. New `frontend/ffi_import_inline_recursive.rr` (36-b:
  the 64 KiB texture's trampoline has no `alwaysinline`, and the program
  prints 1). New `frontend/ffi_import_inline_cold.rr` (this entry's
  repro as a test, textures compiled for the native CPU): no call of `mix`
  left at `-O default` and `-O aggressive`; on the unpatched rrc
  (l2r-anybox) the test fails (one call left). The scalar trampoline test
  `conversion/trampoline_import_scalar.mlir` checks the mark. They pass
  on 136d9a9f, with the other tests under `frontend/ffi_*`,
  `frontend/str_ffi*`, `frontend/polyffi*`, `llvmpass/` and
  `conversion/trampoline*` (41 tests).
- `run.sh bug36`: FIXED (both calls of `mix` inlined).
- `tests/runtime/ffi-inline-check.sh`: all nine tests pass, `RtReadsDeep`
  included (unpatched: 7 calls of `l2r_view_take<LAny>`), on df9d0677 and
  on 136d9a9f.
- The 18 classic programs (`tests/classic`, built with `scripts/l2r.py`,
  `tests/oracle.py check --sizes small`): all pass (with 36-a, and with
  36-a and 03-a). Their `.text` with 36-a: the
  total over the 18 programs grows by 0.03% (28,812,744 to 28,820,264
  bytes; per program from -0.25% to +0.56%: the runtime library is most
  of it). The code
  that rrc generates (the functions `_RC*`, `_RIC*` and `__reussir_main`,
  without the `_ffi` copies) grows by 1.26% (2,636,164 to 2,669,296
  bytes; from -14.3% for nqueens to +3.9% for higher-order).
- Instruction counts (cachegrind, `Ir`; builds without SVE for valgrind
  3.22, as the runtime's profiles). "36-a": df9d0677, one run each.
  "final": 136d9a9f (36-a, 03-a, 36-b, 03-b), two runs each, which agree
  to within 600 instructions:

  | program (size) | unpatched | 36-a | final |
  |---|---|---|---|
  | qsort (80) | 98,779,292 (first state); 99,189,806, 99,189,234 (second) | 99,456,384 (+0.69%, first state) | 99,860,378 (+0.68%, second state) |
  | qsort (250) | 3,345,499,847 (first state); 3,349,560,319, 3,349,560,250 (second) | 3,365,996,998 (+0.61%, first state) | 3,370,055,004 (+0.61%, second state) |
  | sieve (1000000) | 501,321,262 | 504,188,952 (+0.57%) | 504,187,897 (+0.57%) |
  | hashmap (10000) | 121,936,564 | 121,918,536 (-0.01%) | - |
  | `RtReadsDeep` | 168,824,113 | 166,918,583 (-1.13%) | 166,910,381 (-1.13%) |

  For qsort each change is against an unpatched run in the same
  page-retire state (below); the second-state unpatched runs are the
  review's. The increases are side effects of the code around the hot
  loops, not work the inlined textures do.
  - qsort, 36-a: the machine code of its hot function (`qsortAux`) is the
    same except for 4 alignment `nop`s before a loop, because the
    function starts 0x70 bytes further on (in the native build, its LLVM
    IR is the same too).
  - qsort, page retire: the unpatched program runs in one of two
    page-retire states from run to run; with 03-a every run takes the
    second one. In the array growth (`leanrt::array::grow`, `mi_realloc`),
    mimalloc's `_mi_page_retire` costs 368,311 instructions in the first
    state and 684,411 in the second at size 80 (8,100,350 and 11,212,956
    at 250); the review's three unpatched runs at size 80 gave 98,779,053
    (first) and 99,189,806 and 99,189,234 (second). The unpatched run and
    the 36-a run of this table fell in the first state. Against an
    unpatched run in the same state, the final build differs only by
    36-a's 4 alignment `nop`s in `qsortAux` (+659,840 at size 80,
    +20,367,000 at 250) and +12,799 in `main`: +0.68% and +0.61%.
  - sieve: `main` gains inlined cold paths (the release of a box,
    `l2r_any_drop_raw`, at 50 sites; `l2r_once_claim` at 5; with 36-a
    alone also the panic texture at 54 sites, which 36-b keeps a call).
    The register allocator then keeps the constant 1 in no register
    across the inner loop: one more instruction per iteration, +2.12
    million; the rest of `main` adds about 0.75 million net. `main`'s
    count is the same with 36-a and with 36-b: the panic texture was not
    the cause.
  - `RtReadsDeep`, whose reads sit at cold call sites, executes 1.1%
    fewer instructions.

**Review.** Round review-inline (local notes `review-inline/`; the
coordinator judged the findings):

- F1 (high, a stack overflow): `alwaysinline` skipped the inliner's stack
  limit for recursive callers (above). Fixed in 36-b (the frame rule), with
  the review's repro as a lit test.
- F2 (low, code size): a texture that cannot return is cold, but a
  `weak_odr` boundary gets no inferred attribute, so the cold check missed
  it (`l2r_internal_panic`, inlined at 54 sites of sieve's `main`). Fixed
  in 36-b (no `ret`, or `noreturn`: not marked). Sieve's count did not
  change (above).
- F3 (hardening): an interposable trampoline is left alone (36-b).
- F4 (documentation): "the decision at cold sites only" and "exactly when
  LLVM would inline it at an ordinary one" were not exact (F1, F2), and the
  sieve explanation lacked the rest of `main`. Corrected above.

A second look at 36-b is pending.

## Upstream note

The trampoline exists only to pack the arguments. A Reussir upstream fix
could give it `alwaysinline` when the texture is small, as 36-a does, or
pass a texture's own inline request through.
