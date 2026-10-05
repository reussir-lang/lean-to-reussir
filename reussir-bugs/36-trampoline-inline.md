# 36. A texture's import trampoline has no inline attribute

**Kind:** missed optimization. Not a bug: rrc's output is correct. Not
patched: lean2rr keeps the textures that matter small enough.

## Summary

**Kind:** missed optimization. **Status:** worked around (lean2rr's read
textures are small, perf-array-reads); documented only, no patch.

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

Keeps the textures of reads small: each costs less than 45 once the
`_ffi` function is inlined into its trampoline (the runtime's other hot
textures are small for the same reason;
`tests/runtime/ffi-inline-check.sh` fails on a texture called through the
packed-argument boundary). No patch: an `alwaysinline` on every
trampoline would also inline lean2rr's large textures (the string rules,
formatting) at every call site, a code-size decision rather than a fix;
an inline hint copied from the texture would need rrc to read the
texture's attributes, which it does not see before linking the bitcode.

## Upstream note

The trampoline could carry `inlinehint` (or `alwaysinline` when the
texture asks for it): it exists only to pack the arguments.
