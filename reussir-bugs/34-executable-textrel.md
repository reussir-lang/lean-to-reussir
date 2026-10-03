# 34. `rrc --emit executable` links static code into a PIE (text relocations)

## Summary

**Kind:** bug (link). **Status:** patched (0065), not applied yet (branch
`l2r-final-0065` of `~/Documents/l2r-scratch/reussir-final`, on
`l2r-final` cc8e5aa5); review pending. lean2rr has no workaround yet (its
driver could pass `--relocation-mode pic`, below).

**Verdict: bug.** `rrc --emit executable` (and `--emit dynlib`) links
through rustc, whose products are a position-independent executable (PIE)
and a shared object. But the code it links is compiled with rrc's default
`--relocation-mode default`, which hands LLVM its own default relocation
model, static on ELF. Static code may address data absolutely, which a PIE
cannot do without patching its read-only segment at load time. Reussir
knows this: every executable build in its own tests passes
`--relocation-mode pic`, and `rene` passes `pic` unless a profile says
otherwise ("shared objects and position-independent executables need
it", `crates/rene/src/manifest.rs`). rrc's own default did not follow.

- On aarch64 (this machine), with GNU ld, the default linker: the link
  succeeds and the executable gets `DT_TEXTREL`. The dynamic loader makes
  the text segment writable at start-up to apply the relocations, then
  read-only again. Every lean2rr program has it: LeanBoolLoop has 92
  relocations into its read-only segment, MapMIO 106. That is a load-time
  cost, it breaks W^X during start-up, and hardened systems refuse it
  (SELinux `execmod`, loaders built without text relocation support).
- On aarch64 with lld (`-fuse-ld=lld`): the link fails, "relocation
  R_AARCH64_ABS64 cannot be used against local symbol; recompile with
  -fPIC". lld does not create text relocations by default.
- On x86-64: static code also holds 32-bit absolute addresses in the
  instructions (`R_X86_64_32`), which no linker can put into a PIE. lld
  rejects the object ("relocation R_X86_64_32 cannot be used against
  local symbol"); GNU ld rejects such relocations in a PIE as well (not
  tried here: the machine has no x86-64 sysroot). rustc uses lld by
  default on x86_64-unknown-linux-gnu, so an executable built this way
  should not link there at all.

## Symptom and repro

Repro [`repros/bug34-executable-textrel.rr`](repros/bug34-executable-textrel.rr):
two closures, one chosen at run time and called through `ap`, so the
program keeps a closure vtable (a constant table of code addresses). It
prints 6.

**Command.** `rrc bug34-executable-textrel.rr -o OUT --emit executable -O aggressive`
(no `--relocation-mode`, as lean2rr's `scripts/l2r.py` calls rrc), then
`readelf -d OUT`.

**Expected.** No `TEXTREL` in the dynamic section; prints 6.

**Actual on ef922049** (and on the final stack cc8e5aa5), aarch64:

| build | link | `TEXTREL` |
|---|---|---|
| default mode, GNU ld (the default) | ok, prints 6 | yes |
| default mode, lld (`--linker clang --link-arg=-fuse-ld=lld`) | fails: "relocation R_AARCH64_ABS64 cannot be used against local symbol; recompile with -fPIC" | - |
| `--relocation-mode pic`, GNU ld | ok, prints 6 | no |
| `--relocation-mode pic`, lld | ok, prints 6 | no |

`run.sh` prints `bug 34   REPRODUCES  the executable needs text
relocations (DT_TEXTREL); prints 6` on the unpatched build.

The object file shows why (`readelf -SW`, `readelf -rW` of `rrc ... -o x.o`):
with the default mode the vtable is in `.rodata` (flags `A`, read-only)
with six `R_AARCH64_ABS64` relocations against `.text`; with
`--relocation-mode pic` the same table is in `.data.rel.ro` (flags `WA`,
written by the loader before RELRO makes it read-only), with the same
relocations. Compiled for x86-64 (`--target-triple
x86_64-unknown-linux-gnu`), the default-mode object also has six
`R_X86_64_32` relocations in `.text` (the vtable's address loaded as a
32-bit immediate); the PIC object has none.

## Cause

`crates/reussir-compiler/src/driver/cli.rs` declares
`--relocation-mode` with `default_value = "default"`, and
`crates/reussir-compiler/src/lib.rs` maps it to `LLVMRelocDefault`. For an
ELF target LLVM's effective default is `Reloc::Static`. Under the static
model LLVM puts a constant that contains addresses (the closure vtable,
`reussir.closure.vtable` lowered to an LLVM constant global) into
`.rodata`, since no relocation remains after a static link, and on x86-64
it materializes addresses with 32-bit absolute immediates.

The link step (`crates/reussir-compiler/src/driver/link.rs`,
`link_product`) then hands the objects to rustc, which links a PIE (the
default of rustc's Linux targets) or a `cdylib`. Nothing connects the two
choices: the relocation mode is not derived from the product.

## lean2rr

lean2rr's driver (`scripts/l2r.py`) calls `rrc --emit executable` without
`--relocation-mode`, so every lean2rr program is affected: on this
machine every binary carries `DT_TEXTREL` (it still runs); with lld, or on
x86-64, lean2rr's programs would not link. A one-line lean2rr workaround,
independent of the patch: pass `--relocation-mode pic` in `l2r.py` (not
made yet).

## Patch

Patch file
[`patches/0065-l2r-local-bug-34-compile-link-products-position-inde.patch`](patches/0065-l2r-local-bug-34-compile-link-products-position-inde.patch)
(commit `c8a524e7` on branch `l2r-final-0065` of
`~/Documents/l2r-scratch/reussir-final`, on cc8e5aa5; not in `./reussir`
yet). When the mode is left at `default` and the product is an executable
or a dynlib, rrc compiles position-independent code
(`crates/reussir-compiler/src/driver.rs`):

```rust
    let reloc = match parse_reloc(&cli.relocation_mode)? {
        RelocMode::Default if matches!(target, Stage::Executable | Stage::Dynlib) => {
            RelocMode::Pic
        }
        mode => mode,
    };
```

The `--relocation-mode` help says so. An explicit mode is kept (`static`
still builds the TEXTREL executable if asked), and outputs that are not
linked by rrc (objects, archives, IR) keep LLVM's default, as before.

**Why it is correct.** It makes rrc compile its link products the way
rustc compiles the code it links into them (PIC), and the way `rene` and
Reussir's own tests already build them. The vtable moves to
`.data.rel.ro`, relocated at load time like any PIE's, and `.text` carries
no relocations.

**Verification.**

- New test `codegen/executable_pic_default.rr`: a closure vtable at
  `-O none`, built without `--relocation-mode`; `llvm-readobj
  --dynamic-table` shows no `TEXTREL` (the unpatched rrc's executable has
  `TEXTREL` there). Reussir's lit suite on the patched stack: 648 tests,
  567 passed, 81 unsupported, none failed.
- The repro: without `--relocation-mode`, GNU ld and lld both link it,
  no `TEXTREL`, prints 6; with `--relocation-mode static`, still
  `TEXTREL` (the explicit mode kept). `run.sh`: `bug 34   FIXED       no
  text relocations; prints 6`.
- lean2rr: LeanBoolLoop built through `l2r.py` against the patched rrc
  prints 25009648 (as native) and has no `TEXTREL` (0 relocations into
  read-only segments instead of 92). Its `.text` grows 1.3% (937,340 ->
  949,404 bytes; PIC code reaches some symbols through the GOT). Run time
  was not measured (a benchmark needs the user's go-ahead).

**Review.** Pending.

**Effect on lean2rr.** Its programs link without text relocations, with
GNU ld or lld; x86-64 builds become possible. The code is
position-independent, as rustc's own code in the same executable already
is.

## Upstream note

`rrc --emit executable`/`dynlib` link a PIE or a shared object through
rustc, but `--relocation-mode` defaults to LLVM's default (static on ELF),
so closure vtables land in `.rodata` with absolute relocations: GNU ld on
aarch64 adds `DT_TEXTREL`, lld refuses, and on x86-64 the `R_X86_64_32`
relocations cannot link into a PIE. `rene` and the tests pass
`--relocation-mode pic`; making `default` mean `pic` for linked products
fixes rrc itself.
