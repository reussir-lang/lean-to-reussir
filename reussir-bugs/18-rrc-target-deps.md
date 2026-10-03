# 18. The `rrc` build target alone does not link

## Summary

**Kind:** bug (build system). **Status:** patched (0025), applied in
`./reussir` (`l2r-local` 5c0514e3). It affects only Reussir's own build.

**Verdict: bug in Reussir's build system (minor).** The README lists
`cmake --build build --target rrc` as a workflow, and
`lib/CAPI/CMakeLists.txt` keeps an archive list so that what `build.rs`
links is built first. Four archives are missing from it, not one:
`MLIRReussirClosureBetaReduction`, `MLIRReussirDefaultInliner`,
`MLIRReussirInstrumentNonlinearFFI`, `MLIRReussirSpecialPointerTag`.

## Symptom and repro

Repro [`repros/bug18-rrc-target-deps.sh`](repros/bug18-rrc-target-deps.sh)
`REUSSIR_CHECKOUT` checks the cause in an existing build (read-only). The
failure itself needs a fresh build directory:

    cmake -S reussir -B build -G Ninja ...
    cmake --build build --target rrc

**Expected.** rrc builds.

**Actual on ef922049.** cargo fails to link rrc: `could not find native
static library MLIRReussirInstrumentNonlinearFFI`. The check script prints
`REPRODUCES rrc-build does not depend on
libMLIRReussirInstrumentNonlinearFFI.a, which build.rs links`. On the final
stack: `bug 18   FIXED       rrc-build depends on
libMLIRReussirInstrumentNonlinearFFI.a`.

## Cause

`crates/reussir-backend-sys/build.rs` links
`MLIRReussirInstrumentNonlinearFFI` (and three more archives, see the
verdict), but the `rrc-build` custom target
(`crates/reussir-compiler/CMakeLists.txt`) depends only on `ReussirCAPI`
and `MLIRReussir`, which do not pull that library in. The default target
builds every library first. The error names
`MLIRReussirInstrumentNonlinearFFI` only because it is the first of the
four missing archives in `build.rs`'s list; the `rrc-build` edge of
`./reussir/build/build.ninja` depends on none of the four.

## lean2rr

Not affected: lean2rr's tools build Reussir's default target.

## Patch

Patch file
[`patches/0025-l2r-local-bug-18-build-every-archive-build.rs-links-.patch`](patches/0025-l2r-local-bug-18-build-every-archive-build.rs-links-.patch)
(`l2r-local` commit `a3658320`, applied in `./reussir`; `l2r-local` head
`5c0514e3`).

**The change.** The four archives join `REUSSIR_BACKEND_ARCHIVES` in
`lib/CAPI/CMakeLists.txt`, in `build.rs`'s order, and the list's comment
says what it must cover:

```cmake
+# we only ensure they are built first. Every archive in REUSSIR_ARCHIVES of
+# crates/reussir-backend-sys/build.rs must be listed here unless it is a link
+# dependency of ReussirCAPI (...): otherwise building only a cargo target in
+# a fresh build directory (`--target rrc`) does not build it, and cargo
+# cannot link.
 ...
   MLIRReussirCompilePolymorphicFFI
+  MLIRReussirInstrumentNonlinearFFI
   MLIRReussirAttachNativeTarget
   # transformations
+  MLIRReussirClosureBetaReduction
+  MLIRReussirDefaultInliner
   ...
   MLIRReussirTokenReuse
+  MLIRReussirSpecialPointerTag
```

**Why it is correct.** `ReussirCAPI` depends on every archive of the list,
and the cargo targets depend on `ReussirCAPI`, so each archive `build.rs`
links is built before cargo runs. Nothing else changes: the default target
built the four anyway. In the final stack, 0032 adds `MLIRReussirSCCP` to
the same list, as this rule requires (review RV8C-02).

**Verification.** With a fresh build directory and `--target rrc` alone:
before, cargo failed as above; with the patch rrc builds and links, and the
ninja edge of `rrc-build` depends on all four archives (the author's logs,
`~/Documents/l2r-scratch/morepatches-b/build18.build-{before,after}.log`).
`run.sh` on the final stack: `bug 18   FIXED`. No lit test (a build-system
change).

**Review.** Round 7, `p22` (`~/Documents/l2r-scratch/rv7/p22/FINDINGS.txt`):
no defect. All 32 archives in `reussir-backend-sys/build.rs` are direct
dependencies of both the `rrc-build` and `rrepl-build` ninja edges; the
other cargo targets (`reussir-syntax`, `reussir-lsp`, `rene`) do not link
`reussir-backend-sys`. The reviewer accepted the author's fresh-directory
logs instead of a fresh build of its own.

**Effect on lean2rr.** None.

## Upstream note

`crates/reussir-backend-sys/build.rs` links four archives that are neither
in `REUSSIR_BACKEND_ARCHIVES` (`lib/CAPI/CMakeLists.txt`) nor link
dependencies of `ReussirCAPI` (`MLIRReussirInstrumentNonlinearFFI`,
`MLIRReussirClosureBetaReduction`, `MLIRReussirDefaultInliner`,
`MLIRReussirSpecialPointerTag`), so `cmake --build build --target rrc` in a
fresh build directory fails to link. Fix: list them, and keep the list in
step with `build.rs`.
