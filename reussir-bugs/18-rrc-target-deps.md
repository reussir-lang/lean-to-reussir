# 18. The `rrc` build target alone does not link

## Summary

**Kind:** bug (build system). **Status:** worked around (build the default
target); it affects only Reussir's own build. No patch yet.

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
libMLIRReussirInstrumentNonlinearFFI.a, which build.rs links`.

## Cause

`crates/reussir-backend-sys/build.rs` links
`MLIRReussirInstrumentNonlinearFFI` (and three more archives, see the
verdict), but the `rrc-build` custom target
(`crates/reussir-compiler/CMakeLists.txt`) depends only on `ReussirCAPI`
and `MLIRReussir`, which do not pull that library in. The default target
builds every library first.

## lean2rr

Build Reussir's default target.
