#!/usr/bin/env bash
# Bug 18: building only the `rrc` target in a fresh build directory fails:
#
#   cmake -S REUSSIR -B build -G Ninja ...   # a new build directory
#   cmake --build build --target rrc
#   -> cargo: error: could not find native static library
#      `MLIRReussirInstrumentNonlinearFFI`, perhaps an -L flag is missing?
#
# crates/reussir-backend-sys/build.rs links MLIRReussirInstrumentNonlinearFFI,
# but the rrc-build custom target (crates/reussir-compiler/CMakeLists.txt)
# depends only on ReussirCAPI and MLIRReussir, which do not pull that library
# in. Building the default target works, because it builds every library.
#
#   bug18-rrc-target-deps.sh REUSSIR_CHECKOUT
#
# checks this in an existing build (read-only): it prints REPRODUCES when
# build.rs links the library and build/build.ninja's rrc-build edge does not
# depend on it, FIXED when the edge depends on it.
ck=${1:?usage: bug18-rrc-target-deps.sh REUSSIR_CHECKOUT}
nj=$ck/build/build.ninja
rs=$ck/crates/reussir-backend-sys/build.rs
[ -f "$nj" ] && [ -f "$rs" ] || { echo "SKIPPED no build/build.ninja or build.rs in $ck"; exit 0; }
grep -q '"MLIRReussirInstrumentNonlinearFFI"' "$rs" || { echo "OTHER build.rs no longer links MLIRReussirInstrumentNonlinearFFI"; exit 0; }
if grep '^build crates/reussir-compiler/CMakeFiles/rrc-build ' "$nj" | grep -q 'libMLIRReussirInstrumentNonlinearFFI\.a'; then
    echo "FIXED rrc-build depends on libMLIRReussirInstrumentNonlinearFFI.a"
else
    echo "REPRODUCES rrc-build does not depend on libMLIRReussirInstrumentNonlinearFFI.a, which build.rs links"
fi
