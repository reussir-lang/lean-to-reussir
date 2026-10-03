#!/usr/bin/env bash
# Bug 24: the matrix-exponentiation pass (LinearRecurrenceMatExpPass,
# lib/LLVMPass/LinearRecurrence/LinearRecurrenceMatExp.cpp) emits a different
# module from run to run for the same input. It collects a loop's state PHIs
# by iterating a DenseMap keyed by PHINode pointers (`AffineExpr::coeffs`),
# so the order of the state, which is the row and column order of the
# companion matrix and of the emitted code, follows heap addresses. The
# modules are equivalent; the build is not reproducible.
#
#   bug24-matexp-state-order.sh REUSSIR_CHECKOUT [RUNS]
#
# runs the checkout's build/bin/reussir-llvm-opt RUNS times (default 12) on
# its own test tests/integration/llvmpass/linear_recurrence_order6_e2e.ll (an
# order-6 linear recurrence) through the O2 linear-recurrence pipeline and
# counts the distinct outputs: FIXED for one, REPRODUCES for more.
# Expected: 1 output. Reussir ef922049: 10 distinct outputs in 12 runs
# (address-space randomization changes the heap addresses between runs).
ck=${1:?usage: bug24-matexp-state-order.sh REUSSIR_CHECKOUT [RUNS]}
runs=${2:-12}
opt=$ck/build/bin/reussir-llvm-opt
in=$ck/tests/integration/llvmpass/linear_recurrence_order6_e2e.ll
[ -x "$opt" ] && [ -f "$in" ] || { echo "SKIPPED no build/bin/reussir-llvm-opt or $in"; exit 0; }
d=$(mktemp -d /tmp/bug24.XXXXXX)
for i in $(seq "$runs"); do
    "$opt" --linear-recurrence-pipeline=O2 "$in" -o "$d/$i.ll" 2> "$d/$i.log" \
        || { echo "OTHER reussir-llvm-opt failed: $(head -c 200 "$d/$i.log")"; rm -rf "$d"; exit 0; }
done
n=$(md5sum "$d"/*.ll | cut -d' ' -f1 | sort -u | wc -l)
rm -rf "$d"
if [ "$n" = 1 ]; then echo "FIXED $runs runs of the order-6 recurrence: 1 output"
else echo "REPRODUCES $runs runs of the order-6 recurrence: $n different outputs"; fi
