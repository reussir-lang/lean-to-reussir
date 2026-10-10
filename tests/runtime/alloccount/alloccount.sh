# Sourced by the checks that count allocations (tests/runtime/alloc-check.sh,
# tests/runtime/paynothing-check.sh): builds the counter (alloccount.c) and
# defines the link flags of both builds (mimalloc's and the C library's
# allocation entry points, see alloccount.c).
#   alloccount_setup DIR   compiles DIR/alloccount.o with Lean's C compiler
#                          (leanc) and sets
#     AC_LEANC   the extra arguments of the native link (`leanc ... $AC_LEANC`)
#     AC_RRC     the extra rrc flags of the lean2rr build, for L2R_RRC_FLAGS
#                (scripts/l2r.py passes them to rrc, which passes each
#                `--link-arg` to the linker)
#   alloccount_read FILE   prints the allocations and the bytes counted in a
#                          run's stderr, "ALLOCS BYTES" (empty when the
#                          counter printed nothing)
#   alloccount_strip FILE  prints the file without the counter's line
ALLOCCOUNT_SRC=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/alloccount.c
ALLOCCOUNT_SYMS="mi_malloc mi_malloc_small mi_zalloc mi_zalloc_small mi_calloc mi_malloc_aligned mi_zalloc_aligned mi_mallocn mi_realloc mi_realloc_aligned malloc calloc realloc posix_memalign aligned_alloc"

alloccount_setup() {
  local dir=$1 wrap="-Wl" s
  for s in $ALLOCCOUNT_SYMS; do wrap="$wrap,--wrap=$s"; done
  leanc -O2 -c "$ALLOCCOUNT_SRC" -o "$dir/alloccount.o" || return 1
  AC_LEANC="$wrap $dir/alloccount.o"
  AC_RRC="--link-arg=$wrap --link-arg=$dir/alloccount.o"
}

alloccount_read() {
  sed -nE 's/^alloccount: allocs ([0-9]+) reallocs [0-9]+ bytes ([0-9]+)$/\1 \2/p' "$1" | tail -1
}

alloccount_strip() {
  grep -v '^alloccount: allocs [0-9]* reallocs [0-9]* bytes [0-9]*$' "$1" || true
}
