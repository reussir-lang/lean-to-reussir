// C side of RtExternCsimp.lean's own externs, for the native build only.
#include <lean/lean.h>
uint64_t rt_csimp_ctz64(uint64_t x) { return x == 0 ? 64 : (uint64_t)__builtin_ctzll(x); }
lean_object * rt_csimp_dbl(lean_object * n) {
    lean_object * r = lean_nat_add(n, n);
    lean_dec(n);
    return r;
}
uint64_t rt_csimp_low_bit(uint64_t x) { return x == 0 ? 0 : x & (~x + 1); }
