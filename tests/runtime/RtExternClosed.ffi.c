// C side of RtExternClosed.lean's own externs, for the native build only.
#include <lean/lean.h>
lean_object * rt_closed_table(lean_object * n) {
    size_t k = lean_unbox(n);
    lean_object * a = lean_mk_empty_array();
    for (size_t i = 0; i < k; i++) a = lean_array_push(a, lean_box(i * 7 % 11));
    return a;
}
uint64_t rt_closed_seed(uint64_t n) { return n * 6364136223846793005ULL + 1442695040888963407ULL; }
lean_object * rt_closed_greet(lean_object * u) { return lean_mk_string("hi"); }
lean_object * rt_closed_scale(lean_object * k, lean_object * n) {
    lean_object * r = lean_nat_mul(k, n);
    lean_dec(k); lean_dec(n);
    return r;
}
