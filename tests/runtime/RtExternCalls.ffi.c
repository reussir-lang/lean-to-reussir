// C side of RtExternCalls.lean's own externs, for the native build only;
// each does what the Lean definition does.
#include <lean/lean.h>
static lean_object * add_small(lean_object * n, size_t k) {
    lean_object * r = lean_nat_add(n, lean_box(k));
    lean_dec(n);
    return r;
}
lean_object * rt_calls_inc(lean_object * n) { return add_small(n, 1); }
lean_object * rt_calls_inc_twice(lean_object * n) { return add_small(n, 2); }
lean_object * rt_calls_apply_all(lean_object * fs, lean_object * n) {
    lean_object * l = fs;
    while (!lean_is_scalar(l)) {
        lean_object * f = lean_ctor_get(l, 0);
        lean_inc(f);
        n = lean_apply_1(f, n);
        l = lean_ctor_get(l, 1);
    }
    lean_dec(fs);
    return n;
}
lean_object * rt_calls_sum(b_lean_obj_arg xs) {
    lean_object * acc = lean_box(0);
    while (!lean_is_scalar(xs)) {
        lean_object * s = lean_nat_add(acc, lean_ctor_get(xs, 0));
        lean_dec(acc);
        acc = s;
        xs = lean_ctor_get(xs, 1);
    }
    return acc;
}
lean_object * rt_calls_tri_sum(lean_object * xs) {
    lean_object * s = rt_calls_sum(xs);
    lean_dec(xs);
    lean_object * r = lean_nat_mul(s, lean_box(3));
    lean_dec(s);
    return r;
}
lean_object * rt_calls_target(lean_object * n) {
    lean_object * r = lean_nat_mul(n, lean_box(5));
    lean_dec(n);
    return r;
}
lean_object * rt_calls_via_spec(lean_object * n) {
    lean_object * r = lean_nat_mul(n, lean_box(6));
    lean_dec(n);
    return add_small(r, 1);
}
