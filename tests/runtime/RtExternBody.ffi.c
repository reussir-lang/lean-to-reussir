// C implementations of RtExternBody.lean's externs, for the native build
// (tests/runtime/run.sh links NAME.ffi.c natively); each does what the Lean
// body does.
#include <lean/lean.h>

lean_object * my_custom_double(lean_object * n) {
    lean_object * r = lean_nat_add(n, n);
    lean_dec(n);
    return r;
}

static lean_object * fib_go(size_t n) {
    lean_object * a = lean_box(0), * b = lean_box(1);
    for (size_t i = 0; i < n; i++) {
        lean_object * c = lean_nat_add(a, b);
        lean_dec(a);
        a = b;
        b = c;
    }
    lean_dec(b);
    return a;
}

lean_object * my_fib(lean_object * n) {
    size_t k = lean_unbox(n);
    return fib_go(k);
}

lean_object * my_log2(lean_object * n) {
    size_t k = lean_unbox(n), r = 0;
    while (k >= 2) { k /= 2; r++; }
    return lean_box(r);
}

lean_object * my_collatz(lean_object * n, lean_object * steps) {
    size_t k = lean_unbox(n), s = lean_unbox(steps);
    while (k > 1) { k = (k % 2 == 0) ? k / 2 : 3 * k + 1; s++; }
    return lean_box(s);
}

lean_object * my_swap(lean_object * p) {
    lean_object * a = lean_ctor_get(p, 0), * b = lean_ctor_get(p, 1);
    lean_inc(a); lean_inc(b); lean_dec(p);
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, b);
    lean_ctor_set(r, 1, a);
    return r;
}

uint64_t my_mix(uint64_t a, uint64_t b) { return a * 31 + b; }

lean_object * my_greet(b_lean_obj_arg name) {
    lean_object * s = lean_mk_string("hello, ");
    return lean_string_append(s, name);
}

lean_object * my_count(lean_object * r, lean_object * k) {
    lean_object * v = lean_st_ref_get(r);
    lean_object * v2 = lean_nat_add(v, k);
    lean_dec(v); lean_dec(k);
    lean_inc(v2);
    lean_st_ref_set(r, v2);
    lean_dec(r);
    return lean_io_result_mk_ok(v2);
}
