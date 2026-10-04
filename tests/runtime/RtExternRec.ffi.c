// C side of RtExternRec.lean's own externs, for the native build only.
#include <lean/lean.h>
uint8_t rc_even(lean_object * n) { size_t k = lean_unbox(n); return k % 2 == 0; }
lean_object * rc_digits(lean_object * n) {
    size_t k = lean_unbox(n);
    lean_object * acc = lean_box(0);
    do {
        lean_object * c = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(c, 0, lean_box(k % 10)); lean_ctor_set(c, 1, acc); acc = c; k /= 10;
    } while (k > 0);
    return acc;
}
lean_object * rc_search(lean_object * n) {
    size_t k = lean_unbox(n);
    while (k * k <= 50) k++;
    lean_object * r = lean_alloc_ctor(1, 1, 0); lean_ctor_set(r, 0, lean_box(k)); return r;
}
lean_object * rc_sumto(lean_object * n) { size_t k = lean_unbox(n); return lean_box(k * (k + 1) / 2); }
lean_object * rc_gsum(lean_object * add, lean_object * zero, b_lean_obj_arg xs) {
    lean_object * acc = zero;
    while (!lean_is_scalar(xs)) {
        lean_object * h = lean_ctor_get(xs, 0); lean_inc(h); lean_inc(add);
        acc = lean_apply_2(add, acc, h);
        xs = lean_ctor_get(xs, 1);
    }
    lean_dec(add);
    return acc;
}
lean_object * rc_chain(lean_object * n) { size_t k = lean_unbox(n); return lean_box(k * (k + 1) / 2 + (k % 2 == 0)); }
static size_t ack(size_t m, size_t n) { if (m == 0) return n + 1; if (n == 0) return ack(m - 1, 1); return ack(m - 1, ack(m, n - 1)); }
lean_object * rc_ack(lean_object * m, lean_object * n) { return lean_box(ack(lean_unbox(m), lean_unbox(n))); }
