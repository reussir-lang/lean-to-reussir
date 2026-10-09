// C implementations of RtCArrExtern.lean's externs, for the native build
// (tests/runtime/run.sh links NAME.ffi.c natively); each does what the Lean
// body does. (`checksum`'s symbol is the `@[export]` of `checksumImpl`.)
#include <lean/lean.h>

uint32_t rt_carr_uget_u32le(b_lean_obj_arg a, size_t off) {
    uint8_t * p = lean_sarray_cptr(a) + off;
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

lean_object * rt_carr_presize(b_lean_obj_arg n) {
    size_t k = lean_unbox(n);
    lean_object * r = lean_alloc_sarray(1, k, k);
    uint8_t * p = lean_sarray_cptr(r);
    for (size_t i = 0; i < k; i++) p[i] = 0;
    return r;
}

lean_object * rt_carr_bump(lean_object * a, uint8_t k) {
    size_t n = lean_array_size(a);
    lean_object * r = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) {
        uint8_t v = (uint8_t)lean_unbox(lean_array_get_core(a, i));
        lean_array_set_core(r, i, lean_box((uint8_t)(v + k)));
    }
    lean_dec(a);
    return r;
}

lean_object * rt_carr_words(b_lean_obj_arg a) {
    size_t n = lean_sarray_size(a) / 8;
    uint8_t * p = lean_sarray_cptr(a);
    lean_object * r = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++) {
        uint64_t w = 0;
        for (size_t j = 0; j < 8; j++) w |= (uint64_t)p[8 * i + j] << (8 * j);
        lean_array_set_core(r, i, lean_box_uint64(w));
    }
    return r;
}

lean_object * rt_carr_scale(b_lean_obj_arg a, double f) {
    size_t n = lean_array_size(a);
    lean_object * r = lean_alloc_array(n, n);
    for (size_t i = 0; i < n; i++)
        lean_array_set_core(r, i, lean_box_float(lean_unbox_float(lean_array_get_core(a, i)) * f));
    return r;
}
