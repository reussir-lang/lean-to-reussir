// C side of RtExternBytes.lean's own externs, for the native build only
// (tests/runtime/run.sh); each agrees with the Lean definition.
#include <lean/lean.h>

extern lean_object * lean_sarray_ensure_capacity(lean_object * a, size_t min_cap, int exact);

uint32_t rt_bytes_uget_u32le(b_lean_obj_arg a, size_t off) {
    const uint8_t * p = lean_sarray_cptr(a) + off;
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

lean_obj_res rt_bytes_uset_u8x2(lean_obj_arg a, size_t off, uint16_t v) {
    lean_obj_res r = lean_is_exclusive(a) ? a : lean_copy_byte_array(a);
    uint8_t * p = lean_sarray_cptr(r) + off;
    p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8);
    return r;
}

lean_object * rt_bytes_copy_within(lean_object * a, b_lean_obj_arg o_src, b_lean_obj_arg o_len) {
    size_t src = lean_usize_of_nat(o_src), oldsz = lean_sarray_size(a);
    if (src > oldsz) return a;
    size_t len = lean_usize_of_nat(o_len);
    if (len > oldsz - src) len = oldsz - src;
    size_t newsz = oldsz + len;
    lean_object * r = lean_sarray_ensure_capacity(a, newsz, 0);
    if (!lean_is_exclusive(r)) {
        lean_object * c = lean_alloc_sarray(1, oldsz, newsz);
        __builtin_memcpy(lean_sarray_cptr(c), lean_sarray_cptr(r), oldsz);
        lean_dec(r);
        r = c;
    }
    lean_sarray_set_size(r, newsz);
    uint8_t * p = lean_sarray_cptr(r);
    __builtin_memcpy(p + oldsz, p + src, len);
    return r;
}

lean_object * rt_bytes_mk_p(uint8_t x, double y, lean_object * s) {
    lean_object * r = lean_alloc_ctor(0, 1, sizeof(double) + 1);
    lean_object * bang = lean_mk_string("!");
    lean_ctor_set(r, 0, lean_string_append(s, bang));
    lean_dec(bang);
    lean_ctor_set_float(r, sizeof(void *), y * 2);
    lean_ctor_set_uint8(r, sizeof(void *) + sizeof(double), (uint8_t)(x + 1));
    return r;
}

uint8_t rt_bytes_dec_eq(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_nat_dec_eq(a, b); }

lean_object * rt_bytes_fail(uint8_t b) {
    if (b) return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("boom")));
    return lean_io_result_mk_ok(lean_box(7));
}
