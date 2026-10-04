// C side of RtExternNames.lean's own externs, for the native build only.
#include <lean/lean.h>
lean_object * swap(lean_object * p) {
    lean_object * a = lean_ctor_get(p, 0), * b = lean_ctor_get(p, 1);
    lean_inc(a); lean_inc(b); lean_dec(p);
    lean_object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, b); lean_ctor_set(r, 1, a);
    return r;
}
uint64_t hash(uint64_t x) { return x * 31 + 7; }
lean_object * reverse(b_lean_obj_arg s) {
    size_t n = lean_string_size(s) - 1;
    const char * c = lean_string_cstr(s);
    char buf[256];
    for (size_t i = 0; i < n; i++) buf[i] = c[n - 1 - i];
    buf[n] = 0;
    return lean_mk_string(buf);
}
lean_object * ctl_twice(lean_object * n) { lean_object * r = lean_nat_add(n, n); lean_dec(n); return r; }
uint32_t lean_sleep_ms(uint32_t n) { return n > 1000 ? 1000 : n; }
uint32_t gettid(lean_object * u) { return 0; }
