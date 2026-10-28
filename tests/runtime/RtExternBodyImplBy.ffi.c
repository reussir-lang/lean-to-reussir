// C side of RtExternBodyImplBy.lean's externs, for the native build only
// (tests/runtime/run.sh links NAME.ffi.c natively): each calls the
// @[export] copy of the extern's Lean definition, or does what it does.
#include <lean/lean.h>
lean_object* rt_eib_ref(lean_object*);
lean_object* rt_eib_ref_map(lean_object*);
lean_object* rt_eib_ref_g(lean_object*);
lean_object* rt_eib_ref_mapm(lean_object*);
lean_object* rt_eib_ext(lean_object* n) { return rt_eib_ref(n); }
lean_object* rt_eib_ext_map(lean_object* xs) { return rt_eib_ref_map(xs); }
lean_object* rt_eib_ext_g(lean_object* xs) { return rt_eib_ref_g(xs); }
lean_object* rt_eib_mapm(lean_object* a) { return rt_eib_ref_mapm(a); }
lean_object* rt_eib_pick(uint8_t b, lean_object* x, lean_object* y) {
  if (b) { lean_dec(x); return y; } else { lean_dec(y); return x; }
}
lean_object* rt_eib_sum(lean_object* add, lean_object* zero, b_lean_obj_arg xs) {
  lean_object* acc = zero;
  lean_object* p = xs;
  while (!lean_is_scalar(p)) {
    lean_object* h = lean_ctor_get(p, 0); lean_inc(h);
    lean_inc(add);
    acc = lean_apply_2(add, acc, h);
    p = lean_ctor_get(p, 1);
  }
  lean_dec(add);
  return acc;
}
