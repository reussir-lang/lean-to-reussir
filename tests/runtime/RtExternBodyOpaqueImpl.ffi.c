// C side of RtExternBodyOpaqueImpl.lean's externs, for the native build
// only (tests/runtime/run.sh links NAME.ffi.c natively): each calls the
// @[export] copy of the extern's Lean definition.
#include <lean/lean.h>
lean_object* rt_eboi_h_ref(lean_object*);
lean_object* rt_eboi_lib_ref(lean_object*);
lean_object* rt_eboi_h(lean_object* n) { return rt_eboi_h_ref(n); }
lean_object* rt_eboi_lib(lean_object* a) { return rt_eboi_lib_ref(a); }
