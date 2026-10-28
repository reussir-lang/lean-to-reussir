// C side of RtExternBodyComputed.lean's externs, for the native build only
// (tests/runtime/run.sh links NAME.ffi.c natively): each calls the
// @[export] copy of the extern's Lean definition.
#include <lean/lean.h>
lean_object* rt_ebc_mk_ref(lean_object*);
lean_object* rt_ebc_tag_ref(lean_object*);
lean_object* rt_ebc_name_ref(lean_object*);
lean_object* rt_ebc_mk(lean_object* n) { return rt_ebc_mk_ref(n); }
lean_object* rt_ebc_tag(lean_object* x) { return rt_ebc_tag_ref(x); }
lean_object* rt_ebc_name(lean_object* x) { return rt_ebc_name_ref(x); }
