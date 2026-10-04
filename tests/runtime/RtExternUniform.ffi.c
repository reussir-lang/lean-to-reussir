// C side of RtExternUniform.lean's own externs, for the native build only.
#include <lean/lean.h>
lean_object * rt_uniform_push_twice(lean_object * a, lean_object * v) {
    lean_inc(v);
    a = lean_array_push(a, v);
    return lean_array_push(a, v);
}
lean_object * rt_uniform_restart(lean_object * a) {
    lean_dec(a);
    return lean_mk_empty_array();
}
