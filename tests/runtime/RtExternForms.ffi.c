// C side of RtExternForms.lean's own externs, for the native build only.
#include <lean/lean.h>
lean_object * rt_forms_slow(lean_object * n) { return lean_box(lean_unbox(n) + 1); }
lean_object * rt_forms_target(lean_object * n) { return lean_box(lean_unbox(n) * 3); }
uint32_t rt_forms_c(uint32_t n) { return n + 5; }
