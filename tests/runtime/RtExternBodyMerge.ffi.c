// C side of RtExternBodyMerge.lean's extern, for the native build only
// (tests/runtime/run.sh links NAME.ffi.c natively): it prints what the
// Lean definition's dbgTrace prints and returns `none`.
#include <lean/lean.h>
extern int dprintf(int fd, const char *fmt, ...);
lean_object* rt_ebm_mke(lean_object* n) {
  dprintf(2, "mkE %zu\n", (size_t)lean_unbox(n));
  lean_dec(n);
  return lean_box(0);
}
