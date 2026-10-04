// C side of RtExternFold.lean's own extern, for the native build.
#include <lean/lean.h>

lean_object * rt_fold_shl(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_nat_shiftl(a, b);
}
