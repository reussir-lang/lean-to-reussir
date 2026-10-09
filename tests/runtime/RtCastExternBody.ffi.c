// C implementation of RtCastExternBody.lean's extern, for the native build
// (tests/runtime/run.sh links NAME.ffi.c natively): a boxed `UInt64` and a
// boxed `Float` are both an object with one 8-byte scalar field, so the
// words' boxes are read as floats by their bits, as the Lean body's
// `cast` does.
#include <lean/lean.h>

double rt_cast_sum_as_floats(b_lean_obj_arg a, size_t i, double acc) {
    size_t n = lean_array_size(a);
    for (; i < n; i++) acc += lean_unbox_float(lean_array_get_core(a, i));
    return acc;
}
