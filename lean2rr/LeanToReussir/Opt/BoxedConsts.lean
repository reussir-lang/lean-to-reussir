import Lean
import LeanToReussir.PassConfig

/-!
# Constants boxed once (optimization `boxed-consts`)

Native Lean boxes a constant of a scalar type (a literal, or a declaration
without parameters: a constant or closed term) once: its boxing pass
(`ExplicitBoxing`, `isExpensiveConstantValueBoxing`) makes an auxiliary
constant `_boxed_const_N` that holds the boxed value. lean2rr does the
same where boxing allocates (`boxAllocates`: a `Float`, a `UInt64` from
2^63, a negative `i64`, a `[value]` struct of one, an `ElemBox`): the
box is built once and kept in a once-cell like a constant (`boxOf`,
`boxedConst`). The default of `a[i]!` on an `Array Float` is
`instInhabitedFloat`, a constant: without the pass every read allocated a
16-byte cell for it. A constant is pure, so one box does as well as a new
one at each use. Without this pass the box is built where it is used.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Registry entry point (a switch). -/
def Opt.BoxedConsts.install (c : PassConfig) : PassConfig :=
  { c with boxedConsts := true }

end LeanToReussir
