import Lean
import LeanToReussir.PassConfig

/-!
# One-word `Nat`/`Int` arrays (optimization `nat-arrays`)

`Array Nat` and `Array Int` are the runtime's `LNatArr`/`LIntArr`: the
elements' own words (a small value `2n+1`, or a big number's pointer) in
one allocation per array, like Lean's array object (translation plan §5.1;
runtime request 11). The lowering reaches them through the array
representation (`arrayRepr?`, family `natarr`/`intarr`) and the runtime
functions named after the C symbols (`natArrSym?`). Without this pass they
are arrays like the others (`RVec<Nat>`/`RVec<Int>`, also one word per
element, in two allocations), and the runtime keeps the `LNatArr`
functions, unused.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Registry entry point (a switch). -/
def Opt.NatArrays.install (c : PassConfig) : PassConfig :=
  { c with natArrays := true }

end LeanToReussir
