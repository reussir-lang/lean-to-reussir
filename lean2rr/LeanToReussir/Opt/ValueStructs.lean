import Lean
import LeanToReussir.PassConfig

/-!
# One-field structures passed by value (optimization `value-structs`)

A structure with a single relevant field (after dropping irrelevant ones:
`ST.Out`, the result of every `BaseIO` call, once the world is gone) is a
`[value]` struct: passed by value, no heap cell per value (translation plan
§5.1). The type translation (`nominalType`) makes the choice; the rest of
the lowering follows the type's `TypeInfo.value` (conversions, identity,
references and array storage treat such a struct as its field). Without
this pass such a structure is a shared record like any other.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Registry entry point. -/
def Opt.ValueStructs.install (c : PassConfig) : PassConfig :=
  { c with valueStructs := true }

end LeanToReussir
