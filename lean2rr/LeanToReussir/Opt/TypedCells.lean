import Lean
import LeanToReussir.PassConfig

/-!
# Typed references (optimization `typed-cells`, clean step B2)

The cell of a reference whose element type has a cell kind
(`CellKinds.lean`: a shared record or enum, `Nat`, `Int`, `String`, an
array, `Bool`, `UInt8`, `UInt16`, `UInt32`, `Float32`) holds the element's
own Reussir type, where the whole-program check (`TypedCells.lean`,
`typedRefKinds`, run by `lowerProgram`) allows the kind: no reference of
the kind meets an operation at another representation (an operation at
`lcAny`, a cast), and its values hold nothing whose release the program
can observe. Every other reference keeps its cell of `Box`es (rule 1).
-/

namespace LeanToReussir

/-- Registry entry point (a switch). -/
def Opt.TypedCells.install (c : PassConfig) : PassConfig :=
  { c with typedCells := true }

end LeanToReussir
