import Lean
import LeanToReussir.PassConfig

/-!
# Record fields by decreasing alignment (optimization `field-order`)

Each constructor's relevant fields are placed in its record in decreasing
alignment, ties in declaration order (translation plan §5.1), so a record
has no padding between members. The driver turns Reussir's own member
packing off (`--no-pack-record-members`, the workaround for Reussir bug 2),
so lean2rr's order is the layout; the type translation maps each Lean field
to its record position, and constructions, patterns, projections and
conversions go through that map. Without this pass the fields stay in
declaration order, with padding where alignment needs it (Reussir lays
padding out as bytes, also after a one-field `[value]` member).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Field indices in decreasing alignment, ties in declaration order. -/
def alignmentOrder (aligns : Array Nat) : Array Nat :=
  (List.range aligns.size).toArray.qsort fun i j =>
    aligns[i]! > aligns[j]! || (aligns[i]! == aligns[j]! && i < j)

/-- Registry entry point. -/
def Opt.FieldOrder.install (c : PassConfig) : PassConfig :=
  { c with fieldOrder := alignmentOrder }

end LeanToReussir
