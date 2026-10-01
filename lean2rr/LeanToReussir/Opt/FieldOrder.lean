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

/-- The field indices of `order` (a record order) sorted by decreasing
alignment, ties in `order`'s order. -/
def alignmentOrder (order : Array Nat) (aligns : Array Nat) : Array Nat :=
  let rank : Std.HashMap Nat Nat := order.zipIdx.foldl (fun m (i, r) => m.insert i r) {}
  order.qsort fun i j =>
    aligns[i]! > aligns[j]! || (aligns[i]! == aligns[j]! && rank.getD i 0 < rank.getD j 0)

/-- Registry entry point: the order of the hooks installed before, sorted by
alignment. -/
def Opt.FieldOrder.install (c : PassConfig) : PassConfig :=
  let prev := c.fieldOrder
  { c with fieldOrder := fun aligns => alignmentOrder (prev aligns) aligns }

end LeanToReussir
