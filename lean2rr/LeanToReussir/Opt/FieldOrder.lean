import Lean
import LeanToReussir.PassConfig

/-!
# Record fields by decreasing alignment (optimization `field-order`)

Each constructor's relevant fields are placed in its record in decreasing
alignment, ties in declaration order (translation plan §5.1), so a record
has no padding between members. A field's alignment is the one Reussir
gives the member (`fieldAlign` in LowerBase, `RR.fieldAlign?`): a `[value]`
struct is laid out in place, with the largest alignment of its fields
(`struct [value] W(u8)`: 1, so it goes after the 8-byte fields). Every tuple lean2rr generates (`tupleType`:
a join point's arguments, J2; a `flatten-structs` result) uses the same
order, through the same helper (`memberOrder`). The driver turns Reussir's
own member packing off (`--no-pack-record-members`, the workaround for a
Reussir bug fixed upstream in Reussir #656), so lean2rr's order is the
layout; the type translation maps each Lean field to its record position,
and constructions, patterns, projections and conversions go through that
map (a tuple's through its order, `tupleOrders`). Without this pass the
fields stay in declaration order, with padding where alignment needs it
(Reussir lays padding out as bytes, also after a one-field `[value]`
member).
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
