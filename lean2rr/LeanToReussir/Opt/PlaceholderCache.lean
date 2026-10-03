import Lean
import LeanToReussir.PassConfig

/-!
# Placeholders built once (optimization `placeholder-cache`)

Lean passes `box(0)` for values that are never inspected; lean2rr builds
the expected type's zero there (`zeroValue`, translation plan §5.1). A
placeholder that would allocate (a string, an array, a record, a reference,
a boxed unit) is built once and kept in a once-cell like a constant (a
function value's placeholder is the nullary `z`, which allocates nothing):
`Array.modify` stores one per update, and it is never inspected, so a
shared value does as well as a fresh one. Without this pass each
placeholder is built where it is used.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Registry entry point (a switch). -/
def Opt.PlaceholderCache.install (c : PassConfig) : PassConfig :=
  { c with cachePlaceholders := true }

end LeanToReussir
