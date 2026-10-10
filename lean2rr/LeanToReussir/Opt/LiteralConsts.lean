import Lean
import LeanToReussir.PassConfig

/-!
# Constants of one string literal read from a cache (optimization `literal-consts`)

Many closed terms that Lean's `extractClosed` makes are one string literal
(the text of a message, of a `toString` or of a panic). Natively such a
closed term is made once and every read shares it. lean2rr gives every
constant a once-cell accessor and an `_init` function (`cafAccessor`). In
50 programs (size survey of 2026-10-10), 2286 of the 5788 pairs were such
constants: 0.97 MB of the 35 MB of `.rr` (2.8%; 11% in L11).

With this pass such a constant (`literalConsts`, Emit/Program) gets no
function, and a read calls the runtime's literal cache:
`l2r_str_lit_cached(id)`, with `id` the literal's index in the program's
literal table (`strLitCached`, LowerBase). The cache has one slot per
literal id (`leanrt::string::lit_ready`): the first read makes the string
and stores it, every read takes a new reference to it. A read allocates
nothing after the first, and its value is never unique, as a once-cell's.
The program computes the same results. Without this pass such a constant is
a once-cell accessor and its `_init`, as any constant.
-/

namespace LeanToReussir

/-- Registry entry point (a switch). -/
def Opt.LiteralConsts.install (c : PassConfig) : PassConfig :=
  { c with literalConsts := true }

end LeanToReussir
