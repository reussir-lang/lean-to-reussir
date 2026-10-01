import Lean
import LeanToReussir.PassConfig

/-!
# Number printing by the runtime (optimization `prelude-repr`)

`Nat.repr` and `Int.repr` are Lean code. For a big number they divide by 10
digit by digit (quadratic time), and `Nat.reprFast`, Lean's implementation
of `Nat.repr`, clones the `Nat.reprArray` once-cell and drops it out of
line for every number ≥ 128 (13% of the Sieve benchmark). The prelude's
`l2r_nat_repr`/`l2r_int_repr` give the same strings with GMP (runtime
requests 12 and 27). Without this pass the Lean code is translated like any
other.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Registry entry point. -/
def Opt.PreludeRepr.install (c : PassConfig) : PassConfig :=
  { c with preludeReplacements := c.preludeReplacements
      |>.insert ``Nat.repr ("l2r_nat_repr", .named "Nat")
      |>.insert ``Nat.reprFast ("l2r_nat_repr", .named "Nat")
      |>.insert ``Int.repr ("l2r_int_repr", .named "Int") }

end LeanToReussir
