import LeanToReussir.PassConfig
import LeanToReussir.TypedToMono

/-!
# Matches on Reussir's built-in integers (optimization `int-match`)

A `Nat` or `Int` is Reussir's built-in integer, and Reussir has matches
on it: `Nat` as `Zero | Succ`, `Int` as `OfNat | NegSucc`, literal arms
among them, compiled to one `rcgmp.match` over integer intervals (an
immediate's tagged bits select the arm; an arm's binder is the scrutinee
minus the arm's bound, computed in the selection). Lean's `toMono` turns
a `cases` on a `Nat` into `Nat.decEq n 0` and `Nat.sub n 1`, and one on an
`Int` into `Int.decLt` and `Int.natAbs`; with this pass Stage 2 keeps them
(`toMonoK`'s `keepIntCases`), so Lean's mono passes and lean2rr's see a
`cases` on `Nat` or `Int`, and the lowering makes it a `match`
(Lower/IntMatch). It also turns a chain of tests of one `Nat` or `Int`
against literals (Lean's `match n with | 0 => … | 5 => … | _ => …`, which
Lean compiles to `Nat.decEq` or `Int.decEq` tests) into one `match` with
an arm per literal (`LowerCtx.intMatch`).
-/

namespace LeanToReussir.Opt.IntMatch
open Lean Compiler LCNF

/-- Stage 2's `toMono` replaced by lean2rr's copy that keeps `cases` on
`Nat` and `Int`, and the lowering's chains of literal tests on. -/
def install (c : PassConfig) : PassConfig :=
  { c with
    stage2 := c.stage2.map fun e => match e with
      | .replace n _ why => if n == `toMono then .replace n (toMonoK (keepIntCases := true)) why else e
      | e => e
    intMatch := true }

end LeanToReussir.Opt.IntMatch
