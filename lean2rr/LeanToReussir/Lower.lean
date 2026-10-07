import LeanToReussir.Lower.Ctx
import LeanToReussir.Lower.FnValues
import LeanToReussir.Lower.LazyForce
import LeanToReussir.Lower.Conv
import LeanToReussir.Lower.Decls
import LeanToReussir.Lower.Live
import LeanToReussir.Lower.Externs
import LeanToReussir.Lower.LazyGlue
import LeanToReussir.Lower.Process
import LeanToReussir.Lower.Promises
import LeanToReussir.Lower.Identity
import LeanToReussir.Lower.ExternCall
import LeanToReussir.Lower.Borrow
import LeanToReussir.Lower.Values
import LeanToReussir.Lower.JoinPoints
import LeanToReussir.Lower.StateMachine
import LeanToReussir.Lower.BoxedUses
import LeanToReussir.Lower.Hooks
import LeanToReussir.Lower.Code
import LeanToReussir.Lower.Finish

/-!
# Stage 4: lowering mono LCNF to Reussir

Translation plan §5.2–§5.8. Code is lowered declaration by declaration:

* calls follow Lean's arities exactly (§5.2): a saturated call is a direct
  call, a partial application becomes a chain of single-parameter lambdas
  that calls the function only when its last argument arrives, and an
  over-application calls and then applies the result;
* closure values are curried and applied one argument at a time (§5.3);
* `cases` becomes `if`, `match` or field access (§5.5);
* join points are inlined (J1), turned into a structured `let` (J2), or
  outlined into a function called in tail position (J3) (§5.6);
* conversions to and from `Box` are inserted where a value's type differs
  from the type its use expects.

The parts, each importing the previous one (Lean needs definitions before
their uses, so the split follows the original order): `Lower/Ctx` (the
code-lowering context), `FnValues`, `LazyForce`, `Conv`, `Decls`,
`Externs`, `LazyGlue`, `Process`, `Promises`, `Identity`, `ExternCall`,
`Borrow`, `Values`, `JoinPoints`, `StateMachine` (J4), `BoxedUses` (the
variables that only go back into boxes), `Hooks` (where optional passes plug in), `Code`
(including `lowerDecl`), `Finish`. `Live` (the liveness of the optional pass
`conv-liveness`, used by `Externs` and `Finish`) imports `FnValues`.
-/
