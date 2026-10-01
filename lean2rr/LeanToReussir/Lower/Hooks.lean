import LeanToReussir.Lower.JoinPoints

/-!
# Stage 4: the hooks of code lowering

The points where optional passes change how declarations and their code are
lowered. Each default is the plain translation; an optimization module
(`Opt/*.lean`) supplies another function in its `install`, and
Opt/Registry.lean installs the enabled ones. `lowerDecl` and the code
lowering (`Lower/Code`) take the hooks as their first argument.
-/

namespace LeanToReussir
open Lean Compiler LCNF

structure LowerHooks where
  /-- Whether a constant (a declaration without parameters) with body
  `body` is recomputed at every use instead of computed once and kept in a
  once-cell (`cafAccessor`). Plain: kept (Opt/CheapConsts). -/
  recomputeConst : Code .pure → LowerM Bool := fun _ => pure false

end LeanToReussir
