import Lean
import LeanToReussir.PassConfig

/-!
# Helpers for live code only (optimization `conv-liveness`)

The functions Stage 4 generates at the end (unboxing functions, the
application and conversion functions of function values, the reference
dispatch) follow a type-based reachability from the entry point and the
runtime's entries: a helper is generated only once live code calls it,
with an arm only for each variant of `Box` or of its function type that
live code builds, and the functions nothing reaches are dropped
(Lower/Live, `Finish.finishLive`; translation plan §5.3). A removed arm
matches a variant no running code builds, so the program computes the same
results. The one other difference is at translation time: an extern that
only a removed arm would call is not reported as missing
(docs/implementation/conversions/liveness.md).
Without this pass every helper requested anywhere is generated with an arm
for every variant registered anywhere: in a program that can cast, the
helpers grow quadratically (on a program importing a large library, 95 %
of the functions were helpers that can never run).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Registry entry point (a switch). -/
def Opt.ConvLiveness.install (c : PassConfig) : PassConfig :=
  { c with convLiveness := true }

end LeanToReussir
