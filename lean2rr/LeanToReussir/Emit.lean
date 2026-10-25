import LeanToReussir.Emit.Startup
import LeanToReussir.Emit.Entry
import LeanToReussir.Emit.Program
import LeanToReussir.Emit.IntBackendCheck

/-!
# Program assembly

`Emit/Startup` (startup order and chain), `Emit/Entry` (the entry point:
`main`, exit), `Emit/Program` (`lowerProgram`: lowering every declaration,
the finishing loop, and the assembled `.rr` text), `Emit/IntBackendCheck`
(the check of `--int-backend rcgmp` without `--rcgmp-type-args`).
-/
