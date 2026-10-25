import LeanToReussir.Emit.Startup
import LeanToReussir.Emit.Entry
import LeanToReussir.Emit.Program
import LeanToReussir.Emit.IntBackendCheck
import LeanToReussir.Emit.CopyAnchors

/-!
# Program assembly

`Emit/Startup` (startup order and chain), `Emit/Entry` (the entry point:
`main`, exit), `Emit/Program` (`lowerProgram`: lowering every declaration,
the finishing loop, and the assembled `.rr` text), `Emit/IntBackendCheck`
(the check of `--int-backend rcgmp` without `--rcgmp-type-args`),
`Emit/CopyAnchors` (the functions kept out of rrc's inliner because their
copies would make one function too large; `inline-anchors`).
-/
