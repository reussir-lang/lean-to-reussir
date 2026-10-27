import LeanToReussir.Emit.Startup
import LeanToReussir.Emit.Entry
import LeanToReussir.Emit.Program
import LeanToReussir.Emit.CopyAnchors
import LeanToReussir.Emit.ArmRelease

/-!
# Program assembly

`Emit/Startup` (startup order and chain), `Emit/Entry` (the entry point:
`main`, exit), `Emit/Program` (`lowerProgram`: lowering every declaration,
the finishing loop, and the assembled `.rr` text), `Emit/ArmRelease` (the
values that die at the start of a branch released in native Lean's
order, in a program that makes resources), `Emit/CopyAnchors` (the functions kept out of rrc's inliner because their
copies would make one function too large; `inline-anchors`).
-/
