import Lean
import LeanToReussir.PassConfig

/-!
# Only the prelude's functions a program uses (optimization `prelude-liveness`)

The program text keeps only the runtime prelude's functions that the
generated code names, directly or through the prelude's kept functions
(PreludePrune, `prune`; applied by `LoweredProgram.render`). rrc compiles
every texture of its input with its own rustc run (about 25 ms each, one
after the other, when its texture cache misses: after every change of
leanrt, lean-runtime or Reussir, and in a new checkout), also a texture no
code calls, and it lowers every function. A one-line program had 484
textures before and has 75 (rrc: 14.3 s → 3.1 s with an empty texture
cache, 1.8 s → 1.1 s with a full one; docs/implementation/optional-passes.md).
A removed function is one that no code of the program can call, so the
program computes the same results. Without this pass the whole prelude is
in the program text.
-/

namespace LeanToReussir

/-- Registry entry point (a switch). -/
def Opt.PreludeLiveness.install (c : PassConfig) : PassConfig :=
  { c with prunePrelude := true }

end LeanToReussir
