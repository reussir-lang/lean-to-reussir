module

import ModuleVisInlineDep

/-!
A documented difference (translation plan §10, "Inlining across a `module`
boundary"): code inlined across the boundary of a `module` file moves a
closed term into the importer. `f` of the companion module
(`ModuleVisInlineDep`) is public but not `@[expose]`: natively a `module`
importer does not see its mono body, so `g` calls `f` and `f`'s closed
term `noisyP rfl` lives once, in the companion module's cache, and traces
`noisy` once (`RtModuleVisInline.native.err`). lean2rr imports every
module at the private level, so Lean's passes in Stage 2 inline `f` into
`g`, and the term becomes a second closed term, of this module: `noisy`
twice (`RtModuleVisInline.l2r.err`). Results are the same; only an effect
in such a closed term (a trace, a panic) shows. A bug hunt of the passes
(repro c1), judged a documented difference: emulating the exported level
in Stage 2 would also take inlining away from Init and Std.
-/

@[noinline] def g (x : Nat) : Nat := f x + f (x + 1)

public def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (g n)
  IO.println (g (n + 1))
  IO.println (g (n + 2))
  IO.println (h n)
