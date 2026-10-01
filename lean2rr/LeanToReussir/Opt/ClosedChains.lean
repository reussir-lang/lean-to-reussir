import Lean
import LeanToReussir.PassConfig

/-!
# Closed terms used once, not cached (optimization `closed-chains`)

Lean's `extractClosed` turns closed terms into constants, which native Lean
evaluates lazily, once, and keeps for the whole run; lean2rr caches them in
once-cells (translation plan §5.12). An array literal becomes a chain of
such constants, `_closed_k := push _closed_(k-1) e_k`: caching every step
kept every intermediate array alive. A closed term referenced exactly once,
by another constant (which runs once), is therefore evaluated where it is
used instead of cached: it still runs once, at the same point. Without this
pass every closed term is cached.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The closed terms of `decls` referenced exactly once, from a constant
(not from a function, and not a root of the entry point). -/
def chainConsts (decls : Array (Decl .pure)) (roots : Array Name) : NameSet := Id.run do
  let mut uses : NameMap Nat := {}
  let mut fromFunction : NameSet := {}
  for d in decls do
    let .code c := d.value | continue
    for n in codeConsts c #[] do
      uses := uses.insert n (uses.getD n 0 + 1)
      unless d.params.isEmpty do fromFunction := fromFunction.insert n
  let isClosed (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "_closed"
    | _ => false
  return decls.foldl (init := ({} : NameSet)) fun acc d =>
    if d.params.isEmpty && isClosed d.name && uses.getD d.name 0 == 1 && !fromFunction.contains d.name
      && !roots.contains d.name then acc.insert d.name else acc

/-- Registry entry point. -/
def Opt.ClosedChains.install (c : PassConfig) : PassConfig :=
  let prev := c.uncachedConsts
  { c with uncachedConsts := fun decls roots => prev decls roots ++ chainConsts decls roots }

end LeanToReussir
