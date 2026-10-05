-- Issue 20 (a cost of rrc's MLIR inliner): polymorphic recursion through
-- `StateT`. Every level runs `nestS` at `StateT Nat m` for the previous `m`,
-- so lean2rr builds a uniform instance with many representations of a few
-- function types and the conversions between them. Prints "S 5".
def nestS {m : Type → Type} [Monad m] : Nat → m Nat
  | 0 => pure 0
  | n+1 => do
    let r ← (nestS (m := StateT Nat m) n).run' n
    pure (r + 1)

def main (args : List String) : IO Unit := do
  IO.println s!"S {Id.run (nestS (args.length + 5))}"
