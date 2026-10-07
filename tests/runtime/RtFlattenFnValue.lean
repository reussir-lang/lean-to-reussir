/-! Runtime test: optimization `flatten-structs` and a loop reached through
its wrapper (a function value) with the caller's record (review of the
pass, round 4, F1). Every step of `run` builds a new record, and with an
empty list it returns the caller's record itself (natively `same=true`).
Callers through the wrapper pass existing objects (`AState.entryExisting`
from `analyze`), so `run` keeps its result whole and runs its first step in
the wrapper: never a copy per call (`RtFlattenFnValue.alloc`). -/
structure P where
  a : Nat
  b : Nat
  deriving Inhabited

-- every step builds a new P; with [] it returns p itself
@[noinline] def run (p : P) : List Nat → P
  | [] => p
  | x :: xs => run ⟨p.a + x, p.b + 1⟩ xs

-- a fresh value, the result read field by field
@[noinline] def fromFresh (n : Nat) (xs : List Nat) : Nat := (run ⟨n, n⟩ xs).a

-- reaches run through its wrapper
@[noinline] def callRun (f : P → List Nat → P) (p : P) (n : Nat) : Array P := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (f p (if i % 1000 == 999 then [i] else []))
  return out

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [k] =>
    let n := k.toNat!
    let out := callRun run ⟨n, 1⟩ n
    IO.println s!"{out.size} {fromFresh 2 [1, 2]} {out.foldl (fun a p => a + p.b) 0}"
  | _ =>
    let b0 : P := ⟨7, 1⟩
    let w := callRun run b0 2
    IO.println s!"wrap {w[0]!.a} {fromFresh 2 [3]} same={ptrAddrUnsafe w[0]! == ptrAddrUnsafe b0}"
