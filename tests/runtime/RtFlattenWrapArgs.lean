/-! Runtime test: optimization `flatten-structs` and a call that goes
through the callee's wrapper because the declaration keeps its result
whole (`AState.wholeCalls`: rebuilt in a join point's body and at a jump;
review of the pass, round 5, G2). The wrapper takes its arguments whole,
so the analysis constrains them as whole uses: the loop's parameter,
passed on unchanged, is not built again for every call. -/
structure P where
  a : Nat
  b : Nat
  deriving Inhabited

-- non-recursive; reads its parameter field by field (split where callers
-- pass known fields); its result is split too (readF reads it)
@[noinline] def f (p : P) (i : Nat) : Nat × Nat := (p.a + i, p.b)

@[noinline] def readF (i : Nat) : Nat := (f ⟨i, i⟩ i).1

-- s is passed on unchanged at every step
@[noinline] def loopW (s : P) : Nat → Array (Nat × Nat) → Array (Nat × Nat)
  | 0, acc => acc
  | n+1, acc =>
    let r := f s n
    let q := if n % 2 == 0 then r else (n, n)
    loopW s n ((acc.push q).push r)

def main (args : List String) : IO Unit := do
  match args with
  | [k] =>
    let n := k.toNat!
    let out := loopW ⟨n, 1⟩ n (Array.mkEmpty (2 * n))
    IO.println s!"{out.size} {readF 3}"
  | _ =>
    let out := loopW ⟨args.length + 7, 1⟩ 3 #[]
    IO.println s!"loopW {out} {readF 2}"
