/-! Runtime test: a hot loop on a typed structure field (`St.xs : List
Float`) with a branch, never taken at these inputs, that packs the field
into an existential (design review of the layout redesign, performance,
repro ColdPack). The cold branch must not change the cost of the hot loop:
each step pushes a `Float` and reads the two top elements. Natively each
push allocates a list cell and a boxed `Float`. The output is checked
here; the allocations by tests/runtime/alloc-check.sh (RtDepColdPack.alloc).
Argument: N (default 1000). -/
structure St where
  xs : List Float
  n : Nat

structure Packed where
  α : Type
  xs : List α
  f : α → Nat

@[noinline] def Packed.headVal (p : Packed) : Nat :=
  match p.xs with
  | [] => 0
  | x :: _ => p.f x

@[noinline] def St.push (s : St) (x : Float) : St := { s with xs := x :: s.xs, n := s.n + 1 }

@[noinline] def sumTop (s : St) : Float :=
  match s.xs with
  | a :: b :: _ => a + b
  | _ => 0

@[noinline] def loop (lim : Nat) : Nat → St → Float → Float
  | 0, s, acc => acc + Float.ofNat s.n
  | k + 1, s, acc =>
    let s := s.push (Float.ofNat k)
    let acc := acc + sumTop s
    -- cold path: never taken for the inputs used (lim > n)
    let acc := if k == lim then acc + Float.ofNat (Packed.headVal ⟨Float, s.xs, fun x => x.toUInt64.toNat⟩) else acc
    loop lim k s acc

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  IO.println s!"{loop (n + 7) n ⟨[], 0⟩ 0}"
