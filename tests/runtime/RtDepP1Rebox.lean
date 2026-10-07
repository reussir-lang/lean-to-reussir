/-! Runtime test: a `while` loop over a state `x : α` (instantiated at
`Float`) that stores `x` into two existential packages at every step
(design review of the layout redesign, performance, repro P1Rebox): one
value boxed at most once per step for both packages, as native Lean boxes
it once. The output is checked here; the allocations by
tests/runtime/alloc-check.sh (RtDepP1Rebox.alloc). Argument: N (default
1000). -/
structure Pk where
  α : Type
  v : α
  f : α → Nat

@[noinline] def Pk.get (p : Pk) : Nat := p.f p.v

class Num' (α : Type) where
  add : α → α → α
  one : α
  toN : α → Nat

instance : Num' Float := ⟨(· + ·), 1.0, fun y => y.toUInt64.toNat⟩

def run {α : Type} [Num' α] (x0 : α) (n : Nat) : Nat := Id.run do
  let mut x : α := x0
  let mut acc := 0
  let mut i := 0
  while i < n do
    if i % 2 == 1 then acc := acc + 1
    acc := acc + Pk.get ⟨α, x, Num'.toN⟩ + Pk.get ⟨α, x, fun y => Num'.toN y + 1⟩
    x := Num'.add x Num'.one
    i := i + 1
  return acc

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  IO.println s!"{run (1.0 : Float) n}"
