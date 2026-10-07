/-! Runtime test: a `[value]` struct whose one field is a `Box`
(`ST.Out σ α`: `val : α` and an erased `Void σ`; lean2rr's
`struct [value] T_ST_Out(LAny)`), put into boxes and taken out: list
cells, an array, a thunk, a reference (the review's repro RvSTOut), an
`Option`, a pair, a structure's field of a parameter's type, function
values over it kept in a list, and a generic function applied to it. Its
box is the field's box itself (lean2rr's box API): the struct was boxed
as a box of its own type, which a box cannot be (a panic at the first
boxing, or at the first unboxing). Values: small and big `Nat`s, a
`String`, a `Float` (a cell). -/
@[noinline] def rev {α : Type} (xs : List α) : List α := xs.reverse

@[noinline] def pushAll {α : Type} : List α → Array α → Array α
  | [], acc => acc
  | x :: xs, acc => pushAll xs (acc.push x)

@[noinline] def mkOut (n : Nat) : ST.Out Unit Nat := ⟨n, Void.mk ()⟩

@[noinline] def twice {α : Type} (f : α → α) (x : α) : α := f (f x)

@[noinline] def pick {α : Type} (b : Bool) (x y : α) : α := if b then x else y

structure Holder (α : Type) where
  x : α
  tag : Nat

@[noinline] def bump (o : ST.Out Unit Nat) : ST.Out Unit Nat := mkOut (o.val + 1)

def main : IO Unit := do
  let outs : List (ST.Out Unit Nat) := [mkOut 1, mkOut 2, mkOut (2 ^ 70)]
  IO.println ((rev outs).map (·.val))
  IO.println ((pushAll outs #[]).toList.map (·.val))
  let t : Thunk (ST.Out Unit Nat) := Thunk.mk fun _ => mkOut 7
  IO.println t.get.val
  let r ← IO.mkRef (mkOut 9)
  r.modify fun o => mkOut (o.val + 1)
  IO.println (← r.get).val
  let so : List (ST.Out Unit String) := [⟨"a", Void.mk ()⟩, ⟨"b", Void.mk ()⟩]
  IO.println ((rev so).map (·.val))
  let fo : List (ST.Out Unit Float) := [⟨1.5, Void.mk ()⟩, ⟨-2.25, Void.mk ()⟩]
  IO.println ((rev fo).map (·.val))
  let oo : Option (ST.Out Unit Nat) := some (mkOut (2 ^ 65))
  IO.println (oo.map (·.val))
  let pr : ST.Out Unit Nat × Nat := (mkOut 4, 5)
  IO.println s!"{pr.1.val} {pr.2}"
  let h : Holder (ST.Out Unit String) := ⟨⟨"held", Void.mk ()⟩, 3⟩
  IO.println s!"{h.x.val} {h.tag}"
  let fs : List (ST.Out Unit Nat → ST.Out Unit Nat) := [bump, fun o => mkOut (o.val * 2)]
  IO.println (fs.map (fun f => (f (mkOut 10)).val))
  IO.println (twice bump (mkOut 40)).val
  IO.println (pick false (mkOut 1) (mkOut (2 ^ 66))).val
