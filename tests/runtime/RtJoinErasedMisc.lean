/-! Runtime test: two more forms of the joined match of RtJoinErasedProp
(Lean 4.34.0's `joinTypes` gives the join point's parameter the type `◾`
when one arm gives a predicate; translation plan §10, "Compiler: Lean bugs
we do not reproduce"; shapes of the review of the fix):
- `dec`: the data arm gives a `Decidable` (a `Bool` at run time), matched
  in the join point;
- `cas`: the match written as `Bool.casesOn` with an explicit motive.
Natively each reads `◾` (the boxed 0) in place of the value and prints 0
and 100. lean2rr prints the kernel's values (the `example`s below):
native's output is in `RtJoinErasedMisc.native.out`, lean2rr's in
`RtJoinErasedMisc.l2r.out`. The `true` cases agree on both sides. -/

@[noinline] def g (n : Nat) : Nat := n + 100

def TDec : Bool → Nat → Type
  | true, _  => Nat → Prop
  | false, n => Decidable (g n < 150)

def dec (b : Bool) (n : Nat) : Nat :=
  let v : TDec b n := match b with
    | true  => fun _ => True
    | false => Nat.decLt (g n) 150
  let w := g n
  match b, v with
  | false, v => (match (show Decidable (g n < 150) from v) with | isTrue _ => w + 1 | isFalse _ => w + 2)
  | true,  _ => w

def T : Bool → Type
  | true  => Nat → Prop
  | false => Nat

def cas (b : Bool) (n : Nat) : Nat :=
  let v : T b := Bool.casesOn (motive := T) b (g n) (fun _ => True)
  let w := g n
  match b, v with
  | false, v => (show Nat from v) + w
  | true,  _ => w

example : dec false 0 = 101 := rfl
example : cas false 0 = 200 := rfl
example : dec true 7 = 107 := rfl
example : cas true 7 = 107 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  let b := k == 7
  IO.println s!"dec false {k} = {dec b k}"
  IO.println s!"cas false {k} = {cas b k}"
  -- 7 and true at run time
  let k7 := k + 7
  let b7 := k7 == 7
  IO.println s!"dec true {k7} = {dec b7 k7}"
  IO.println s!"cas true {k7} = {cas b7 k7}"
