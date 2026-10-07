/-! Runtime test: the data that a join point's erased parameter receives
(RtJoinErasedProp: Lean 4.34.0's `joinTypes` gives the parameter the type
`◾` when one arm of the `match` gives a type or a predicate) used in other
ways (translation plan §10, "Compiler: Lean bugs we do not reproduce"):
- `p2`: a pair, its two fields read (a `cases` on the parameter);
- `p3`: a closure, applied;
- `p5`: read inside a lambda that Lean's specializer turns into a
  declaration (`List.mapTR.loop._at_.p5.spec_0`), whose parameter for the
  value gets the type `◾` too; `toMono` passes `◾` at every call of it, so
  lean2rr gives that parameter the type `lcAny` before `toMono` runs;
- `p7`: an `Option`, matched.
Natively each reads `◾` (the boxed 0) in place of the value and prints 0,
0, 100, 0 and 0. lean2rr prints the kernel's values (the `example`s below):
native's output is in `RtJoinErasedFlow.native.out`, lean2rr's in
`RtJoinErasedFlow.l2r.out`. The `true` cases agree on both sides. -/

@[noinline] def g (n : Nat) : Nat := n + 100

def TP : Bool → Type 1
  | true  => Type
  | false => ULift.{1} (Nat × Nat)

def p2 (b : Bool) (n : Nat) : Nat :=
  let v : TP b := match b with
    | true  => Nat
    | false => ULift.up (g n, n + 5)
  let w := g n
  match b, v with
  | false, v => (show ULift.{1} (Nat × Nat) from v).down.1 + (show ULift.{1} (Nat × Nat) from v).down.2 + w
  | true,  _ => w

def TF : Bool → Type
  | true  => Nat → Prop
  | false => Nat → Nat

@[noinline] def mk (n : Nat) : Nat → Nat := fun x => x + n

def p3 (b : Bool) (n : Nat) : Nat :=
  let v : TF b := match b with
    | true  => fun _ => True
    | false => mk n
  let w := g n
  match b, v with
  | false, v => (show Nat → Nat from v) w
  | true,  _ => w

def p5 (b : Bool) (n : Nat) (xs : List Nat) : Nat :=
  let v : TP b := match b with
    | true  => Nat
    | false => ULift.up (g n, n + 5)
  let w := g n
  match b, v with
  | false, v => (xs.map (fun x => x + (show ULift.{1} (Nat × Nat) from v).down.1)).foldl (· + ·) w
  | true,  _ => w

def TO : Bool → Type 1
  | true  => Type
  | false => ULift.{1} (Option Nat)

def p7 (b : Bool) (n : Nat) : Nat :=
  let v : TO b := match b with
    | true  => Nat
    | false => ULift.up (if n > 3 then some (g n) else none)
  let w := g n
  match b, v with
  | false, v => (match (show ULift.{1} (Option Nat) from v).down with | some x => x + w | none => w + 1)
  | true,  _ => w

example : p2 false 0 = 205 := rfl
example : p3 false 0 = 100 := rfl
example : p5 false 0 [1, 2] = 303 := rfl
example : p7 false 0 = 101 := rfl
example : p7 false 5 = 210 := rfl
example : p2 true 7 = 107 := rfl
example : p5 true 7 [1, 2] = 107 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  IO.println s!"p2 false {k} = {p2 (k == 7) k}"
  IO.println s!"p3 false {k} = {p3 (k == 7) k}"
  IO.println s!"p5 false {k} [1, 2] = {p5 (k == 7) k [1, 2]}"
  IO.println s!"p7 false {k} = {p7 (k == 7) k}"
  IO.println s!"p7 false {k + 5} = {p7 (k == 7) (k + 5)}"
  -- 7 and true at run time
  let k7 := k + 7
  IO.println s!"p2 true {k7} = {p2 (k7 == 7) k7}"
  IO.println s!"p3 true {k7} = {p3 (k7 == 7) k7}"
  IO.println s!"p5 true {k7} [1, 2] = {p5 (k7 == 7) k7 [1, 2]}"
  IO.println s!"p7 true {k7} = {p7 (k7 == 7) k7}"
