/-! Runtime test: a `match` whose one arm gives a type (`T true` is `Type`,
erased at run time) and whose other arm gives data (`T false` is
`ULift Nat`), followed by code that uses the data (translation plan §10,
"Compiler: Lean bugs we do not reproduce"; RtJoinErasedProp's case with a
type instead of a predicate). Lean 4.34.0's `toLCNF` joins the arms' types
to `◾`, so the join point after the `match` gets a parameter of type
`lcErased`. Natively the impure phase drops it and reads `◾` (the boxed 0)
in place of the `false` arm's number: `f false 0` and `h false 0` print
100. The kernel gives 200 (the `example`s below), which lean2rr prints:
native's output is in `RtJoinErasedType.native.out`, lean2rr's in
`RtJoinErasedType.l2r.out`. `h` is `f` kept out of line (`@[noinline]`).
The `true` cases agree on both sides. -/

def T : Bool → Type 1
  | true  => Type
  | false => ULift.{1} Nat

@[noinline] def g (n : Nat) : Nat := n + 100

def f (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => Nat
    | false => ULift.up (g n)
  let w := g n
  match b, v with
  | false, v => (show ULift.{1} Nat from v).down + w
  | true,  _ => w

@[noinline] def h (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => Nat
    | false => ULift.up (g n)
  let w := g n
  match b, v with
  | false, v => (show ULift.{1} Nat from v).down + w
  | true,  _ => w

example : f false 0 = 200 := rfl
example : h false 0 = 200 := rfl
example : f true 7 = 107 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  IO.println s!"f false {k} = {f (k == 7) k}"
  IO.println s!"h false {k} = {h (k == 7) k}"
  -- 7 and true at run time
  let k7 := k + 7
  IO.println s!"f true {k7} = {f (k7 == 7) k7}"
  IO.println s!"h true {k7} = {h (k7 == 7) k7}"
