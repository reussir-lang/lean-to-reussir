/-! Runtime test: a `match` whose one arm gives a predicate (`T true` is
`Nat → Prop`, erased at run time) and whose other arm gives data (`T false`
is `Nat`), followed by code that uses the data (translation plan §10,
"Compiler: Lean bugs we do not reproduce"). Lean 4.34.0's `toLCNF` joins
the arms' types with `joinTypes`, which gives `◾` when one side is erased,
so the join point after the `match` gets a parameter of type `lcErased`,
and the jump from the `false` arm passes the number to it. Natively the
impure phase drops that parameter and reads `◾` (the boxed 0) instead:
`f false 0` prints 100 and `f2 false 41` prints 1. The kernel gives 200 and
42 (the `example`s below). lean2rr gives such a parameter the type `lcAny`
(a boxed data parameter), so it prints the kernel's values: native's output
is in `RtJoinErasedProp.native.out`, lean2rr's in `RtJoinErasedProp.l2r.out`.
The constant `c := f2 false 41` is computed at run time from `f2`'s join
point (Lean's passes do not fold it): native 1, kernel 42. The `true` cases
take the arm that gives the predicate, and `ci` (`f2` inlined: Lean's
`simp` puts the number in place of the parameter) gives 42: these agree on
both sides. -/

-- `T true` is a predicate type (erased at run time), `T false` is `Nat` (data).
def T : Bool → Type
  | true  => Nat → Prop
  | false => Nat

@[noinline] def g (n : Nat) : Nat := n + 100

-- Code between the `match` and its use (`w`): a join point with the
-- erased parameter.
def f (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => g n
  let w := g n
  match b, v with
  | false, v => (show Nat from v) + w
  | true,  _ => w

-- No code between the `match` and its use.
def f2 (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => n
  match b, v with
  | false, v => (show Nat from v) + 1
  | true,  _ => 0

-- A constant that calls `f2`.
def c : Nat := f2 false 41

-- `f2` inlined into a constant.
@[inline] def f2i (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => n
  match b, v with
  | false, v => (show Nat from v) + 1
  | true,  _ => 0

def ci : Nat := f2i false 41

example : f false 0 = 200 := rfl
example : f2 false 41 = 42 := rfl
example : f true 7 = 107 := rfl
example : f2 true 48 = 0 := rfl
example : c = 42 := rfl
example : ci = 42 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  IO.println s!"f false {k} = {f (k == 7) k}"
  IO.println s!"f2 false {k + 41} = {f2 (k == 7) (k + 41)}"
  -- 7 and true at run time
  let k7 := k + 7
  IO.println s!"f true {k7} = {f (k7 == 7) k7}"
  IO.println s!"f2 true {k7 + 41} = {f2 (k7 == 7) (k7 + 41)}"
  IO.println s!"c = {c}"
  IO.println s!"ci = {ci}"
