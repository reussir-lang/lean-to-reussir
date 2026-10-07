/-! Runtime test: joined matches (Lean 4.34.0's `joinTypes` gives a join
point's parameter the type `◾` when one arm gives a type or a predicate;
translation plan §10, "Compiler: Lean bugs we do not reproduce") in two
shapes of the review of the fix:
- `m1`: two joined values as in RtJoinErasedFlow's `p5`, whose two
  identical lambdas Lean's specializer turns into one declaration with two
  calls. Natively `toMono` passes `◾` at both calls (and `cse` merges
  them), and `m1 false 0 [1, 2]` prints 100. lean2rr gives the
  declaration's parameter the type `lcAny` before `toMono` runs, so the two
  calls keep their values;
- `m3`: a match of three arms, two of which give a predicate. Natively
  `m3 .b 0` prints 100.
lean2rr prints the kernel's values (the `example`s below): native's output
is in `RtJoinErasedMerge.native.out`, lean2rr's in
`RtJoinErasedMerge.l2r.out`. The cases that take an erased arm agree on
both sides. (The review's `m2`, two calls of a helper with the two values,
crashes natively: it is in RtJoinErasedLayouts.) -/

@[noinline] def g (n : Nat) : Nat := n + 100

def TP : Bool → Type 1
  | true  => Type
  | false => ULift.{1} (Nat × Nat)

def m1 (b : Bool) (n : Nat) (xs : List Nat) : Nat :=
  let v1 : TP b := match b with
    | true  => Nat
    | false => ULift.up (g n, n + 5)
  let v2 : TP b := match b with
    | true  => Nat
    | false => ULift.up (n + 1000, n + 5)
  let w := g n
  match b, v1, v2 with
  | false, v1, v2 =>
    (xs.map (fun x => x + (show ULift.{1} (Nat × Nat) from v1).down.1)).foldl (· + ·) w
    + (xs.map (fun x => x + (show ULift.{1} (Nat × Nat) from v2).down.1)).foldl (· + ·) 0
  | true, _, _ => w

inductive Three | a | b | c

def T3 : Three → Type
  | .a => Nat → Prop
  | .b => Nat
  | .c => Nat → Prop

def m3 (t : Three) (n : Nat) : Nat :=
  let v : T3 t := match t with
    | .a => fun _ => True
    | .b => g n
    | .c => fun _ => False
  let w := g n
  match t, v with
  | .b, v => (show Nat from v) + w
  | .a, _ => w
  | .c, _ => w + 1

example : m1 false 0 [1, 2] = 100 + 101 + 102 + 1001 + 1002 := rfl
example : m1 true 7 [1, 2] = 107 := rfl
example : m3 .b 0 = 200 := rfl
example : m3 .a 7 = 107 := rfl
example : m3 .c 7 = 108 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  IO.println s!"m1 false {k} [1, 2] = {m1 (k == 7) k [1, 2]}"
  let t : Three := if k == 7 then .a else .b
  IO.println s!"m3 b {k} = {m3 t k}"
  -- 7 and true at run time
  let k7 := k + 7
  IO.println s!"m1 true {k7} [1, 2] = {m1 (k7 == 7) k7 [1, 2]}"
  let ta : Three := if k7 == 7 then .a else .b
  IO.println s!"m3 a {k7} = {m3 ta k7}"
  let tc : Three := if k7 == 7 then .c else .b
  IO.println s!"m3 c {k7} = {m3 tc k7}"
