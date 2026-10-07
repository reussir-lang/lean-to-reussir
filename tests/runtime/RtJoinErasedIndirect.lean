/-! Runtime test: the data that a join point's erased parameter receives
(RtJoinErasedProp: Lean 4.34.0's `joinTypes` gives the parameter the type
`◾` when one arm of the `match` gives a predicate) reaches its use
indirectly (translation plan §10, "Compiler: Lean bugs we do not
reproduce"; shapes of the review of the fix):
- `q1`: a closure that captures the value before the match that refines
  it, applied by another function;
- `q2`: such a closure stored in a structure, read and applied elsewhere;
- `q3`: a partial application of a two-argument closure over the value;
- `q6`: the value reaches a second joined match (two hops).
Natively each reads `◾` (the boxed 0) in place of the value and prints 1,
12, 3 and 1. lean2rr prints the kernel's values (the `example`s below):
native's output is in `RtJoinErasedIndirect.native.out`, lean2rr's in
`RtJoinErasedIndirect.l2r.out`. The `true` cases agree on both sides. -/

def T : Bool → Type
  | true  => Nat → Prop
  | false => Nat

@[noinline] def g (n : Nat) : Nat := n + 100
@[noinline] def apply (h : Unit → Nat) : Nat := h ()
@[noinline] def apply2 (h : Nat → Nat) (k : Nat) : Nat := h k

def q1 (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => g n
  let h : Unit → Nat := fun _ => match b, v with
    | false, v => (show Nat from v) + 1
    | true,  _ => 0
  apply h

structure S where
  f : Nat → Nat
  tag : Nat

@[noinline] def useS (s : S) (k : Nat) : Nat := s.f k + s.tag

def q2 (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => g n
  let s : S := ⟨fun k => match b, v with
    | false, v => (show Nat from v) + k
    | true,  _ => k, 7⟩
  useS s 5

def q3 (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => g n
  let h : Nat → Nat → Nat := fun j k => match b, v with
    | false, v => (show Nat from v) + j + k
    | true,  _ => j + k
  apply2 (h 1) 2

def q6 (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with
    | true  => fun _ => True
    | false => g n
  let w : T b := match b with
    | true  => fun _ => False
    | false => ((match b, v with
      | false, v => (show Nat from v) + 1
      | true,  _ => 0) : Nat)
  match b, w with
  | false, w => (show Nat from w) + 1
  | true,  _ => 0

example : q1 false 0 = 101 := rfl
example : q2 false 0 = 112 := rfl
example : q3 false 0 = 103 := rfl
example : q6 false 0 = 102 := rfl
example : q1 true 7 = 0 := rfl
example : q2 true 7 = 12 := rfl
example : q3 true 7 = 3 := rfl
example : q6 true 7 = 0 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  let b := k == 7
  IO.println s!"q1 false {k} = {q1 b k}"
  IO.println s!"q2 false {k} = {q2 b k}"
  IO.println s!"q3 false {k} = {q3 b k}"
  IO.println s!"q6 false {k} = {q6 b k}"
  -- 7 and true at run time
  let k7 := k + 7
  let b7 := k7 == 7
  IO.println s!"q1 true {k7} = {q1 b7 k7}"
  IO.println s!"q2 true {k7} = {q2 b7 k7}"
  IO.println s!"q3 true {k7} = {q3 b7 k7}"
  IO.println s!"q6 true {k7} = {q6 b7 k7}"
