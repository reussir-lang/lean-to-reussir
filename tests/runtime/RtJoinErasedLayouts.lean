/-! Runtime test: the joined match of RtJoinErasedType (Lean 4.34.0's
`joinTypes` gives the join point's parameter the type `◾` when one arm
gives a type; translation plan §10, "Compiler: Lean bugs we do not
reproduce") with data of other layouts: a `String` (`ss`), an
`Array Nat` (`sa`), a structure with a `Float` field (`sp`), a structure
of two scalars (`st`), and two pairs passed to a helper (`m2`); shapes of
the review of the fix. Natively the join point reads `◾` (the boxed 0) as
that value: `ss`, `sa`, `sp` and `m2` each end with a segmentation fault
(exit 139; `ss` runs first, so nothing is printed:
`RtJoinErasedLayouts.native.out` is empty and
`RtJoinErasedLayouts.native.code` holds 139), and `st` alone prints 0.
lean2rr prints the kernel's values (the `example`s below; `sp`'s is
`100.0 + 0.0 + 0.0`) and exits 0: `RtJoinErasedLayouts.l2r.out` and
`RtJoinErasedLayouts.l2r.code`. Every `false` case is taken first, then
every `true` case, which takes the erased arm (`box(0)` at the retyped
parameter). -/

def TS : Bool → Type 1
  | true  => Type
  | false => ULift.{1} String

def TA : Bool → Type 1
  | true  => Type
  | false => ULift.{1} (Array Nat)

structure Pt where
  x : Float
  y : Nat

def TP : Bool → Type 1
  | true  => Type
  | false => ULift.{1} Pt

structure Two where
  a : UInt32
  b : UInt8

def TT : Bool → Type 1
  | true  => Type
  | false => ULift.{1} Two

@[noinline] def g (n : Nat) : Nat := n + 100

def ss (b : Bool) (n : Nat) : String :=
  let v : TS b := match b with
    | true  => Nat
    | false => ULift.up (toString (g n))
  let w := toString n
  match b, v with
  | false, v => (show ULift.{1} String from v).down ++ "/" ++ w
  | true,  _ => w

def sa (b : Bool) (n : Nat) : Nat :=
  let v : TA b := match b with
    | true  => Nat
    | false => ULift.up #[g n, n, 3]
  let w := g n
  match b, v with
  | false, v => (show ULift.{1} (Array Nat) from v).down.foldl (· + ·) w
  | true,  _ => w

def sp (b : Bool) (n : Nat) : Float :=
  let v : TP b := match b with
    | true  => Nat
    | false => ULift.up ⟨Float.ofNat (g n), n⟩
  let w := Float.ofNat n
  match b, v with
  | false, v => (show ULift.{1} Pt from v).down.x + Float.ofNat (show ULift.{1} Pt from v).down.y + w
  | true,  _ => w

def st (b : Bool) (n : Nat) : Nat :=
  let v : TT b := match b with
    | true  => Nat
    | false => ULift.up ⟨(g n).toUInt32, n.toUInt8⟩
  let w := g n
  match b, v with
  | false, v => (show ULift.{1} Two from v).down.a.toNat + (show ULift.{1} Two from v).down.b.toNat + w
  | true,  _ => w

def TQ : Bool → Type 1
  | true  => Type
  | false => ULift.{1} (Nat × Nat)

@[noinline] def h (p : Nat × Nat) (k : Nat) : Nat := p.1 + p.2 + k

def m2 (b : Bool) (n : Nat) : Nat :=
  let v1 : TQ b := match b with
    | true  => Nat
    | false => ULift.up (g n, n + 5)
  let v2 : TQ b := match b with
    | true  => Nat
    | false => ULift.up (n + 1000, n + 5)
  let w := g n
  match b, v1, v2 with
  | false, v1, v2 =>
    h (show ULift.{1} (Nat × Nat) from v1).down w + h (show ULift.{1} (Nat × Nat) from v2).down w
  | true, _, _ => w

example : ss false 0 = "100/0" := rfl
example : sa false 0 = 203 := rfl
example : st false 0 = 200 := rfl
example : ss true 7 = "7" := rfl
example : sa true 7 = 107 := rfl
example : st true 7 = 107 := rfl
example : m2 false 0 = 105 + 100 + 1005 + 100 := rfl
example : m2 true 7 = 107 := rfl

def main (args : List String) : IO Unit := do
  -- 0 and false at run time
  let k := args.length
  let b := k == 7
  IO.println s!"ss false {k} = {ss b k}"
  IO.println s!"sa false {k} = {sa b k}"
  IO.println s!"sp false {k} = {sp b k}"
  IO.println s!"st false {k} = {st b k}"
  IO.println s!"m2 false {k} = {m2 b k}"
  -- 7 and true at run time
  let k7 := k + 7
  let b7 := k7 == 7
  IO.println s!"ss true {k7} = {ss b7 k7}"
  IO.println s!"sa true {k7} = {sa b7 k7}"
  IO.println s!"sp true {k7} = {sp b7 k7}"
  IO.println s!"st true {k7} = {st b7 k7}"
  IO.println s!"m2 true {k7} = {m2 b7 k7}"
