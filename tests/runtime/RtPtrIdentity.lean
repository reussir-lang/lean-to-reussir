/-! Runtime test: `ptrAddrUnsafe` answers what native Lean answers (adv4
RP4-01, RP4-02). Boxed scalars answer their word `2n+1` (small `Nat`s,
`int32` `Int`s, `UInt8/32`, `Char`, `Bool`, enumerations, nullary
constructors, `Unit`); a value held in uniform code (an existential payload,
a function value or a thunk/task converted to another representation)
answers the original's identity; `UInt64` and `Float`, boxed into a new
cell at each call natively, are not `ptrEq` across a call boundary, but are
to themselves once Lean's CSE merged the two calls. Fixpoint loops that stop
when a step returns its argument stop after native's number of steps. Only
booleans and scalar words are printed (heap addresses vary). -/

structure Pkg where
  α : Type
  v : α
  f : α → α

structure PkgV where
  α : Type
  v : α

structure PkgT where
  α : Type
  t : Thunk α

structure PkgK where
  α : Type
  t : Task α

inductive C | a | b | c
inductive L | nil | one | cons (x : Nat) (t : L)
structure W where x : UInt64
unsafe structure U where n : Nat

@[noinline] unsafe def same2 {α : Type} (x y : α) : Bool := ptrEq x y
@[noinline] unsafe def addr {α : Type} (x : α) : USize := ptrAddrUnsafe x
@[noinline] unsafe def unchanged (p : Pkg) : Bool := ptrEq p.v (p.f p.v)
@[noinline] unsafe def sameV (p q : PkgV) : Bool := ptrAddrUnsafe p.v == ptrAddrUnsafe q.v
@[noinline] unsafe def sameT (p q : PkgT) : Bool := ptrAddrUnsafe p.t == ptrAddrUnsafe q.t
@[noinline] unsafe def sameK (p q : PkgK) : Bool := ptrAddrUnsafe p.t == ptrAddrUnsafe q.t
@[noinline] unsafe def forceT (p : PkgT) : Nat := (unsafeCast p.t.get : Nat)

@[noinline] unsafe def fixPtr {α : Type} (f : α → α) (x : α) : Nat → Nat
  | 0 => 999
  | n+1 => let y := f x; if ptrEq x y then 0 else 1 + fixPtr f y n

@[noinline] def nextC : C → C | .a => .b | _ => .c

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  -- Boxed scalars: the words native Lean answers.
  IO.println s!"nat {addr (k + 5)} {addr (2 ^ 63 - 1 + k)} int {addr ((k : Int) - 5)} {addr ((k : Int) + 2 ^ 31 - 1)} {addr ((k : Int) - 2 ^ 31)}"
  IO.println s!"u8 {addr (k.toUInt8 + 200)} u32 {addr (k.toUInt32 + 9)} char {addr 'a'} bool {addr true} {addr false} unit {addr ()}"
  IO.println s!"enum {addr C.c} nullary {addr L.nil} {addr L.one} {addr (none : Option Nat)} i8 {addr (k.toInt8 - 1)} i32 {addr (k.toInt32 - 1)}"
  IO.println s!"heap is even {addr (some (k + 1) : Option Nat) % 2} {addr (2 ^ 70 + k) % 2} {addr [k] % 2}"
  -- The same variable twice.
  let n := k + 5
  let i : Int := (k : Int) - 3
  let c := if args.isEmpty then C.b else C.a
  let big := 2 ^ 80 + k
  IO.println s!"self {same2 n n} {same2 i i} {same2 c c} {same2 () ()} {same2 big big} {same2 L.one L.one}"
  -- UInt64/Float: a new cell at each call natively; CSE'd calls agree.
  let u : UInt64 := k.toUInt64 + 7
  let fl : Float := k.toFloat + 1.5
  let w : W := ⟨u⟩
  IO.println s!"cells {same2 u u} {same2 fl fl} {same2 w w} direct {ptrEq u u} {ptrEq fl fl}"
  -- Uniform code: a payload is itself, through its own function too.
  let l : List Nat := [k, 2]
  let fn : Nat → Nat := fun x => x + k
  let th : Thunk Nat := Thunk.mk fun _ => 5 + k
  let tk : Task Nat := Task.spawn fun _ => 6 + k
  IO.println s!"payload {unchanged ⟨String, "abc", fun s => s⟩} {unchanged ⟨List Nat, l, fun l => l⟩} {unchanged ⟨Nat, 7, fun m => m⟩} {unchanged ⟨UInt64, u, fun v => v⟩}"
  IO.println s!"two {sameV ⟨List Nat, l⟩ ⟨List Nat, l⟩} {sameV ⟨Nat → Nat, fn⟩ ⟨Nat → Nat, fn⟩} {sameV ⟨Nat, n⟩ ⟨Nat, n⟩} {sameV ⟨Thunk Nat, th⟩ ⟨Thunk Nat, th⟩}"
  IO.println s!"lazy {sameT ⟨Nat, th⟩ ⟨Nat, th⟩} {sameK ⟨Nat, tk⟩ ⟨Nat, tk⟩}"
  -- A converted thunk keeps the original's identity once forced, and so
  -- does a converted forced thunk.
  let p : PkgT := ⟨Nat, th⟩
  let before := ptrAddrUnsafe p.t
  let v := forceT p
  IO.println s!"forced {v} {before == ptrAddrUnsafe p.t} {sameT ⟨Nat, th⟩ p} {th.get}"
  -- Fixpoints stop where native ones do.
  IO.println s!"fix nat {fixPtr (fun m : Nat => m / 2) 100 50} big {fixPtr (fun m : Nat => if m > 2 ^ 80 then m / 2 else m) (2 ^ 90) 50} enum {fixPtr nextC .a 50}"
  IO.println s!"fix U {fixPtr (fun (x : U) => if x.n > 5 then x else ⟨x.n + 1⟩) ⟨0⟩ 50} int {fixPtr (fun j : Int => if j < -3 then j + 1 else j) (-10) 50}"
  IO.println s!"fix list {fixPtr (fun (xs : List Nat) => match xs with | 0 :: t => t | t => t) [0, 0, 0, k + 1] 50} opt {fixPtr (fun (o : Option Nat) => match o with | some 0 => none | x => x) (some 0) 50}"
