/-! Runtime test: `ptrAddrUnsafe` and `ptrEq` on values of every
representation (scalars, big numbers, `Unit`, enumerations, nullary
constructors, records, `[value]` structures, `UInt64`/`Float`, function
values, thunks, tasks, values held in uniform code, function values and
thunks converted to another representation) run without crashing, and
`ptrEq` saying `true` always means equal values (the property code using it
as a shortcut for equality needs). lean2rr does not emulate native pointer
identity (translation plan §9), so no identity result itself is printed. -/

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

inductive C | a | b | c
  deriving DecidableEq
inductive L | nil | one | cons (x : Nat) (t : L)
  deriving DecidableEq
structure W where x : UInt64
  deriving DecidableEq
structure U where n : Nat
  deriving DecidableEq

-- `ptrEq x y` only when `x = y`.
@[noinline] unsafe def sound {α : Type} [DecidableEq α] (x y : α) : Bool := !ptrEq x y || decide (x = y)
-- The same in uniform code, with the equality of the payload's type.
@[noinline] unsafe def soundU (p : Pkg) (eq : p.α → p.α → Bool) : Bool := let y := p.f p.v; !ptrEq p.v y || eq p.v y
@[noinline] unsafe def soundV (p q : PkgV) (eq : p.α → p.α → Bool) : Bool :=
  !(ptrAddrUnsafe p.v == ptrAddrUnsafe q.v) || eq p.v (unsafeCast q.v)
-- Addresses are computed (and must not crash); nothing about them is
-- printed.
@[noinline] unsafe def addr {α : Type} (x : α) : USize := ptrAddrUnsafe x
@[noinline] unsafe def runs {α : Type} (x : α) : Bool := addr x % 2 < 2

@[noinline] unsafe def fixPtr {α : Type} (f : α → α) (x : α) : Nat → α
  | 0 => x
  | n+1 => let y := f x; if ptrEq x y then y else fixPtr f y n

@[noinline] unsafe def forceT (p : PkgT) : Nat := (unsafeCast p.t.get : Nat)

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  let n := k + 5
  let i : Int := (k : Int) - 3
  let big := 2 ^ 80 + k
  let wide := 2 ^ 63 + k
  let iw : Int := (k : Int) - 2 ^ 40
  let u : UInt64 := k.toUInt64 + 7
  let fl : Float := k.toFloat + 1.5
  let cc := if args.isEmpty then C.b else C.a
  let l : List Nat := [k, 2]
  IO.println s!"scalars {sound n n} {sound n (n + 1)} {sound i i} {sound i (i - 1)} {sound big big} {sound big (big + 1)} {sound wide (wide + 1)} {sound iw (iw + 1)}"
  IO.println s!"words {sound u u} {sound u (u + 1)} {sound (k.toUInt8 + 200) 200} {sound 'a' 'b'} {sound true (k == 0)} {sound () ()} {sound cc C.c}"
  IO.println s!"floats {sound fl.toBits (fl + 1).toBits} {sound (⟨u⟩ : W) ⟨u + 1⟩} {sound (⟨n⟩ : U) ⟨n + 1⟩}"
  IO.println s!"ctors {sound L.nil L.one} {sound L.one L.one} {sound (L.cons n .nil) (L.cons n .nil)} {sound (none : Option Nat) (some k)} {sound l l} {sound l (k :: l)}"
  IO.println s!"heap {sound s!"a{k}" s!"a{k}"} {sound #[n, k] #[n, k]} {sound (some l) (some l)}"
  -- Uniform code.
  IO.println s!"uniform {soundU ⟨String, s!"x{k}", fun s => s⟩ (· == ·)} {soundU ⟨String, s!"x{k}", fun s => s ++ "!"⟩ (· == ·)} {soundU ⟨List Nat, l, fun l => l⟩ (· == ·)} {soundU ⟨List Nat, l, fun l => 1 :: l⟩ (· == ·)} {soundU ⟨Nat, 7, fun m => m + k⟩ (· == ·)} {soundU ⟨UInt64, u, fun v => v⟩ (· == ·)}"
  IO.println s!"packages {soundV ⟨List Nat, l⟩ ⟨List Nat, l⟩ (· == ·)} {soundV ⟨List Nat, l⟩ ⟨List Nat, 3 :: l⟩ (· == ·)} {soundV ⟨Nat, n⟩ ⟨Nat, n + 1⟩ (· == ·)} {soundV ⟨Nat, n⟩ ⟨Nat, n⟩ (· == ·)}"
  -- Function values, thunks and tasks, also converted.
  let fn : Nat → Nat := fun x => x + k
  let th : Thunk Nat := Thunk.mk fun _ => 5 + k
  let tk : Task Nat := Task.spawn fun _ => 6 + k
  let p : PkgT := ⟨Nat, th⟩
  IO.println s!"runs {runs fn} {runs th} {runs tk} {runs p.t} {runs (⟨Nat → Nat, fn⟩ : PkgV).v} {runs (⟨Thunk Nat, th⟩ : PkgV).v} {runs big} {runs fl} {runs ()}"
  IO.println s!"forced {forceT p} {th.get} {tk.get} {runs p.t}"
  -- Fixpoints that stop when a step returns its argument: the final
  -- values (not the number of steps).
  IO.println s!"fix {fixPtr (fun m : Nat => m / 2) 100 50} {fixPtr (fun m : Nat => if m > 2 ^ 80 then m / 2 else m) (2 ^ 90) 50} {fixPtr (fun (xs : List Nat) => match xs with | 0 :: t => t | t => t) [0, 0, 0, k + 1] 50}"
  IO.println s!"fix opt {fixPtr (fun (o : Option Nat) => match o with | some 0 => none | x => x) (some 0) 50} {(fixPtr (fun (x : U) => if x.n > 5 then x else ⟨x.n + 1⟩) ⟨0⟩ 50).n}"
