/-! Runtime test: structures with one field that carries data, whose type is
a type parameter (`W α`: `x : α` and a proof; `Subtype`, `PLift`, `ULift`,
and a wrapper of a wrapper). Native Lean represents such a structure as
its field, so `W Nat` is a `Nat` and `W α` is whatever `α` is. The values
are built and read at concrete types (`Nat`, `Float`, `UInt64` above 2^63,
`String`, lists) and in code over an unknown type, stored in arrays, lists,
options and existential packages, and read back. `unsafeCast` between a
container of `W α` (or of `Fin n`, or of a `Subtype`) and the same
container of `α` is the same object natively, so its results are defined:
the program casts lists, arrays and options both ways and reads them.
Native Lean prints the values. -/

structure W (α : Type) where
  x : α
  ok : True := trivial

structure WW (α : Type) where
  w : W α

@[noinline] def wrap {α : Type} (a : α) : W α := ⟨a, trivial⟩
@[noinline] def unwrap {α : Type} (w : W α) : α := w.x
@[noinline] def rewrap {α : Type} (w : W α) : WW α := ⟨w⟩

structure Pk where
  α : Type
  w : W α
  sh : α → String

@[noinline] def Pk.show (p : Pk) : String := p.sh p.w.x
@[noinline] def Pk.twice (p : Pk) : Pk := ⟨p.α, wrap (unwrap p.w), p.sh⟩

/-- Generic code over containers of wrappers. -/
@[noinline] def firsts {α : Type} (xs : List (W α)) : Option α := xs.head?.map (·.x)
@[noinline] def lastA {α : Type} (a : Array (WW α)) : Option α := a.back?.map (·.w.x)

def f64 (f : Float) : String := s!"{f.toBits}"

@[noinline] unsafe def castList {α β : Type} (xs : List α) : List β := unsafeCast xs
@[noinline] unsafe def castArr {α β : Type} (xs : Array α) : Array β := unsafeCast xs

unsafe def main (args : List String) : IO Unit := do
  let n := args.length + 5
  -- at concrete types
  let wn : W Nat := wrap (2 ^ 64 + n)
  let wf : W Float := wrap (-0.0)
  let wu : W UInt64 := wrap 18446744073709551615
  let ws : W String := wrap s!"s{n}"
  let wl : W (List Nat) := wrap (List.range n)
  IO.println s!"{unwrap wn} {f64 (unwrap wf)} {unwrap wu} {unwrap ws} {unwrap wl}"
  IO.println s!"{(rewrap wn).w.x} {f64 (rewrap wf).w.x} {(rewrap wu).w.x} {(rewrap (rewrap ws).w).w.x}"
  -- in containers and generic code
  IO.println s!"{firsts [wn, wrap 3]} {(firsts [wf]).map f64} {firsts [wu]} {firsts ([] : List (W String))}"
  IO.println s!"{lastA #[rewrap wn, rewrap (wrap 7)]} {lastA #[rewrap wu]} {lastA #[rewrap ws]}"
  let ps : List Pk := [⟨Nat, wn, toString⟩, ⟨Float, wf, f64⟩, ⟨UInt64, wu, toString⟩, ⟨String, ws, id⟩,
    ⟨List Nat, wl, toString⟩]
  IO.println ((ps.map Pk.twice).map Pk.show)
  -- library one-field structures
  let sub : List { k : Nat // k > 2 } := (List.range n).map fun i => ⟨i + 3, by omega⟩
  let pl : Array (PLift UInt64) := #[⟨18446744073709551614⟩, ⟨1⟩]
  let ul : Option (ULift.{1} Float) := some ⟨2.5⟩
  IO.println s!"{sub.map (·.val)} {pl.map (·.down)} {ul.map fun u => f64 u.down}"
  -- casts between a container of wrappers and of their field, both ways
  let ln : List Nat := castList [wn, wrap 9]
  let lw : List (W Nat) := castList (List.range 4)
  let fins : List (Fin 10) := castList [3, 9, 0]
  let backN : List Nat := castList fins
  let arrS : Array { k : Nat // k > 2 } := castArr #[5, 2 ^ 70]
  let arrW : Array (W UInt64) := castArr #[(9223372036854775808 : UInt64), 2]
  IO.println s!"{ln} {lw.map (·.x)} {fins} {backN} {arrS.map (·.val)} {arrW.map (·.x)}"
  let ow : Option (W Float) := unsafeCast (some (1.5 : Float))
  let os : Option String := unsafeCast (some (wrap "back" : W String))
  IO.println s!"{ow.map fun w => f64 w.x} {os}"
