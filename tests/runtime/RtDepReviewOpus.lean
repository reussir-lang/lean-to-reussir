/-! Runtime test: the probes of a review of lean2rr's handling of unknown
types (review of the dependent-type design, probes Any1, Conf, Drop,
Dyn, Fields and Layout; one namespace each, run in that order with the
program's arguments):
- Any1: a value whose type is a field of a structure; a type computed from
  a run-time `Bool`; an identity at a type argument;
- Conf: a function whose result is a type (no data) for one argument and
  data (`ULift Nat`) for the other, read at the data argument only;
- Drop: a function whose only argument is a proof, and a constant with the
  same body (both panic; neither runs here);
- Dyn: `Dynamic` values of a structure, a `Float` and a `String`, read
  back with `Dynamic.get?`;
- Fields: field types that are neither a type parameter nor concrete (an
  application of a type-former parameter, a type computed from another
  field, a heterogeneous list) and polymorphic recursion at `α × α`;
- Layout: a structure with scalar and boxed fields, a pair of `UInt64`s, a
  `List Float` and a `List UInt8`.
The probes Conf2, Conf3 and Conf4 (a local `let` whose one branch is a
type and whose other branch is data, then read as data) are not here: Lean's
compiled code gives another value than its kernel for them (100, the kernel
200), a difference that is not judged yet. -/

namespace Any1
-- A value whose type is a type *field* of a structure (existential package).
structure Box where
  α     : Type
  val   : α
  show' : α → String

-- A type computed from a run-time value.
def T : Bool → Type
  | true  => Nat
  | false => String

def pick : (b : Bool) → T b
  | true  => (42 : Nat)
  | false => "hello"

def showT : (b : Bool) → T b → String
  | true,  v => toString (show Nat from v)
  | false, v => (show String from v)

@[noinline] def mkBox (n : Nat) : Box :=
  if n % 2 == 0 then ⟨Nat, n * 10, toString⟩ else ⟨String, s!"odd{n}", id⟩

@[noinline] def myId (α : Type) (x : α) : α := x

@[noinline] def useBox (b : Box) : String := b.show' b.val

@[noinline] def usePick (b : Bool) : String := showT b (pick b)

def run (args : List String) : IO Unit := do
  let n := args.length          -- run-time value, unknown at compile time
  IO.println (useBox (mkBox n))
  IO.println (useBox (mkBox (n+1)))
  IO.println (usePick (n == 0))
  IO.println (usePick (n != 0))
  IO.println (myId Nat (n + 7))
end Any1

namespace Conf
-- One branch returns a type (erased), the other returns data.
def T2 : Bool → Type 1
  | true  => Type
  | false => ULift.{1} Nat

@[noinline] def h (b : Bool) : T2 b :=
  match b with
  | true  => Nat
  | false => ULift.up 5

@[noinline] def get (b : Bool) : Nat :=
  match b, h b with
  | false, v => (show ULift.{1} Nat from v).down
  | true,  _ => 0

def run (args : List String) : IO Unit :=
  IO.println (get (args.length == 7))
end Conf



namespace Drop
-- `withProof` takes only an erased argument (a proof); `asConst` is the same
-- body with that argument dropped.
def withProof (_h : True) : Nat := panic! "evaluated withProof"
def asConst : Nat := panic! "evaluated asConst"

def run (args : List String) : IO Unit := do
  if args.length == 99 then
    IO.println (withProof trivial + asConst)
  IO.println "main done"
end Drop

namespace Dyn
structure Pt where
  x : UInt64
  y : Float
  deriving TypeName

deriving instance TypeName for Float
deriving instance TypeName for String

@[noinline] def store (n : Nat) : Array Dynamic :=
  #[Dynamic.mk (Pt.mk n.toUInt64 2.5), Dynamic.mk (3.25 : Float), Dynamic.mk "str"]

def run (args : List String) : IO Unit := do
  let a := store args.length
  for d in a do
    match d.get? Pt, d.get? Float, d.get? String with
    | some p, _, _ => IO.println s!"Pt {p.x} {p.y}"
    | _, some f, _ => IO.println s!"Float {f}"
    | _, _, some s => IO.println s!"String {s}"
    | _, _, _      => IO.println "?"
end Dyn

namespace Fields
-- Field types that are neither "a type parameter" nor concrete.
structure Wrap (f : Type → Type) (α : Type) where
  val : f α                         -- application of a type-former parameter

structure Dep where
  b : Bool
  v : cond b Nat String             -- type computed from another field

inductive HList : List Type → Type 1 where
  | nil  : HList []
  | cons {α : Type} {αs : List Type} : α → HList αs → HList (α :: αs)   -- α is a constructor field, not a parameter

-- Polymorphic recursion: the type argument grows at run time (α, α×α, (α×α)×(α×α), ...);
-- no finite set of *instantiated* types covers it, only a finite set of layouts.
def deep {α : Type} [ToString α] (x : α) : Nat → String
  | 0   => toString x
  | n+1 => deep (x, x) n

@[noinline] def useAll (w : Wrap List Nat) (d : Dep) (h : HList [Nat, String]) : Nat :=
  let a := w.val.length
  let c := match d with
    | ⟨true, v⟩  => (show Nat from v)
    | ⟨false, v⟩ => (show String from v).length
  let e := match h with
    | .cons x _ => (show Nat from x)
  a + c + e

def run (args : List String) : IO Unit := do
  let n := args.length
  let d : Dep := if h : n == 0 then ⟨true, (10 : Nat)⟩ else ⟨false, ("abc" : String)⟩
  IO.println (useAll ⟨[1,2,3]⟩ d (.cons (n+100) (.cons "s" .nil)))
  IO.println (deep n (n+2))
end Fields

namespace Layout
structure P where
  a : UInt64     -- concrete scalar field
  b : Nat        -- concrete boxed field
  c : Float      -- concrete scalar field

@[noinline] def mkP (n : Nat) : P := ⟨n.toUInt64, n, n.toFloat⟩
@[noinline] def mkPair (n : Nat) : UInt64 × UInt64 := (n.toUInt64, n.toUInt64 + 1)
@[noinline] def mkList (n : Nat) : List Float := [n.toFloat]
@[noinline] def mkListU8 (n : Nat) : List UInt8 := [n.toUInt8]

def run (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{(mkP n).a} {(mkPair n).2} {mkList n} {mkListU8 n}"
end Layout

def main (args : List String) : IO Unit := do
  IO.println "-- Any1"; Any1.run args
  IO.println "-- Conf"; Conf.run args
  IO.println "-- Drop"; Drop.run args
  IO.println "-- Dyn"; Dyn.run args
  IO.println "-- Fields"; Fields.run args
  IO.println "-- Layout"; Layout.run args
