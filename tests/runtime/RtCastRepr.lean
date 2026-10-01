/-! Runtime test: `unsafeCast` between types Lean represents alike (adv4
RP4-03 to RP4-07).
- Values held in a `Box` (existential payloads, `IO.Ref` contents,
  polymorphically recursive code) read at another such type: the unboxing
  function converts them (isomorphic inductives, words).
- Structures whose fields are in another declaration order but the same
  native layout (objects first, then scalars by decreasing size): fields
  correspond by layout; a `UInt64` field read as `Float` is its bits.
- `Nat`/`Int` and fixed-width scalars, `Bool`, enumerations, nullary
  constructors: Lean's `lean_box`/`lean_unbox` (truncation to the target's
  width, an index past the last constructor selects the last one, an `Int`
  read as a `Nat` is its 32 bits). Only cases where native results do not
  depend on addresses are printed.
- An array field of a cast value, read at the cast type, is the same array
  (no conversion per access). -/

inductive P1 | a | b (x : Nat) (y : P1)
inductive P2 | a | b (x : Nat) (y : P2)
inductive C3 | a | b | c deriving Repr
inductive L | nil | one | cons (x : Nat) (t : L)

structure Pkg where
  α : Type
  v : α

def C3.str : C3 → String | .a => "a" | .b => "b" | .c => "c"
def L.str : L → String | .nil => "nil" | .one => "one" | .cons x _ => s!"cons {x}"

@[noinline] unsafe def pkgHead (p : Pkg) : Nat := match (unsafeCast p.v : P2) with | .b x _ => x | .a => 7
@[noinline] unsafe def headVia (r : IO.Ref P1) : IO Nat := do
  match ← (unsafeCast r : IO.Ref P2).get with
  | .b x _ => return x
  | .a => return 0
@[noinline] unsafe def setVia (r : IO.Ref P1) (n : Nat) : IO Unit := (unsafeCast r : IO.Ref P2).set (.b n .a)
@[noinline] unsafe def headAt {α : Type} (x : α) (v : α) : Nat → Nat
  | 0 => match (unsafeCast v : P2) with | .b n _ => n | .a => 0
  | k+1 => headAt (x, x) (unsafeCast v) k
@[noinline] unsafe def asC3 (p : Pkg) : String := (unsafeCast p.v : C3).str
@[noinline] unsafe def asNat (p : Pkg) : Nat := (unsafeCast p.v : Nat) + 1
@[noinline] unsafe def asBool (p : Pkg) : Bool := (unsafeCast p.v : Bool)
@[noinline] unsafe def asU8 (p : Pkg) : UInt8 := (unsafeCast p.v : UInt8) + 1

structure S3 where
  a : UInt8
  b : Nat
structure S4 where
  x : Nat
  y : UInt8
structure S5 where
  a : UInt8
  f : Float
  n : Nat
  u : UInt32
structure S6 where
  m : Nat
  w : UInt64
  v : UInt32
  c : UInt8
@[noinline] unsafe def s3s4 (s : S3) : String := match (unsafeCast s : S4) with | ⟨x, y⟩ => s!"{x} {y}"
@[noinline] unsafe def s5s6 (s : S5) : String := match (unsafeCast s : S6) with | ⟨m, w, v, c⟩ => s!"{m} {w} {v} {c}"
@[noinline] unsafe def s6s5 (s : S6) : String := let t : S5 := unsafeCast s; s!"{t.a} {t.f} {t.n} {t.u}"

@[noinline] unsafe def natU8 (x : Nat) : UInt8 := unsafeCast x
@[noinline] unsafe def natU16 (x : Nat) : UInt16 := unsafeCast x
@[noinline] unsafe def natU32 (x : Nat) : UInt32 := unsafeCast x
@[noinline] unsafe def natChar (x : Nat) : Char := unsafeCast x
@[noinline] unsafe def natBool (x : Nat) : Bool := unsafeCast x
@[noinline] unsafe def natC3 (x : Nat) : C3 := unsafeCast x
@[noinline] unsafe def natInt (x : Nat) : Int := unsafeCast x
@[noinline] unsafe def intNat (x : Int) : Nat := unsafeCast x
@[noinline] unsafe def intU8 (x : Int) : UInt8 := unsafeCast x
@[noinline] unsafe def intU32 (x : Int) : UInt32 := unsafeCast x
@[noinline] unsafe def intBool (x : Int) : Bool := unsafeCast x
@[noinline] unsafe def intC3 (x : Int) : C3 := unsafeCast x
@[noinline] unsafe def u8Int (x : UInt8) : Int := unsafeCast x
@[noinline] unsafe def u32Int (x : UInt32) : Int := unsafeCast x
@[noinline] unsafe def c3Int (x : C3) : Int := unsafeCast x
@[noinline] unsafe def boolInt (x : Bool) : Int := unsafeCast x
@[noinline] unsafe def u32Nat (x : UInt32) : Nat := unsafeCast x
@[noinline] unsafe def u8C3 (x : UInt8) : C3 := unsafeCast x
@[noinline] unsafe def natL (x : Nat) : L := unsafeCast x
@[noinline] unsafe def lNat (x : L) : Nat := unsafeCast x
@[noinline] unsafe def c3L (x : C3) : L := unsafeCast x
@[noinline] unsafe def lC3 (x : L) : C3 := unsafeCast x
@[noinline] unsafe def natOpt (x : Nat) : String := match (unsafeCast x : Option Nat) with | none => "none" | some _ => "some"
@[noinline] unsafe def noneNat (o : Option Nat) : Nat := unsafeCast o

inductive T1 | node (v : Nat) (cs : Array T1)
inductive T2 | node (w : Nat) (ds : Array T2)
instance : Inhabited T2 := ⟨.node 0 #[]⟩
@[noinline] unsafe def kidVia (t : T1) (i : Nat) : Nat :=
  match (unsafeCast t : T2) with
  | .node _ ds => match ds[i]! with | .node w _ => w
@[noinline] unsafe def sizeVia (t : T1) : Nat := match (unsafeCast t : T2) with | .node _ ds => ds.size
@[noinline] unsafe def sameKids (t : T1) : Bool :=
  match t, (unsafeCast t : T2) with
  | .node _ cs, .node _ ds => ptrAddrUnsafe cs == ptrAddrUnsafe ds

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  -- Through a Box.
  let r ← IO.mkRef (P1.b (5 + k) .a)
  let h1 ← headVia r
  setVia r (40 + k)
  let h2 ← headVia r
  let back ← r.get
  IO.println s!"box {pkgHead ⟨P1, .b (5 + k) .a⟩} ref {h1} {h2} {match back with | .b x _ => x | .a => 0} polyrec {headAt P1.a (P1.b 4 .a) 0} {headAt P1.a (P1.b 5 .a) (2 + k)}"
  IO.println s!"box words {asC3 ⟨Nat, 2 + k⟩} {asNat ⟨C3, .b⟩} {asBool ⟨C3, .b⟩} {asU8 ⟨Bool, true⟩} {asC3 ⟨UInt8, (1 + k).toUInt8⟩} {asBool ⟨Nat, 1 + k⟩} {asNat ⟨Bool, true⟩} {asC3 ⟨Bool, false⟩}"
  -- Native layout order.
  IO.println s!"layout {s3s4 ⟨7, 1000 + k⟩} {s5s6 ⟨3, 2.0, 99 + k, 70000⟩} {s6s5 ⟨12 + k, 4611686018427387904, 9, 255⟩}"
  -- Words.
  IO.println s!"nat {natU8 (200 + k)} {natU8 (300 + k)} {natU8 (2 ^ 63 - 1 + k)} {natU16 (70000 + k)} {natU32 (2 ^ 32 + 7 + k)} {(natChar (97 + k)).toNat}"
  IO.println s!"bool {natBool (0 + k)} {natBool (2 + k)} {natBool (256 + k)} {intBool (0 + k)} {intBool (-1 + k)} {intBool (256 + k)}"
  IO.println s!"enum {repr (natC3 (1 + k))} {repr (natC3 (3 + k))} {repr (natC3 (257 + k))} {repr (intC3 (-1 + k))} {repr (u8C3 (5 + k.toUInt8))}"
  IO.println s!"int {natInt (3 + k)} {natInt (2 ^ 70 + k)} {intNat (3 + k)} {intNat (-5 + k)} {intNat (2 ^ 40 + k)} {intNat (-(2 ^ 40) + k)} {intU8 (300 + k)} {intU8 (-1 + k)} {intU32 (-1 + k)}"
  IO.println s!"toint {u8Int (200 + k.toUInt8)} {u32Int (0xFFFFFFFF - k.toUInt32)} {u32Int (2 ^ 31 + k.toUInt32)} {c3Int C3.c} {boolInt true} {u32Nat (0xFFFFFFFF - k.toUInt32)}"
  IO.println s!"nullary {(natL (0 + k)).str} {(natL (1 + k)).str} {lNat L.nil} {lNat L.one} {(c3L C3.b).str} {repr (lC3 L.one)} {natOpt (0 + k)} {noneNat none}"
  -- An array field read at the cast type: the same array.
  let t := T1.node 0 ((Array.range (1000 + k)).map fun i => .node i #[])
  let mut s := 0
  for i in [0:20000] do s := s + kidVia t (i % 1000)
  IO.println s!"array {s} {sizeVia t} {sameKids t}"
