/-! Runtime test: `unsafeCast` of values held in a `Box` (existential
payloads), and casts that natively read an address (plan §5.1, §10).
- `N`: constructors without fields and words, both natively `lean_box(i)`:
  `[]`/`none`/`Unit` read as `Nat`, `UInt8`, `Bool` or an enumeration, a
  word read as `List`/`Option`, a nullary constructor of one inductive read
  as another's.
- `L`: inductives that Lean lays out alike whose lean2rr layouts differ
  (field declaration order, `Float`/`UInt64` bits, `Nat`/`Int` fields,
  `Bool`/`UInt8`/enumeration scalars, lists of other element types):
  converted constructor by constructor through the target's layout.
- `T`: typed casts between inductives that do not correspond constructor
  for constructor (another number of constructors): by tag, as Lean's
  `cases` reads them.
- `A`: objects read as narrow words (natively bits of an address; lean2rr
  a deterministic word): only results that hold for every address are
  printed, and nothing may panic. -/

namespace N
structure Pkg where
  α : Type
  v : α

inductive C3 | a | b | c

@[noinline] unsafe def asNat (p : Pkg) : Nat := unsafeCast p.v
@[noinline] unsafe def asU8 (p : Pkg) : UInt8 := unsafeCast p.v
@[noinline] unsafe def asBool (p : Pkg) : Bool := unsafeCast p.v
@[noinline] unsafe def asC3 (p : Pkg) : C3 := unsafeCast p.v
@[noinline] unsafe def asListS (p : Pkg) : String := match (unsafeCast p.v : List Nat) with
  | [] => "nil" | _ :: _ => "cons"
@[noinline] unsafe def asOptS (p : Pkg) : String := match (unsafeCast p.v : Option String) with
  | none => "none" | some s => s!"some {s}"
@[noinline] unsafe def asOrd (p : Pkg) : Ordering := unsafeCast p.v

def c3s : C3 → String | .a => "a" | .b => "b" | .c => "c"

end N

namespace L
structure Pkg where
  α : Type
  v : α

inductive Q1 | a | b (x : UInt8) (y : Nat) (r : Q1)
inductive Q2 | a | b (y : Nat) (r : Q2) (x : UInt8)

structure S1 where
  a : UInt8
  b : String
  c : UInt32
structure S2 where
  s : String
  w : UInt32
  t : UInt8

inductive P1 | a | b (x : Nat) (y : P1)
inductive P2 | a | b (x : Nat) (y : P2)

structure W1 where
  f : Float
  n : Nat
structure W2 where
  n : Nat
  bits : UInt64

inductive E1 | a | b (x : Nat) (y : E1)
inductive E3 | a | b (x : Int) (y : E3)
structure B1 where
  flag : Bool
  c : UInt8
  n : Nat
inductive C3 | a | b | c
structure B2 where
  n : Nat
  k : UInt8
  col : C3
structure U where
  n : Nat
structure V1 where
  u : U
  s : String
structure V2 where
  n : Nat
  s : String
structure R1 where
  l : List Nat
  o : Option Nat
structure R2 where
  l : List Int
  o : Option Int

def Q2.sum : Q2 → Nat
  | .a => 0
  | .b y r x => y + x.toNat * 1000 + r.sum

@[noinline] unsafe def asQ2 (p : Pkg) : Nat := (unsafeCast p.v : Q2).sum
@[noinline] unsafe def asS2 (p : Pkg) : String := match (unsafeCast p.v : S2) with
  | ⟨s, w, t⟩ => s!"{s} {w} {t}"
@[noinline] unsafe def asP2 (p : Pkg) : Nat := match (unsafeCast p.v : P2) with
  | .b x _ => x | .a => 7
@[noinline] unsafe def asOptP2 (p : Pkg) : Nat := match (unsafeCast p.v : Option P2) with
  | some (.b x _) => x | some .a => 8 | none => 9
@[noinline] unsafe def asW2 (p : Pkg) : String := match (unsafeCast p.v : W2) with
  | ⟨n, b⟩ => s!"{n} {b}"
@[noinline] unsafe def asListP2 (p : Pkg) : Nat := (unsafeCast p.v : List P2).foldl (fun acc q => match q with | .b x _ => acc + x | .a => acc + 100) 0

def c3s : C3 → String | .a => "a" | .b => "b" | .c => "c"
def E3.sum : E3 → Int
  | .a => 0
  | .b x y => x + y.sum
@[noinline] unsafe def asE3 (p : Pkg) : Int := (unsafeCast p.v : E3).sum
@[noinline] unsafe def asB2 (p : Pkg) : String := match (unsafeCast p.v : B2) with
  | ⟨n, k, col⟩ => s!"{n} {k} {c3s col}"
@[noinline] unsafe def asV2 (p : Pkg) : String := match (unsafeCast p.v : V2) with
  | ⟨n, s⟩ => s!"{n} {s}"
@[noinline] unsafe def asR2 (p : Pkg) : String := match (unsafeCast p.v : R2) with
  | ⟨l, o⟩ => s!"{l} {o}"

end L

namespace T
inductive Sum3 | a | b (x : Nat) | c (y : String)
inductive Pair2 | mk (x : Nat) (y : String)
@[noinline] unsafe def tOptN (s : Sum3) : String := match (unsafeCast s : Option Nat) with
  | none => "none" | some n => s!"some {n}"
@[noinline] unsafe def tOptS (s : Sum3) : String := match (unsafeCast s : Option String) with
  | none => "none" | some s => s!"some {s}"
@[noinline] unsafe def tPairOpt (s : Pair2) : String := match (unsafeCast s : Option Nat) with
  | none => "none" | some n => s!"some {n}"
end T

namespace A
structure Pkg where
  α : Type
  v : α

inductive C3 | a | b | c

structure S where
  x : Nat
  y : String

@[noinline] unsafe def usz {α : Type} (x : α) : USize := unsafeCast x
@[noinline] unsafe def u8 {α : Type} (x : α) : UInt8 := unsafeCast x
@[noinline] unsafe def c3 {α : Type} (x : α) : C3 := unsafeCast x
@[noinline] unsafe def bUsz (p : Pkg) : USize := unsafeCast p.v
@[noinline] unsafe def bU8 (p : Pkg) : UInt8 := unsafeCast p.v
@[noinline] unsafe def bC3 (p : Pkg) : C3 := unsafeCast p.v
@[noinline] unsafe def bU32 (p : Pkg) : UInt32 := unsafeCast p.v

def objWord (w : USize) : Bool := w != 0 && w % 4 == 0 && w > 4096
def anyC3 : C3 → Bool | .a => true | .b => true | .c => true

end A

open N in
unsafe def runN (k : Nat) : IO Unit := do
  IO.println s!"01 nil as Nat {asNat ⟨List Nat, List.replicate k 1⟩}"
  IO.println s!"02 none as Nat {asNat ⟨Option Nat, if k > 5 then some 1 else none⟩}"
  IO.println s!"03 none as U8 {asU8 ⟨Option String, none⟩} as Bool {asBool ⟨Option Nat, none⟩}"
  IO.println s!"04 0 as List {asListS ⟨Nat, k⟩}"
  IO.println s!"05 0 as Option {asOptS ⟨Nat, k⟩} false as Option {asOptS ⟨Bool, k > 3⟩}"
  IO.println s!"06 nil as Option {asOptS ⟨List Nat, []⟩}"
  IO.println s!"07 none as C3 {c3s (asC3 ⟨Option Nat, none⟩)} C3.b as Nat {asNat ⟨C3, C3.b⟩}"
  IO.println s!"08 Ordering.gt as Nat {asNat ⟨Ordering, .gt⟩} 1 as Ordering {repr (asOrd ⟨Nat, 1 + k⟩)}"
  IO.println s!"09 unit as Nat {asNat ⟨Unit, ()⟩} as List {asListS ⟨Unit, ()⟩}"

open L in
unsafe def runL (k : Nat) : IO Unit := do
  IO.println s!"L01 Q1 as Q2 {asQ2 ⟨Q1, .b 3 (40 + k) (.b 5 6 .a)⟩}"
  IO.println s!"L02 S1 as S2 {asS2 ⟨S1, ⟨7, "str", 70000⟩⟩}"
  IO.println s!"L03 P1 as P2 {asP2 ⟨P1, .b (5 + k) .a⟩}"
  IO.println s!"L04 Option P1 as Option P2 {asOptP2 ⟨Option P1, some (.b (6 + k) .a)⟩}"
  IO.println s!"L05 W1 as W2 {asW2 ⟨W1, ⟨2.0, 11 + k⟩⟩}"
  IO.println s!"L06 List P1 as List P2 {asListP2 ⟨List P1, [.b 1 .a, .a, .b (2 + k) .a]⟩}"
  IO.println s!"L07 E1 as E3 {asE3 ⟨E1, .b (3 + k) (.b 4 .a)⟩}"
  IO.println s!"L08 B1 as B2 {asB2 ⟨B1, ⟨true, 2, 9 + k⟩⟩}"
  IO.println s!"L09 V1 as V2 {asV2 ⟨V1, ⟨⟨5 + k⟩, "v"⟩⟩}"
  IO.println s!"L10 R1 as R2 {asR2 ⟨R1, ⟨[1, 2 + k], some 3⟩⟩}"

open T in
unsafe def runT (k : Nat) : IO Unit := do
  IO.println s!"T01 typed {tOptN .a} {tOptN (.b (6 + k))} {tOptS (.c "t")} {tPairOpt (.mk 4 "r")}"

open A in
unsafe def runA (k : Nat) : IO Unit := do
  let s : S := ⟨k, "s"⟩
  IO.println s!"A03 typed narrow {decide ((u8 (some k)).toNat < 256)} {anyC3 (c3 s)} {decide ((u8 (2 ^ 70 + k)).toNat < 256)} {anyC3 (c3 (2 ^ 80 + k))}"
  IO.println s!"A05 boxed narrow {decide ((bU8 ⟨S, s⟩).toNat < 256)} {anyC3 (bC3 ⟨List Nat, [k]⟩)} {decide ((bU8 ⟨Nat, 2 ^ 70 + k⟩).toNat < 256)} {decide ((bU32 ⟨Int, -(2 ^ 70 : Int) - k⟩).toNat < 2 ^ 32)}"

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  runN k
  runL k
  runT k
  runA k
