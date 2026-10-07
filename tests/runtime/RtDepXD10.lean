/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterF33T24G4`: Pairs of ['Nat', 'List Nat'] in an existential
- `D71TesterF33T24P`: Control for T24M63: the depth-64 value without a Box
  position
- `D71TesterT01`: Two Lean types with one Rust type (Char and UInt32 are
  both u32) boxed at one position
- `D71TesterT02`: ByteArray and Array UInt8 (both Vec<u8>?), FloatArray and
  Array Float, boxed at one position
- `D71TesterT02A`: ByteArray and Array UInt8 (both Vec<u8>?), FloatArray and
  Array Float, boxed at one position
- `D71TesterT02B`: ByteArray and Array UInt8 (both Vec<u8>?), FloatArray and
  Array Float, boxed at one position
- `D71TesterT03`: Two reduced types meet (heads differ: Nat against Bool) at
  a family result
- `D71TesterT04`: Two closed types differing below the head (List Nat
  against List String): Box at the element
- `D71TesterT05`: Occurs check (polymorphic recursion grow n (x, x))
- `D71TesterT06B`: A cast node in generic code (Nat read as UInt32, Bool
  read as Nat, a list read as a list)
- `D71TesterT07`: B2 open positions: a family field read under a refinement -/

namespace D71TesterF33T24G4
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [
    ⟨((n : Nat), (n : Nat))⟩,
    ⟨((n : Nat), ([n] : List Nat))⟩,
    ⟨(([n] : List Nat), (n : Nat))⟩,
    ⟨(([n] : List Nat), ([n] : List Nat))⟩]
  IO.println (xs.map (·.show))
end D71TesterF33T24G4

namespace D71TesterF33T24P
abbrev Deep := List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
instance : ToString Deep := ⟨fun x => s!"deep{x.length}"⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Deep := [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  IO.println [toString d, toString n]
end D71TesterF33T24P

namespace D71TesterT01
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  let xs : List AnyS := [⟨Char.ofNat (97 + n)⟩, ⟨(n.toUInt32 * 3)⟩, ⟨n⟩]
  IO.println (xs.map (·.show))
end D71TesterT01

namespace D71TesterT02
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
instance : ToString ByteArray := ⟨fun b => s!"BA{b.toList}"⟩
instance : ToString FloatArray := ⟨fun b => s!"FA{b.toList}"⟩
def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ba := (List.range n).foldl (fun b i => b.push i.toUInt8) ByteArray.empty
  let au : Array UInt8 := (List.range (n+1)).toArray.map (·.toUInt8)
  let fa := (List.range n).foldl (fun b i => b.push i.toFloat) FloatArray.empty
  let af : Array Float := (List.range (n+1)).toArray.map (·.toFloat)
  let xs : List AnyS := [⟨ba⟩, ⟨au⟩, ⟨fa⟩, ⟨af⟩]
  IO.println (xs.map (·.show))
end D71TesterT02

namespace D71TesterT02A
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
instance : ToString ByteArray := ⟨fun b => s!"BA{b.toList}"⟩
instance : ToString FloatArray := ⟨fun b => s!"FA{b.toList}"⟩
def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ba := (List.range n).foldl (fun b i => b.push i.toUInt8) ByteArray.empty
  let au : Array UInt8 := (List.range (n+1)).toArray.map (·.toUInt8)
  let fa := (List.range n).foldl (fun b i => b.push i.toFloat) FloatArray.empty
  let af : Array Float := (List.range (n+1)).toArray.map (·.toFloat)
  let xs : List AnyS := [⟨ba⟩, ⟨au⟩]
  IO.println (xs.map (·.show))
end D71TesterT02A

namespace D71TesterT02B
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
instance : ToString ByteArray := ⟨fun b => s!"BA{b.toList}"⟩
instance : ToString FloatArray := ⟨fun b => s!"FA{b.toList}"⟩
def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ba := (List.range n).foldl (fun b i => b.push i.toUInt8) ByteArray.empty
  let au : Array UInt8 := (List.range (n+1)).toArray.map (·.toUInt8)
  let fa := (List.range n).foldl (fun b i => b.push i.toFloat) FloatArray.empty
  let af : Array Float := (List.range (n+1)).toArray.map (·.toFloat)
  let xs : List AnyS := [⟨fa⟩, ⟨af⟩]
  IO.println (xs.map (·.show))
end D71TesterT02B

namespace D71TesterT03
@[noinline] def pick : (b : Bool) → Nat → (if b then Nat else Bool)
  | true, n => (n * 2 : Nat)
  | false, n => (n % 2 == 0 : Bool)
@[noinline] def useN (n : Nat) : Nat := let r : Nat := pick true n; r + 1
@[noinline] def useB (n : Nat) : Bool := let r : Bool := pick false n; !r
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  IO.println s!"{useN n} {useB n} {useN (n+1)} {useB (n+1)}"
end D71TesterT03

namespace D71TesterT04
def F : Bool → Type
  | true => List Nat
  | false => List String
def mk : (b : Bool) → Nat → F b
  | true, n => List.range n
  | false, n => (List.range n).map toString
def sumN (n : Nat) : Nat := (mk true n : List Nat).foldl (· + ·) 0
def catS (n : Nat) : String := String.intercalate "," (mk false n : List String)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 5
  IO.println s!"{sumN n} [{catS n}] {(mk true 0 : List Nat).length}"
end D71TesterT04

namespace D71TesterT05
def grow {α : Type} [ToString α] : Nat → α → String
  | 0, x => toString x
  | n+1, x => grow n (x, x)
def growLen {α : Type} : Nat → α → Nat
  | 0, _ => 1
  | n+1, x => 2 * growLen n (x, x)
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{grow n n} {grow n "a"} {growLen (n+2) ()}"
end D71TesterT05

namespace D71TesterT06B
unsafe def coerceU {α β : Type} [Inhabited β] (x : α) : β := unsafeCast x
@[implemented_by coerceU, noinline] def coerceS {α β : Type} [Inhabited β] (_ : α) : β := default
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  let u : UInt32 := coerceS n
  let k : Nat := coerceS (n % 2 == 0)
  let s : String := coerceS s!"s{n}"
  IO.println s!"{u} {k} {s}"
end D71TesterT06B

namespace D71TesterT07
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, _⟩ => 0
@[noinline] def sz : Pkg → Nat
  | ⟨true, _⟩ => 100
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def mkN (n : Nat) : Pkg := ⟨true, (n : Nat)⟩
@[noinline] def mkS (s : String) : Pkg := ⟨false, (s : String)⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 7
  let ps := [mkN n, mkS (toString (n * 1000)), mkN 0, mkS ""]
  IO.println s!"{ps.map rd} {ps.map sz}"
end D71TesterT07

def main : IO Unit := do
  IO.println "-- D71TesterF33T24G4"
  D71TesterF33T24G4.caseMain ["3"]
  IO.println "-- D71TesterF33T24P"
  D71TesterF33T24P.caseMain []
  IO.println "-- D71TesterT01"
  D71TesterT01.caseMain ["3"]
  IO.println "-- D71TesterT02"
  D71TesterT02.caseMain ["1"]
  IO.println "-- D71TesterT02A"
  D71TesterT02A.caseMain ["0"]
  IO.println "-- D71TesterT02B"
  D71TesterT02B.caseMain ["0"]
  IO.println "-- D71TesterT03"
  D71TesterT03.caseMain ["0"]
  IO.println "-- D71TesterT04"
  D71TesterT04.caseMain ["1"]
  IO.println "-- D71TesterT05"
  D71TesterT05.caseMain ["1"]
  IO.println "-- D71TesterT06B"
  D71TesterT06B.caseMain ["4"]
  IO.println "-- D71TesterT07"
  D71TesterT07.caseMain ["0"]
