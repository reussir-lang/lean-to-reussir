/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71TesterT24A`: B3 guard: a variant type of depth 64 (List^63 Nat)
- `D71TesterT24B`: B3 guard: a variant type of depth 65 (List^64 Nat)
- `D71TesterT24C`: B3 guard: a variant type of 255 nodes (balanced tuple of
  128 Nats)
- `D71TesterT24D`: B3 guard: a variant type of 257 nodes (balanced tuple of
  129 Nats)
- `D71TesterT24I`: Control for T24G: the same 144 pair values without a Box
  position
- `D71TesterT24K40`: A variant type of depth 41
- `D71TesterT24K62`: A variant type of depth 63 -/


namespace D71TesterT24A
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24A

namespace D71TesterT24B
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24B

namespace D71TesterT24C
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Big := ((((((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))) × (((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))))) × (((((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))) × (((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))))))
instance : ToString Big := ⟨fun x => toString x.1.1.1.1⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Big := (((((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n))))), (((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))))), ((((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n))))), (((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))))))
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24C

namespace D71TesterT24D
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
abbrev Big := ((((((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))) × (((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))))) × (((((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))))) × (((((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))))) × (((((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (Nat))))))) × (((((((Nat) × (Nat))) × (((Nat) × (Nat))))) × (((((Nat) × (Nat))) × (((Nat) × (((Nat) × (Nat))))))))))))))))
instance : ToString Big := ⟨fun x => toString x.1.1.1.1⟩
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : Big := (((((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n))))), (((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))))), ((((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n))))), (((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, n)))), ((((n, n), (n, n)), ((n, n), (n, n))), (((n, n), (n, n)), ((n, n), (n, (n, n))))))))
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24D




namespace D71TesterT24I
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List String := [
    toString ((n : Nat), (n : Nat)),
    toString ((n : Nat), (n>2 : Bool)),
    toString ((n : Nat), (toString n : String)),
    toString ((n : Nat), (n.toUInt8 : UInt8)),
    toString ((n : Nat), (n.toUInt16 : UInt16)),
    toString ((n : Nat), (n.toUInt32 : UInt32)),
    toString ((n : Nat), (n.toUInt64 : UInt64)),
    toString ((n : Nat), (n.toFloat : Float)),
    toString ((n : Nat), ((n : Int) : Int)),
    toString ((n : Nat), (() : Unit)),
    toString ((n : Nat), (some n : Option Nat)),
    toString ((n : Nat), ([n] : List Nat)),
    toString ((n>2 : Bool), (n : Nat)),
    toString ((n>2 : Bool), (n>2 : Bool)),
    toString ((n>2 : Bool), (toString n : String)),
    toString ((n>2 : Bool), (n.toUInt8 : UInt8)),
    toString ((n>2 : Bool), (n.toUInt16 : UInt16)),
    toString ((n>2 : Bool), (n.toUInt32 : UInt32)),
    toString ((n>2 : Bool), (n.toUInt64 : UInt64)),
    toString ((n>2 : Bool), (n.toFloat : Float)),
    toString ((n>2 : Bool), ((n : Int) : Int)),
    toString ((n>2 : Bool), (() : Unit)),
    toString ((n>2 : Bool), (some n : Option Nat)),
    toString ((n>2 : Bool), ([n] : List Nat)),
    toString ((toString n : String), (n : Nat)),
    toString ((toString n : String), (n>2 : Bool)),
    toString ((toString n : String), (toString n : String)),
    toString ((toString n : String), (n.toUInt8 : UInt8)),
    toString ((toString n : String), (n.toUInt16 : UInt16)),
    toString ((toString n : String), (n.toUInt32 : UInt32)),
    toString ((toString n : String), (n.toUInt64 : UInt64)),
    toString ((toString n : String), (n.toFloat : Float)),
    toString ((toString n : String), ((n : Int) : Int)),
    toString ((toString n : String), (() : Unit)),
    toString ((toString n : String), (some n : Option Nat)),
    toString ((toString n : String), ([n] : List Nat)),
    toString ((n.toUInt8 : UInt8), (n : Nat)),
    toString ((n.toUInt8 : UInt8), (n>2 : Bool)),
    toString ((n.toUInt8 : UInt8), (toString n : String)),
    toString ((n.toUInt8 : UInt8), (n.toUInt8 : UInt8)),
    toString ((n.toUInt8 : UInt8), (n.toUInt16 : UInt16)),
    toString ((n.toUInt8 : UInt8), (n.toUInt32 : UInt32)),
    toString ((n.toUInt8 : UInt8), (n.toUInt64 : UInt64)),
    toString ((n.toUInt8 : UInt8), (n.toFloat : Float)),
    toString ((n.toUInt8 : UInt8), ((n : Int) : Int)),
    toString ((n.toUInt8 : UInt8), (() : Unit)),
    toString ((n.toUInt8 : UInt8), (some n : Option Nat)),
    toString ((n.toUInt8 : UInt8), ([n] : List Nat)),
    toString ((n.toUInt16 : UInt16), (n : Nat)),
    toString ((n.toUInt16 : UInt16), (n>2 : Bool)),
    toString ((n.toUInt16 : UInt16), (toString n : String)),
    toString ((n.toUInt16 : UInt16), (n.toUInt8 : UInt8)),
    toString ((n.toUInt16 : UInt16), (n.toUInt16 : UInt16)),
    toString ((n.toUInt16 : UInt16), (n.toUInt32 : UInt32)),
    toString ((n.toUInt16 : UInt16), (n.toUInt64 : UInt64)),
    toString ((n.toUInt16 : UInt16), (n.toFloat : Float)),
    toString ((n.toUInt16 : UInt16), ((n : Int) : Int)),
    toString ((n.toUInt16 : UInt16), (() : Unit)),
    toString ((n.toUInt16 : UInt16), (some n : Option Nat)),
    toString ((n.toUInt16 : UInt16), ([n] : List Nat)),
    toString ((n.toUInt32 : UInt32), (n : Nat)),
    toString ((n.toUInt32 : UInt32), (n>2 : Bool)),
    toString ((n.toUInt32 : UInt32), (toString n : String)),
    toString ((n.toUInt32 : UInt32), (n.toUInt8 : UInt8)),
    toString ((n.toUInt32 : UInt32), (n.toUInt16 : UInt16)),
    toString ((n.toUInt32 : UInt32), (n.toUInt32 : UInt32)),
    toString ((n.toUInt32 : UInt32), (n.toUInt64 : UInt64)),
    toString ((n.toUInt32 : UInt32), (n.toFloat : Float)),
    toString ((n.toUInt32 : UInt32), ((n : Int) : Int)),
    toString ((n.toUInt32 : UInt32), (() : Unit)),
    toString ((n.toUInt32 : UInt32), (some n : Option Nat)),
    toString ((n.toUInt32 : UInt32), ([n] : List Nat)),
    toString ((n.toUInt64 : UInt64), (n : Nat)),
    toString ((n.toUInt64 : UInt64), (n>2 : Bool)),
    toString ((n.toUInt64 : UInt64), (toString n : String)),
    toString ((n.toUInt64 : UInt64), (n.toUInt8 : UInt8)),
    toString ((n.toUInt64 : UInt64), (n.toUInt16 : UInt16)),
    toString ((n.toUInt64 : UInt64), (n.toUInt32 : UInt32)),
    toString ((n.toUInt64 : UInt64), (n.toUInt64 : UInt64)),
    toString ((n.toUInt64 : UInt64), (n.toFloat : Float)),
    toString ((n.toUInt64 : UInt64), ((n : Int) : Int)),
    toString ((n.toUInt64 : UInt64), (() : Unit)),
    toString ((n.toUInt64 : UInt64), (some n : Option Nat)),
    toString ((n.toUInt64 : UInt64), ([n] : List Nat)),
    toString ((n.toFloat : Float), (n : Nat)),
    toString ((n.toFloat : Float), (n>2 : Bool)),
    toString ((n.toFloat : Float), (toString n : String)),
    toString ((n.toFloat : Float), (n.toUInt8 : UInt8)),
    toString ((n.toFloat : Float), (n.toUInt16 : UInt16)),
    toString ((n.toFloat : Float), (n.toUInt32 : UInt32)),
    toString ((n.toFloat : Float), (n.toUInt64 : UInt64)),
    toString ((n.toFloat : Float), (n.toFloat : Float)),
    toString ((n.toFloat : Float), ((n : Int) : Int)),
    toString ((n.toFloat : Float), (() : Unit)),
    toString ((n.toFloat : Float), (some n : Option Nat)),
    toString ((n.toFloat : Float), ([n] : List Nat)),
    toString (((n : Int) : Int), (n : Nat)),
    toString (((n : Int) : Int), (n>2 : Bool)),
    toString (((n : Int) : Int), (toString n : String)),
    toString (((n : Int) : Int), (n.toUInt8 : UInt8)),
    toString (((n : Int) : Int), (n.toUInt16 : UInt16)),
    toString (((n : Int) : Int), (n.toUInt32 : UInt32)),
    toString (((n : Int) : Int), (n.toUInt64 : UInt64)),
    toString (((n : Int) : Int), (n.toFloat : Float)),
    toString (((n : Int) : Int), ((n : Int) : Int)),
    toString (((n : Int) : Int), (() : Unit)),
    toString (((n : Int) : Int), (some n : Option Nat)),
    toString (((n : Int) : Int), ([n] : List Nat)),
    toString ((() : Unit), (n : Nat)),
    toString ((() : Unit), (n>2 : Bool)),
    toString ((() : Unit), (toString n : String)),
    toString ((() : Unit), (n.toUInt8 : UInt8)),
    toString ((() : Unit), (n.toUInt16 : UInt16)),
    toString ((() : Unit), (n.toUInt32 : UInt32)),
    toString ((() : Unit), (n.toUInt64 : UInt64)),
    toString ((() : Unit), (n.toFloat : Float)),
    toString ((() : Unit), ((n : Int) : Int)),
    toString ((() : Unit), (() : Unit)),
    toString ((() : Unit), (some n : Option Nat)),
    toString ((() : Unit), ([n] : List Nat)),
    toString ((some n : Option Nat), (n : Nat)),
    toString ((some n : Option Nat), (n>2 : Bool)),
    toString ((some n : Option Nat), (toString n : String)),
    toString ((some n : Option Nat), (n.toUInt8 : UInt8)),
    toString ((some n : Option Nat), (n.toUInt16 : UInt16)),
    toString ((some n : Option Nat), (n.toUInt32 : UInt32)),
    toString ((some n : Option Nat), (n.toUInt64 : UInt64)),
    toString ((some n : Option Nat), (n.toFloat : Float)),
    toString ((some n : Option Nat), ((n : Int) : Int)),
    toString ((some n : Option Nat), (() : Unit)),
    toString ((some n : Option Nat), (some n : Option Nat)),
    toString ((some n : Option Nat), ([n] : List Nat)),
    toString (([n] : List Nat), (n : Nat)),
    toString (([n] : List Nat), (n>2 : Bool)),
    toString (([n] : List Nat), (toString n : String)),
    toString (([n] : List Nat), (n.toUInt8 : UInt8)),
    toString (([n] : List Nat), (n.toUInt16 : UInt16)),
    toString (([n] : List Nat), (n.toUInt32 : UInt32)),
    toString (([n] : List Nat), (n.toUInt64 : UInt64)),
    toString (([n] : List Nat), (n.toFloat : Float)),
    toString (([n] : List Nat), ((n : Int) : Int)),
    toString (([n] : List Nat), (() : Unit)),
    toString (([n] : List Nat), (some n : Option Nat)),
    toString (([n] : List Nat), ([n] : List Nat))]
  IO.println (xs.foldl (fun a s => a + s.length) 0)
end D71TesterT24I

namespace D71TesterT24K40
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat)))))))))))))))))))))))))))))))))))))))) := [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24K40

namespace D71TesterT24K62
structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let d : List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (List (Nat)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := [[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  let xs : List AnyS := [⟨d⟩, ⟨n⟩]
  IO.println ((xs.map (·.show)).map (·.length))
end D71TesterT24K62

def main : IO Unit := do
  IO.println "-- D71TesterT24A"
  D71TesterT24A.caseMain ["3"]
  IO.println "-- D71TesterT24B"
  D71TesterT24B.caseMain ["3"]
  IO.println "-- D71TesterT24C"
  D71TesterT24C.caseMain ["3"]
  IO.println "-- D71TesterT24D"
  D71TesterT24D.caseMain ["3"]
  IO.println "-- D71TesterT24I"
  D71TesterT24I.caseMain []
  IO.println "-- D71TesterT24K40"
  D71TesterT24K40.caseMain ["3"]
  IO.println "-- D71TesterT24K62"
  D71TesterT24K62.caseMain []
