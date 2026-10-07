import Std.Data.HashMap
import Std.Data.HashSet
/-! Runtime test: the unsafe casts of Lean's library and of user code, where
native Lean defines the result (no read of another type's memory):
- `Array.map`, `Array.mapM` (in `Id`, `Option`, `Except` and `IO`),
  `Array.mapIdx` and `Array.mapFinIdx` whose element type changes (the
  library maps in place through `NonScalar` when the array is unique), at
  boxed and unboxed element types, on unique and shared arrays;
- `Array.modify` (the library puts a placeholder, `unsafeCast ()`, in the
  slot while the function runs) at `Float`, `UInt64`, `String` and lists;
- `List.attach`, `Array.attach`, `List.unattach`, `Array.pmap` (casts
  between `α` and `{x // p x}`);
- `ShareCommon.shareCommon'` and a `ShareCommon.State` built from a user
  factory (its maps hold `NonScalar` objects), on values with repeated
  parts: only the values are printed;
- `NonScalar` in user code: values of several types cast to `NonScalar`,
  stored in an array, and cast back to their own types;
- the unit value read as a `Nat` (natively `box(0)`, so 0), and a `Fin`
  and a `Subtype` read as `Nat` (the same representation).
Argument: N (default 20). -/

structure P where
  a : Nat
  s : String
  deriving Repr

@[noinline] def toStrs (a : Array Nat) : Array String := a.map toString
@[noinline] def toFloats (a : Array Nat) : Array Float := a.map (·.toFloat * 0.5)
@[noinline] def toU64 (a : Array Float) : Array UInt64 := a.map (·.toUInt64 + 18446744073709551000)
@[noinline] def toPairs (a : Array UInt64) : Array (UInt64 × Nat) := a.map fun u => (u, u.toNat + 1)
@[noinline] def toP (a : Array String) : Array P := a.mapIdx fun i s => ⟨i, s⟩
@[noinline] def toFin (a : Array Nat) : Array String := a.mapFinIdx fun i x _ => s!"{i}:{x}"
@[noinline] def toOpt (a : Array Nat) : Option (Array Float) :=
  a.mapM fun x => if x < 1000 then some (x.toFloat + 0.25) else none
@[noinline] def toExc (a : Array Nat) : Except String (Array (List Nat)) :=
  a.mapM fun x => if x == 13 then throw "thirteen" else pure (List.range (x % 3))
@[noinline] def toClos (a : Array Nat) : Array (Nat → Nat) := a.map fun x => (· * x)

def f64s (a : Array Float) : String := toString (a.map Float.toBits)

@[noinline] def modifyAll (n : Nat) : String :=
  let fl : Array Float := (Array.range n).map (·.toFloat)
  let fl := (List.range n).foldl (fun a i => a.modify i (· * 3)) fl
  let us : Array UInt64 := (Array.range n).map fun i => i.toUInt64 + 18446744073709551000
  let us := (List.range n).foldl (fun a i => a.modify i (· + 7)) us
  let ss : Array String := (Array.range n).map toString
  let ss := (List.range n).foldl (fun a i => a.modify i (· ++ "!")) ss
  let ls : Array (List Nat) := (Array.range n).map List.range
  let ls := (List.range n).foldl (fun a i => a.modify i (i :: ·)) ls
  s!"{f64s fl} {us} {ss} {ls.map (·.length)}"

def sharedParts (n : Nat) : List (List Nat) :=
  (List.range n).map fun i => List.range (i % 4)

def builder : ShareCommon.StateFactoryBuilder where
  Map α β _ _ := Std.HashMap α β
  mkMap n := Std.HashMap.emptyWithCapacity n
  mapFind? m k := m.get? k
  mapInsert m k v := m.insert k v
  Set α _ _ := Std.HashSet α
  mkSet n := Std.HashSet.emptyWithCapacity n
  setFind? s a := s.get? a
  setInsert s a := s.insert a

def factory : ShareCommon.StateFactory := .mk builder

@[noinline] def shareAll (n : Nat) : List (List Nat) × Array String :=
  ShareCommonM.run (σ := factory) do
    let a ← shareCommonM (sharedParts n)
    let b ← shareCommonM ((Array.range n).map fun i => toString (i % 3))
    return (a, b)

@[noinline] unsafe def nonScalars (n : Nat) : Array NonScalar :=
  #[unsafeCast (List.range n), unsafeCast s!"str{n}", unsafeCast (#[n, n + 1] : Array Nat),
    unsafeCast (P.mk n "p"), unsafeCast (2 ^ 70 + n : Nat)]

@[noinline] unsafe def readNonScalars (a : Array NonScalar) : String :=
  match a.toList with
  | [l, s, arr, p, big] =>
    let l : List Nat := unsafeCast l
    let s : String := unsafeCast s
    let arr : Array Nat := unsafeCast arr
    let p : P := unsafeCast p
    let big : Nat := unsafeCast big
    s!"{l.length} {s} {arr} {p.a} {p.s} {big}"
  | _ => "?"

structure Pkg where
  α : Type
  v : α

@[noinline] unsafe def asNat (p : Pkg) : Nat := unsafeCast p.v

def main (args : List String) : IO Unit := do
  let n := (args.headD "20").toNat!
  let a := Array.range n
  -- unique arrays, mapped in place
  IO.println (toStrs (Array.range n))
  IO.println (f64s (toFloats (Array.range n)))
  IO.println (toPairs (toU64 (toFloats (Array.range n))))
  IO.println (repr (toP (toStrs (Array.range 4))))
  IO.println (toFin (Array.range 5))
  -- shared arrays: the source is used again afterwards
  IO.println s!"{toStrs a} {a.size}"
  IO.println s!"{(toOpt a).map f64s} {(toOpt (a.push 5000)).isSome}"
  IO.println s!"{repr (toExc a)}"
  IO.println s!"{repr (toExc (a.filter (· != 13)))}"
  IO.println s!"{(toClos a).map (· 3)} {a}"
  let io ← a.mapM fun x => do return (x * x : Nat).toFloat
  IO.println (f64s io)
  IO.println (modifyAll n)
  -- attach and unattach
  let l := List.range n
  IO.println s!"{l.attach.map (·.val + 1)} {(a.attach.map fun x => x.val * 2).size}"
  IO.println s!"{(l.attach.map fun x => (⟨x.val + 1, by omega⟩ : { y // y > 0 })).unattach}"
  IO.println s!"{(Array.range n).pmap (fun x (h : x < n) => (⟨x, h⟩ : Fin n).val + 100) (fun x hx => by simpa using hx)}"
  -- ShareCommon
  let parts := sharedParts n
  IO.println s!"{ShareCommon.shareCommon' parts == parts} {(ShareCommon.shareCommon' parts).length}"
  let (sa, sb) := shareAll n
  IO.println s!"{sa == sharedParts n} {sa.map (·.length)} {sb}"
  -- NonScalar, the unit value as a Nat, Fin and Subtype as Nat
  IO.println (unsafe readNonScalars (unsafe nonScalars n))
  IO.println (unsafe asNat ⟨Unit, ()⟩)
  IO.println (unsafe asNat ⟨Fin (n + 1), ⟨n, by omega⟩⟩)
  IO.println (unsafe asNat ⟨{ x : Nat // x > 2 }, ⟨n + 3, by omega⟩⟩)
  IO.println (unsafe asNat ⟨PUnit.{1}, PUnit.unit⟩)
