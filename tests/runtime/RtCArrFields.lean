/-! Runtime test (compact scalar arrays): a field `Array α` of an inductive
that the program also uses with a compact array is a box
(docs/implementation/representations/compact-arrays.md, "A field `Array α`
of an inductive used with a compact array is a box"). `Subarray UInt64`
values built, kept in a list and read by a function that is not inlined;
a subarray of an array updated afterwards (copy on write); a
`Vector UInt16` (a structure with one field) set and read; a user structure
`Col α` with a field `Array α` at `Float` (compact) and at `Nat` (boxes),
and a `Subarray Nat` beside the `Subarray UInt64` (one layout, the field a
box holding either array). Argument: k (default 6). -/
structure Col (α : Type) where
  data : Array α
  name : String

@[noinline] def sumSub (s : Subarray UInt64) : UInt64 := s.foldl (· + ·) 0
@[noinline] def mkSubs (a : Array UInt64) (k : Nat) : List (Subarray UInt64) :=
  (List.range k).map fun i => a[i:i+3]
@[noinline] def vecSum (v : Vector UInt16 n) : Nat := v.toArray.foldl (fun s x => s + x.toNat) 0
@[noinline] def vecBump (v : Vector UInt16 n) (i : Fin n) : Vector UInt16 n := v.set i (v[i] + 1)
@[noinline] def colPush (c : Col Float) (x : Float) : Col Float := { c with data := c.data.push x }
@[noinline] def colNat (c : Col Nat) : Nat := c.data.foldl (· + ·) 0
@[noinline] def subNat (s : Subarray Nat) : Nat := s.foldl (· + ·) 0

def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 6
  let a : Array UInt64 := (Array.range (k + 4)).map fun i => i.toUInt64 * 0x8000000000000001
  let subs := mkSubs a k
  IO.println s!"subs {subs.map sumSub} {subs.map (·.size)} {(subs.map (·.toArray.toList)).take 2}"
  let s0 := a.toSubarray 1 4
  let a2 := a.set! 2 7
  IO.println s!"sub shared {sumSub s0} {s0.toArray.toList} {a2[2]!} {sumSub (a2.toSubarray 1 4)}"
  let v : Vector UInt16 4 := ⟨#[1, 2, 65535, 4], rfl⟩
  let v2 := vecBump v ⟨2, by decide⟩
  IO.println s!"vector {vecSum v} {vecSum v2} {v2.toArray.toList} {v.toArray.toList}"
  let mut c : Col Float := ⟨#[], "f"⟩
  for i in [0:k] do c := colPush c (i.toFloat / 2)
  IO.println s!"col {c.data.toList} {c.name} {colNat ⟨#[1, 2, 3], "n"⟩} {subNat (#[5, 6, 7, 8][1:3])}"
