/-! Runtime test (compact scalar arrays, hunt HARR2-01): common ways user
code takes arrays of scalars apart, each at its own storage kind: array
literal patterns (`UInt8`), `a = #[]` decisions (`UInt16`), derived
instances of a structure with array fields (`UInt32`, `UInt64`), and an
anonymous-constructor pattern `⟨xs⟩` (`Float`). Only the last one turned
its kind off (`f64 off: anon._l2r.0: Array Float meets Array lcAny`):
Lean's `toMono` made it a call of `Array.toList` at an unknown element
type. Now every kind stays on (RtCArrMatchPatterns.l2r-debug). -/
@[noinline] def lit (a : Array UInt8) : Nat :=
  match a with
  | #[] => 0
  | #[x] => x.toNat
  | #[x, y] => x.toNat * 256 + y.toNat
  | _ => a.size

@[noinline] def isNil (a : Array UInt16) : Bool := if a = #[] then true else (#[] = a)

structure Rec where
  xs : Array UInt32
  ys : Array UInt64
  deriving BEq, Hashable, Repr, DecidableEq, Inhabited

@[noinline] def anon (a : Array Float) : Nat := match a with | ⟨l⟩ => l.length

def main (args : List String) : IO Unit := do
  let n := args.length
  let a8 : Array UInt8 := (Array.range (n + 2)).map (·.toUInt8)
  let a16 : Array UInt16 := (Array.range n).map (·.toUInt16)
  let r1 : Rec := ⟨(Array.range (n + 3)).map (·.toUInt32), #[1, 2]⟩
  let r2 : Rec := { r1 with ys := r1.ys.push 3 }
  IO.println s!"{lit a8} {lit #[] } {isNil a16} {r1 == r2} {decide (r1 = r1)} {hash r1 != hash r2} {repr r2}"
  IO.println s!"{anon ((Array.range (n + 4)).map (·.toFloat))}"
