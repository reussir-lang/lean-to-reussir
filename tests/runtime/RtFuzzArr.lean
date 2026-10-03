/-! Runtime test: 6000 random array operations (fixed LCG seed) over pools of
shared versions, for 8 element representations (tagged `Nat`/`Int` words,
`String`, `Float`, `UInt8`, `Array Nat`, `Nat × String`, `Option UInt64`):
push/pop/set!/swapIfInBounds/extract/++/reverse/insertIdxIfInBounds/
eraseIdxIfInBounds/modify/take/zip-then-map/filter/replicate.
From the round-7 review, area D (rv7/rtdata), check DFuzzArr. Operation 11,
`(a.zip b).map (·.1)`, a projection map over a parametric structure, is
where every divergence of finding RV7D-01 showed (zeros, empty strings or
"INTERNAL PANIC: unreachable code has been reached"; fixed by e318fbd and
a9b89e6). -/

-- Random sequences of array operations over pools of shared versions, for
-- several element representations (tagged Nat/Int words, strings, floats,
-- bytes, nested arrays, pairs).
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def vals : Array Nat := #[0, 1, 2^62 - 1, 2^62, 2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^100, 7, 12345]

class Gen (α : Type) where
  gen : Nat → α
  dig : α → UInt64

instance : Gen Nat := ⟨fun k => vals[k % vals.size]! + k / vals.size, fun n => hash n⟩
instance : Gen Int := ⟨fun k => if k % 2 == 0 then (vals[k % vals.size]! : Int) else -(vals[k % vals.size]! : Int) - 1, fun n => hash n⟩
instance : Gen String := ⟨fun k => s!"s{k}é", fun s => hash s⟩
instance : Gen Float := ⟨fun k => k.toFloat / 3.0, fun f => f.toBits⟩
instance : Gen UInt8 := ⟨fun k => k.toUInt8, fun u => u.toUInt64⟩
instance : Gen (Array Nat) := ⟨fun k => #[k, 2^65 + k], fun a => a.foldl (fun h x => mixHash h (hash x)) 3⟩
instance : Gen (Nat × String) := ⟨fun k => (2^64 + k, toString k), fun (a, b) => mixHash (hash a) (hash b)⟩
instance : Gen (Option UInt64) := ⟨fun k => if k % 3 == 0 then none else some k.toUInt64, fun o => match o with | none => 99 | some v => v⟩

def digest {α} [Gen α] (p : Array (Array α)) : UInt64 :=
  p.foldl (fun h a => a.foldl (fun h x => mixHash h (Gen.dig x)) (mixHash h a.size.toUInt64)) 17

def run (α : Type) [Gen α] [Inhabited α] (lbl : String) (seed0 : UInt64) : IO Unit := do
  let mut seed := seed0
  let mut pool : Array (Array α) := #[#[], #[Gen.gen 1], (List.range 5).toArray.map Gen.gen, #[Gen.gen 9, Gen.gen 10], Array.emptyWithCapacity 3]
  for n in [0:6000] do
    let mut r : Array Nat := #[]
    for _ in [0:6] do
      seed := lcg seed
      r := r.push (seed >>> 33).toNat
    let op := r[0]! % 15
    let a := pool[r[1]! % pool.size]!
    let b := pool[r[2]! % pool.size]!
    let k := r[3]! % pool.size
    let i := r[4]! % 8
    let x : α := Gen.gen r[5]!
    let res : Array α := match op with
      | 0 => a.push x
      | 1 => a.pop
      | 2 => a.set! i x
      | 3 => a.swapIfInBounds i (r[5]! % 8)
      | 4 => a.extract i (r[5]! % 9)
      | 5 => a ++ b
      | 6 => a.reverse
      | 7 => a.insertIdxIfInBounds i x
      | 8 => a.eraseIdxIfInBounds i
      | 9 => a.modify i (fun _ => x)
      | 10 => a.take i
      | 11 => (a.zip b).map (·.1)
      | 12 => a.filter (fun y => Gen.dig y % 2 == 0)
      | 13 => (Array.replicate (i % 4) x) ++ a
      | _ => a.extract (r[5]! % 9) i
    let res := if res.size > 40 then res.extract 0 10 else res
    pool := pool.set! k res
    if n % 1000 == 0 then IO.println s!"{lbl} {n} {digest pool} {pool.map Array.size}"
  IO.println s!"{lbl} final {digest pool}"

def main : IO Unit := do
  run Nat "nat" 1
  run Int "int" 2
  run String "str" 3
  run Float "flt" 4
  run UInt8 "u8" 5
  run (Array Nat) "nest" 6
  run (Nat × String) "pair" 7
  run (Option UInt64) "opt" 8

