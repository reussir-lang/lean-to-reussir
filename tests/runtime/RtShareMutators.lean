/-! Runtime test: array mutators with the old array observed afterwards. 18
mutators (set!, push, swap, pop, modify, set, uset, swap with proofs,
reverse, ++, insertIdx, eraseIdx, extract, filter, mapIdx, zipWith, ...) on a
shared array at 24 element representations (small/big Nat, Int, UInt8/64,
Int8, USize, Float, Float32, Bool, Char, String, Unit, an enumeration,
Ordering, Option, pairs, one-field and scalar structures, closures, nested
arrays, Fin, List, ByteArray); ByteArray copySlice/uset/append/extract,
FloatArray uset/push/set!, String pushn/append/set/modify/map/join on shared
values.
From the round-7 review, area L (rv7/lowering), check 2 (LwShare2). -/

structure W where
  v : Nat
  deriving Inhabited, Repr

instance : ToString W := ⟨fun w => s!"W{w.v}"⟩

structure P2 where
  a : UInt8
  b : Float
  deriving Inhabited

instance : ToString P2 := ⟨fun p => s!"P({p.a},{p.b})"⟩

inductive E | e1 | e2 | e3
  deriving Inhabited, Repr

instance : ToString E := ⟨fun e => match e with | .e1 => "e1" | .e2 => "e2" | .e3 => "e3"⟩

structure Fn where
  f : Nat → Nat

instance : Inhabited Fn := ⟨⟨id⟩⟩
instance : ToString Fn := ⟨fun f => s!"F{f.f 1}"⟩

instance : ToString Ordering := ⟨fun o => match o with | .lt => "lt" | .eq => "eq" | .gt => "gt"⟩

def shareTest {α} [ToString α] [Inhabited α] (label : String) (a : Array α) (x y : α) : IO Unit := do
  let b := a.set! 0 x
  let c := a.push y
  let d := a.swapIfInBounds 0 1
  let e := a.pop
  let f := a.modify 1 (fun _ => x)
  let g := if h : 1 < a.size then a.set 1 y h else a
  let h := if h : (0 : USize).toNat < a.size then a.uset 0 y h else a
  let i := if h : 0 < a.size ∧ 1 < a.size then a.swap 0 1 h.1 h.2 else a
  let j := a.reverse
  let k := a ++ #[x, y]
  let l := a.insertIdxIfInBounds 1 x
  let m := a.eraseIdxIfInBounds 0
  let n := a.extract 1 2
  let o := (a.set! 0 x).set! 1 y
  let p := a.filter (fun _ => true)
  let q := a.mapIdx (fun i v => if i == 0 then x else v)
  let r := a.zipWith (fun u _ => u) a
  IO.println s!"{label}: {a} | {b} {c} {d} {e} {f} {g} {h} {i} {j} {k} {l} {m} {n} {o} {p} {q} {r} | {a}"

@[noinline] def mkArr {α} (xs : List α) : Array α := xs.toArray

def main : IO Unit := do
  shareTest "nat" (mkArr [1, 2, 3]) 10 20
  shareTest "bignat" (mkArr [2^64, 2^63, 2^70]) (2^65) (2^100)
  shareTest "int" (mkArr [(-1 : Int), -2^63, 2^64]) (-5) (2^63)
  shareTest "u8" (mkArr [(1 : UInt8), 2, 3]) 10 20
  shareTest "u64" (mkArr [(1 : UInt64), 2, 3]) 10 20
  shareTest "i8" (mkArr [(-1 : Int8), 2, 3]) (-10) 20
  shareTest "usize" (mkArr [(1 : USize), 2, 3]) 10 20
  shareTest "float" (mkArr [(1.5 : Float), 2, 3]) 10 20
  shareTest "f32" (mkArr [(1.5 : Float32), 2, 3]) 10 20
  shareTest "bool" (mkArr [true, false, true]) false true
  shareTest "char" (mkArr ['a', 'b', 'c']) 'x' 'y'
  shareTest "str" (mkArr ["a", "b", "c"]) "x" "y"
  shareTest "unit" (mkArr [(), (), ()]) () ()
  shareTest "enum" (mkArr [E.e1, .e2, .e3]) .e3 .e1
  shareTest "ord" (mkArr [Ordering.lt, .eq, .gt]) .gt .lt
  shareTest "opt" (mkArr [some 1, none, some 3]) none (some 9)
  shareTest "pair" (mkArr [(1, "a"), (2, "b"), (3, "c")]) (9, "x") (8, "y")
  shareTest "w" (mkArr [W.mk 1, W.mk 2, W.mk 3]) (W.mk 9) (W.mk 8)
  shareTest "p2" (mkArr [P2.mk 1 1.5, P2.mk 2 2.5, P2.mk 3 3.5]) (P2.mk 9 9.5) (P2.mk 8 8.5)
  shareTest "fn" (mkArr [Fn.mk (· + 1), Fn.mk (· * 2), Fn.mk id]) (Fn.mk (· + 100)) (Fn.mk (fun _ => 7))
  shareTest "arr" (mkArr [#[1], #[2, 3], #[]]) #[9] #[8, 8]
  shareTest "fin" (mkArr [(1 : Fin 5), 2, 3]) 4 0
  shareTest "list" (mkArr [[1], [2, 3], []]) [9] [8]
  shareTest "bytes" (mkArr [ByteArray.mk #[1], ByteArray.mk #[2], .empty]) (ByteArray.mk #[9]) .empty
  -- ByteArray / FloatArray / String mutators on shared values
  let ba : ByteArray := ⟨#[1, 2, 3, 4, 5]⟩
  let ba2 := ba.copySlice 0 (ByteArray.mk #[9, 9, 9, 9, 9, 9]) 1 3
  let ba3 := (ByteArray.mk #[7, 7, 7]).copySlice 0 ba 1 2
  let ba4 := if h : (1 : USize).toNat < ba.size then ba.uset 1 77 h else ba
  let ba5 := ba.append ba
  let ba6 := ba.extract 1 3
  IO.println s!"ba {ba} {ba2} {ba3} {ba4} {ba5} {ba6} {ba}"
  let fa : FloatArray := ⟨#[1, 2, 3]⟩
  let fa2 := if h : (1 : USize).toNat < fa.size then fa.uset 1 77 h else fa
  let fa3 := fa.push 4
  let fa4 := fa.set! 0 0.5
  IO.println s!"fa {fa} {fa2} {fa3} {fa4} {fa}"
  let s := "héllo"
  let s2 := s.pushn '!' 3
  let s3 := s ++ s
  let s4 := String.Pos.Raw.set s ⟨1⟩ 'E'
  let s5 := String.Pos.Raw.modify s ⟨0⟩ Char.toUpper
  let s6 := s.push 'x'
  let s7 := s.append "z"
  let s8 := s.map Char.toUpper
  let s9 := String.join [s, s]
  IO.println s!"str {s} {s2} {s3} {s4} {s5} {s6} {s7} {s8} {s9} {s}"

