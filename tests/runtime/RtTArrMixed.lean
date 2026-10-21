/-! Runtime test (typed arrays, clean step B1): typed and boxed arrays in
one program. `Array Pt` and `Array (Array Pt)` never meet generic code and
stay typed; `Array Shape` enters an existential package (`Pack`), so its
kind is boxed, and so is `Array (Array Shape)`, whose flow class holds
the same arrays; a structure field `Array (Array Float)` (a
typed array of compact arrays); a subarray of an `Array Pt` (the field
`Array α` of `Subarray` is then a box); an `Array Pt` in a generic box
(`Wrap`, a list of `Option (Array Pt)`) read back at its type; `Array Pt`
values compared, hashed into strings, and updated after a copy (the copy
keeps the old array). `RtTArrMixed.l2r-debug` checks which kinds stay
typed; the values must be the same either way. -/

structure Pt where
  n : Nat
  s : String
  deriving BEq, Inhabited

instance : ToString Pt := ⟨fun p => s!"<{p.n},{p.s}>"⟩

inductive Shape where
  | none
  | circle (r : Nat)
  deriving BEq, Inhabited

instance : ToString Shape := ⟨fun | .none => "none" | .circle r => s!"c{r}"⟩

structure Pack where
  α : Type
  arr : Array α
  render : α → String

@[noinline] def mkPack (a : Array Shape) : Pack := ⟨Shape, a, toString⟩
@[noinline] def Pack.show (p : Pack) : String := s!"{(p.arr.toList.take 4).map p.render} {p.arr.size}"
@[noinline] def Pack.grow (p : Pack) : Pack := { p with arr := p.arr.reverse }

structure Grid where
  rows : Array (Array Float)
  name : String

structure Wrap (α : Type) where
  val : α
  tag : Nat
  deriving Inhabited

@[noinline] def wrapAll {α : Type} (xs : List α) : List (Wrap α) := xs.mapIdx fun i x => ⟨x, i⟩

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 12
  let pts : Array Pt := (Array.range n).map fun i => { n := i * i, s := s!"p{i}" }
  let shs : Array Shape := (Array.range n).map fun i => if i % 2 == 0 then .none else .circle i
  let pk := (mkPack (shs.push (.circle 99))).grow
  IO.println s!"pack {pk.show}"
  let grid : Array (Array Pt) := #[pts, pts.reverse, pts.extract 2 5]
  let grid2 := grid.modify 1 (·.push { n := 7, s := "seven" }) |>.set! 0 #[]
  IO.println s!"grid {grid.map (·.size)} {grid2.map (·.size)} {grid2[1]!.back!} {grid[0]![3]!}"
  let sgrid : Array (Array Shape) := #[shs, shs.map fun | .none => .circle 0 | s => s]
  IO.println s!"sgrid {sgrid.map (fun r => r.foldl (fun c s => if s == .none then c + 1 else c) 0)} {sgrid[1]![2]!}"
  let g : Grid := { rows := (Array.range 3).map fun i => (Array.range n).map fun j => i.toFloat * j.toFloat, name := "g" }
  let g2 := { g with rows := g.rows.modify 2 (·.map (· / 2.0)) }
  IO.println s!"floats {g.rows.map (·.foldl (· + ·) 0.0)} {g2.rows[2]![5]!} {g2.name}"
  let sub := pts[2:6]
  let mut acc := 0
  for p in sub do
    acc := acc + p.n
  IO.println s!"subarray {sub.size} {acc} {sub.toArray.map (·.s)}"
  let ws := wrapAll [pts, pts.pop, #[]]
  IO.println s!"wrap {ws.map (·.val.size)} {ws.map (·.tag)} {(ws.head!).val[1]!}"
  let opts : List (Option (Array Pt)) := [some pts, none, some (pts.map fun p => { p with n := p.n + 1 })]
  IO.println s!"opts {opts.map (·.map (·.size))} {(opts.getLast!.get!)[2]!}"
  let copy := pts
  let upd := (pts.set! 0 { n := 100, s := "hundred" }).swapIfInBounds 1 2
  IO.println s!"copy {copy[0]!} {upd[0]!} {upd[1]!} {copy == upd} {copy == pts} {toString (copy.map (·.n))}"
