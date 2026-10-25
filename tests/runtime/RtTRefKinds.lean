/-! Runtime test (typed references, clean step B2, optimization
`typed-cells`): every cell kind of a typed reference (`L2RRef…(Cell<T>)`,
the cell holding the element's own type) through the reference operations
of typed code: `mkRef`, `get`, `set`, `swap`, `modify` and `modifyGet`
(`take`, then `set`), `ptrEq` (aliases, and two references of equal
contents), aliases seen through a structure field, an array of references,
a closure and an `initialize` constant, and `ST.Ref` in `runST`. The
element types: a structure of a `Nat`, a `String` and a `Float` (`I:Pt`);
an inductive with nullary constructors and constructors with fields
(`I:Shape`); `Nat` (small, and big from 2^64 and 2^70); `Int` (negative,
small and big); `String`; `List Nat` (`I:List`); `Option Pt`
(`I:Option`); `Array Nat` (`A(box)`: in this program typed arrays turn
`Nat` off, so its arrays of `Nat` hold boxes; `RtTRefInPlace` has `A(Nat)`);
`Array (Array String)`; `Bool`,
`UInt8`, `UInt16`, `UInt32`, `Char`, `Float32` (scalars a box holds as an
immediate). `UInt64` and `Float` keep cells of boxes (no cell kind: their
box allocates). The program has no cast and no reference operation at
`lcAny`, and no element holds anything whose release could be observed,
so every kind seen is typed (`RtTRefKinds.l2r-debug`). -/

structure Pt where
  n : Nat
  s : String
  f : Float
  deriving Repr, BEq, Inhabited

instance : ToString Pt := ⟨fun p => s!"<{p.n},{p.s},{p.f}>"⟩

inductive Shape where
  | none
  | circle (r : Nat)
  | rect (w h : Nat) (tag : String)
  | dot
  deriving Repr, BEq, Inhabited

instance : ToString Shape := ⟨fun
  | .none => "none" | .dot => "dot" | .circle r => s!"c{r}" | .rect w h t => s!"r{w}x{h}{t}"⟩

/-- Every operation on references of element type `α`: `vals` are stored in
turn, `step` is the update of `modify`. -/
@[inline] def exercise {α : Type} [ToString α] (name : String) (init : α) (vals : Array α)
    (step : α → α) : IO Unit := do
  let out (s : String) : IO Unit := IO.println s!"{name} {s}"
  let r ← IO.mkRef init
  out s!"get {← r.get}"
  let mut log : Array String := #[]
  for v in vals do
    r.set v
    log := log.push (toString (← r.get))
  out s!"set {log}"
  let old ← r.swap init
  out s!"swap {old} {← r.get}"
  for _ in [0:3] do r.modify step
  out s!"modify {← r.get}"
  let got ← r.modifyGet fun x => (toString x, step x)
  out s!"modifyGet {got} {← r.get}"
  -- An alias: the same cell.
  let alias := r
  alias.set (vals.back?.getD init)
  out s!"alias {← r.get} {← r.ptrEq alias}"
  -- Another reference with the same contents is another cell.
  let r2 ← IO.mkRef (← r.get)
  r2.modify step
  out s!"other {← r.get} {← r2.get} {← r.ptrEq r2}"

structure Ctx where
  hits : IO.Ref Nat
  log : IO.Ref (Array String)
  last : IO.Ref Pt

initialize gCount : IO.Ref Nat ← IO.mkRef 5

def bump (c : Ctx) (k : Nat) : IO Unit := do
  c.hits.modify (· + k)
  c.log.modify (·.push s!"bump {k}")
  c.last.modify fun p => { p with n := p.n + k }

def stSum (xs : List Nat) : Nat := runST fun σ => show ST σ Nat from do
  let acc : ST.Ref σ Nat ← ST.mkRef 0
  for x in xs do acc.modify (· + x)
  let s : ST.Ref σ String ← ST.mkRef ""
  for x in xs do s.modify (· ++ toString x)
  return (← acc.get) + (← s.get).length

def mkCounter (start : Nat) : IO (IO.Ref Nat × (Nat → IO Nat)) := do
  let r ← IO.mkRef start
  return (r, fun k => do r.modify (· + k); r.get)

def main : IO Unit := do
  let big := 2 ^ 64
  exercise "pt" ({ n := 1, s := "a", f := 1.5 } : Pt)
    #[{ n := 2, s := "b", f := 2.5 }, { n := big, s := "big", f := -0.0 }]
    fun p => { p with n := p.n + 1, s := p.s ++ "!" }
  exercise "shape" Shape.none #[.circle 3, .dot, .rect 2 5 "x", .none]
    fun | .none => .dot | .dot => .circle 1 | .circle r => .circle (r + 1) | .rect w h t => .rect h w t
  exercise "nat" 0 #[7, big, 2 ^ 70 + 3, 9] (· + 2 ^ 63)
  exercise "int" (-3 : Int) #[-big, 4, (2 : Int) ^ 70, -1] (· * -2)
  exercise "str" "" #["x", "yz", "", "long string value"] (· ++ "+")
  exercise "list" ([] : List Nat) #[[1], [2, 3], []] (fun l => l.length :: l)
  exercise "opt" (none : Option Pt) #[some default, none, some { n := 5, s := "o", f := 0.25 }]
    fun | none => some default | some p => some { p with n := p.n * 2 }
  exercise "arr" (#[] : Array Nat) #[#[1, 2], #[big]] (·.push 1)
  exercise "arr2" (#[] : Array (Array String)) #[#[#["a"]], #[#[], #["b", "c"]]]
    (·.push #["n"])
  exercise "bool" false #[true, false, true] (!·)
  exercise "u8" (0 : UInt8) #[255, 7] (· + 100)
  exercise "u16" (0 : UInt16) #[65535, 7] (· + 30000)
  exercise "u32" (0 : UInt32) #[4294967295, 7] (· * 3)
  exercise "char" 'a' #['é', '∀', 'z'] (fun c => Char.ofNat (c.toNat + 1))
  exercise "f32" (0.5 : Float32) #[1.25, -3.0] (· * 2)
  exercise "u64" (0 : UInt64) #[18446744073709551615, 9223372036854775808, 3] (· + 1)
  exercise "float" (0.5 : Float) #[1.25, -3.0, 1e300] (· * 2)
  -- References in a structure, read and updated through it.
  let c : Ctx := { hits := ← IO.mkRef 0, log := ← IO.mkRef #[], last := ← IO.mkRef default }
  for k in [1:5] do bump c k
  IO.println s!"ctx {← c.hits.get} {← c.log.get} {← c.last.get}"
  -- An array of references: each its own cell.
  let rs ← (List.range 4).toArray.mapM fun i => IO.mkRef ({ n := i, s := toString i, f := 0.0 } : Pt)
  for r in rs do r.modify fun p => { p with s := p.s ++ p.s }
  if h : 1 < rs.size then
    rs[1].set { n := 99, s := "set", f := 9.0 }
    IO.println s!"refs {← rs.mapM (·.get)} {← rs[0].ptrEq rs[0]} {← rs[0].ptrEq rs[1]}"
  -- A closure holding a reference.
  let (r, add) ← mkCounter 10
  let a ← add 5
  let b ← add 7
  IO.println s!"counter {a} {b} {← r.get}"
  -- An `initialize` constant.
  gCount.modify (· * 3)
  IO.println s!"global {← gCount.get}"
  IO.println s!"st {stSum [1, 2, 30]}"
