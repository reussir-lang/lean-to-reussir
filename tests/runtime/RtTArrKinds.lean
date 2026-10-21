/-! Runtime test (typed arrays, clean step B1, optimization `typed-arrays`):
every pointer kind of a typed `Array X` (`RVec<T>` of the element's own
type) through the array operations of typed code, the same operations as
`RtCArrKinds`: a structure of a `Nat`, a `String` and a `Float` (`I:Pt`);
an inductive with nullary constructors and constructors with fields
(`I:Shape`; its nullary values are Reussir immediates); `Nat` (small ones,
and big ones from 2^63 and 2^70); `Int` (negative, small and big);
`String`; `List Nat` (`I:List`); `Option Pt` (`I:Option`); `Array Nat`
(`A(Nat)`); `Array (Array String)` (`A(A(LStr))`). The program has no cast
and no value of unknown type that holds such an array, and no element holds
anything whose release could be observed, so every array here is typed
(`RtTArrKinds.l2r-debug`). `exercise` is `@[inline]`: each call is typed
code at one element type. -/

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

def Shape.bits : Shape → UInt64
  | .none => 1 | .dot => 2 | .circle r => r.toUInt64 * 3 | .rect w h t => (w * 31 + h).toUInt64 + t.length.toUInt64

def Shape.lt (a b : Shape) : Bool := a.bits < b.bits

def strBits (s : String) : UInt64 := s.foldl (fun h c => (h ^^^ c.val.toUInt64) * 1099511628211) 3

def mix (h x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

@[inline] def exercise {α : Type} [ToString α] [BEq α] [Inhabited α]
    (name : String) (specials : Array α) (mk : Nat → α) (bits : α → UInt64)
    (lt : α → α → Bool) (n : Nat) : IO Unit := do
  let out (s : String) : IO Unit := IO.println s!"{name} {s}"
  let dg (xs : Array α) : UInt64 := xs.foldl (fun h x => mix h (bits x)) 7
  -- push
  let mut a : Array α := #[]
  for i in [0:n] do
    a := a.push (mk i)
  out s!"push {a.size} {dg a} {a[0]!} {a[n / 2]!} {a.back!}"
  -- the special values: stored with set! into a replicated array, read back
  let mut s : Array α := Array.replicate specials.size default
  for i in [0:specials.size] do
    s := s.set! i specials[i]!
  out s!"specials {s.toList} {s.toList.map bits} {s == specials} {s.size}"
  -- set!, get!, getD, a[i]?
  let a1 := a.set! 3 specials[0]!
  out s!"read {a1[3]!} {a[3]!} {a.getD (n + 5) specials[1]!} {a.getD 2 specials[1]!} {a[n + 2]?} {a[2]?} {(a[n]?).getD default}"
  -- uset over the whole array (a1 is dead: in place), uget sum
  let mut u := a1
  for i in [0:n] do
    let j : USize := (n - 1 - i).toUSize
    if h : j.toNat < u.size then
      u := u.uset j (mk (i + 100)) h
  let mut usum : UInt64 := 7
  for i in [0:u.size] do
    let j := i.toUSize
    if h : j.toNat < u.size then
      usum := mix usum (bits (u.uget j h))
  out s!"uset {dg u} {usum} {u[0]!} {u.back!}"
  -- swap (the second is out of bounds: no change)
  let w := (u.swapIfInBounds 0 (n - 1)).swapIfInBounds 1 (n + 3)
  out s!"swap {w[0]!} {w[n - 1]!} {w[1]!} {dg w}"
  -- pop, back
  let p := w.pop.pop
  out s!"pop {p.size} {p.back!} {p.back?} {(#[] : Array α).back?} {(p.pop.push specials[2 % specials.size]!).back!} {dg p}"
  -- extract
  let e1 := p.extract 2 7
  let e2 := p.extract (p.size - 3) (p.size + 10)
  let e3 := p.extract 5 2
  out s!"extract {e1.toList} {e2.toList} {e3.size} {dg e1}"
  -- append, also an array to itself
  let ap := e1 ++ specials
  let self := e1 ++ e1
  out s!"append {ap.size} {dg ap} {self.size} {dg self} {e1.size} {(e1 ++ #[]).size} {((#[] : Array α) ++ e1).size}"
  -- reverse
  let r := ap.reverse
  out s!"reverse {r.toList} {r.reverse == ap} {dg r.reverse == dg ap}"
  -- folds
  out s!"fold {a.foldl (fun h x => mix h (bits x)) 1} {a.foldr (fun x h => mix h (bits x)) 1} {a.foldl (fun h x => mix h (bits x)) 1 2 9} {a.foldr (fun x h => mix h (bits x)) 1 9 2}"
  -- any, all, filter, count
  let pr (x : α) : Bool := bits x % 3 == 0
  out s!"anyall {a.any pr} {a.all pr} {a.any (fun x => bits x == 12345)} {a.all (fun x => bits x != 12345)} {a.any pr 5 9} {(a.filter pr).size} {dg (a.filter pr)} {a.count specials[0]!} {a.count (mk 5)}"
  -- lists
  let l := a.toList
  let back1 := Array.mk l
  let back2 := l.toArray
  let ofn := Array.ofFn (n := 6) fun i => mk (i.val * 7)
  out s!"lists {l.length} {dg back1} {dg back2} {back1 == a} {ofn.toList} {(Array.mk specials.toList.reverse).toList}"
  -- replicate, range
  let rep := Array.replicate 4 specials[1]!
  let rng := (Array.range 7).map mk
  out s!"replicate {rep.toList} {rng.toList} {(Array.replicate 0 specials[0]!).size}"
  -- search
  out s!"search {a.contains specials[0]!} {a.contains (mk 5)} {a.idxOf? (mk 5)} {a.findIdx? pr} {a.find? pr} {a.isPrefixOf (a.push (mk 0))} {(a.erase (mk 5)).size}"
  -- sorting
  let q := a.qsort lt
  let ins := a.insertionSort lt
  out s!"sort {dg q} {dg ins} {q[0]!} {q.back!} {q.binSearch (mk 5) lt} {(specials.qsort lt).toList} {(specials.insertionSort lt).toList}"
  -- for with break
  let mut cnt := 0
  for x in a do
    if bits x % 7 == 6 then break
    cnt := cnt + 1
  out s!"forin {cnt}"
  -- subarrays
  let sub := a[2:9]
  let mut subd : UInt64 := 0
  for x in sub do
    subd := mix subd (bits x)
  out s!"subarray {sub.size} {sub.foldl (fun h x => mix h (bits x)) 3} {sub.toArray.toList} {sub.any pr} {sub.all pr} {subd}"
  -- insert, erase, popWhile, takeWhile, leftpad
  let ie := (e1.insertIdx! 2 specials[0]!).eraseIdx! 0
  out s!"insert {ie.toList} {(e1.insertIdx! e1.size specials[1]!).back!} {(e1.popWhile pr).size} {(e1.takeWhile pr).size} {(e1.leftpad 8 specials[1]!).toList}"
  -- out of bounds: a panic, then the default
  out s!"default {a[n + 9]!}"


def big : Nat := 2 ^ 70 + 12345

def runPt (n : Nat) : IO Unit :=
  exercise (α := Pt) "pt" #[{ n := 0, s := "", f := 0.5 }, { n := big, s := "big", f := -1.0 }, { n := 7, s := "é€😀", f := 2.0 }]
    (fun i => { n := i * i, s := s!"p{i}", f := i.toFloat / 4.0 }) (fun p => p.n.toUInt64 + strBits p.s)
    (fun a b => a.n < b.n) n
def runShape (n : Nat) : IO Unit :=
  exercise (α := Shape) "shape" #[.none, .rect 3 4 "x", .dot, .circle 9]
    (fun i => match i % 4 with | 0 => .none | 1 => .circle i | 2 => .rect i (i + 1) s!"t{i}" | _ => .dot)
    Shape.bits Shape.lt n
def runNat (n : Nat) : IO Unit :=
  exercise (α := Nat) "nat" #[0, 2 ^ 63 - 1, 2 ^ 63, big, 1]
    (fun i => if i % 5 == 3 then 2 ^ 64 + i else i * 1000003) (fun x => (x % 18446744073709551557).toUInt64)
    (· < ·) n
def runInt (n : Nat) : IO Unit :=
  exercise (α := Int) "int" #[0, -1, -(2 ^ 63 : Int), (2 ^ 63 : Int), -(big : Int)]
    (fun i => if i % 4 == 1 then -((2 : Int) ^ 65) - i else (i : Int) * 7919 - 100)
    (fun x => (x % 18446744073709551557).toNat.toUInt64) (· < ·) n
def runStr (n : Nat) : IO Unit :=
  exercise (α := String) "str" #["", "a", "é€😀", "a much longer string than the small ones"]
    (fun i => s!"s{i * 13 % 17}") strBits (· < ·) n
def runList (n : Nat) : IO Unit :=
  exercise (α := List Nat) "list" #[[], [1, 2, 3], [big]]
    (fun i => List.range (i % 4) |>.map (· + i)) (fun l => l.foldl (fun h x => (h ^^^ x.toUInt64) * 31) 5)
    (fun a b => a.length < b.length || (a.length == b.length && a.sum < b.sum)) n
def runOpt (n : Nat) : IO Unit :=
  exercise (α := Option Pt) "opt" #[none, some { n := 1, s := "one", f := 1.0 }]
    (fun i => if i % 3 == 0 then none else some { n := i, s := s!"o{i}", f := 0.0 })
    (fun o => match o with | none => 0 | some p => p.n.toUInt64 + 1)
    (fun a b => (a.map (·.n)).getD 0 < (b.map (·.n)).getD 0) n
def runArr (n : Nat) : IO Unit :=
  exercise (α := Array Nat) "arr" #[#[], #[1, 2], #[big, 0]]
    (fun i => (Array.range (i % 5)).map (· * i)) (fun a => a.foldl (fun h x => (h ^^^ x.toUInt64) * 31) 5)
    (fun a b => a.size < b.size || (a.size == b.size && a.foldl (· + ·) 0 < b.foldl (· + ·) 0)) n
def runArr2 (n : Nat) : IO Unit :=
  exercise (α := Array (Array String)) "arr2" #[#[], #[#["x"], #[]], #[#["é", "€"]]]
    (fun i => #[#[s!"a{i}"], (Array.range (i % 3)).map toString])
    (fun a => a.foldl (fun h b => b.foldl (fun h s => (h ^^^ strBits s) * 31) h) 5)
    (fun a b => a.size < b.size || (a.size == b.size && a.foldl (· + ·.size) 0 < b.foldl (· + ·.size) 0)) n

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 40
  runPt n; runShape n; runNat n; runInt n; runStr n; runList n; runOpt n; runArr n; runArr2 n
