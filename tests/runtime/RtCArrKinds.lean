/-! Runtime test (compact scalar arrays, plan "Tests"): every storage kind of
a compact `Array S` (u8: `UInt8`, `Bool`, a five-constructor enum; u16:
`UInt16`; u32: `UInt32`, `Char`; u64: `UInt64`, `USize`; f32: `Float32`;
f64: `Float`) through the array operations of typed code: `push`, `set!`,
`get!`, `getD`, `a[i]?`, `uget`/`uset`, `swapIfInBounds`, `pop`, `back!`,
`back?`, `extract`, `++`, `reverse`, `foldl`/`foldr` (also with bounds),
`any`/`all`, `filter`, `count`, `toList`, `Array.mk`, `List.toArray`,
`Array.ofFn`, `Array.replicate`, `Array.range` mapped, `contains`, `idxOf?`,
`findIdx?`, `find?`, `isPrefixOf`, `erase`, `qsort`, `insertionSort`,
`binSearch`, `for` with `break`, subarrays, `insertIdx!`, `eraseIdx!`,
`popWhile`, `takeWhile`, `leftpad`, and `get!` out of bounds (a panic and
the kind's default). The special values of each kind go through the array
and are printed with their bits: `UInt64` and `USize` at and above 2^63,
`Char` up to U+10FFFF and U+0000, `Float` and `Float32` NaNs (with a
payload, signalling, negative), -0.0, infinities, the smallest denormal;
`==`, `contains` and `count` compare floats as floats (a NaN is unequal
to itself). The program has no cast and no value of unknown type, so once
compact arrays land every array here is compact. `exercise` is
`@[inline]`: each call is typed code at one element type. -/

inductive Col | red | green | blue | cyan | magenta
  deriving Repr, BEq, Inhabited

def Col.ofIdx : Nat → Col
  | 0 => .red | 1 => .green | 2 => .blue | 3 => .cyan | _ => .magenta

def Col.idx : Col → Nat
  | .red => 0 | .green => 1 | .blue => 2 | .cyan => 3 | .magenta => 4

instance : ToString Col := ⟨reprStr⟩

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

def chars : Array Char := #['a', 'Z', 'é', 'ß', '€', '中', '😀', Char.ofNat 0x10FFFF]

def fspecials : Array Float :=
  #[0.0, -0.0, 1.0 / 0.0, -1.0 / 0.0, Float.ofBits 0x7FF8000000000000,
    Float.ofBits 0x7FF8000000000001, Float.ofBits 0xFFF0000000000001,
    1.5, Float.ofBits 1]

def f32specials : Array Float32 :=
  #[Float32.ofBits 0, Float32.ofBits 0x80000000, Float32.ofBits 0x7F800000,
    Float32.ofBits 0xFF800000, Float32.ofBits 0x7FC00000,
    Float32.ofBits 0x7FC00001, Float32.ofBits 0xFF800001, 1.5,
    Float32.ofBits 1]

def mkF (i : Nat) : Float :=
  if i % 9 == 4 then fspecials[(i / 9) % fspecials.size]! else (i.toFloat - 7.5) / 3.0

def mkF32 (i : Nat) : Float32 :=
  if i % 9 == 4 then f32specials[(i / 9) % f32specials.size]! else ((i.toFloat - 7.5) / 3.0).toFloat32

def runU8 (n : Nat) : IO Unit :=
  exercise "u8" #[0, 1, 127, 128, 255] (fun i => (i * 37 + 11).toUInt8) (·.toUInt64) (· < ·) n
def runBool (n : Nat) : IO Unit :=
  exercise "bool" #[true, false] (fun i => i % 3 == 0) (fun b => if b then 1 else 0) (fun x y => !x && y) n
def runCol (n : Nat) : IO Unit :=
  exercise "col" #[.red, .magenta, .blue] (fun i => Col.ofIdx (i % 5)) (fun c => c.idx.toUInt64)
    (fun x y => x.idx < y.idx) n
def runU16 (n : Nat) : IO Unit :=
  exercise "u16" #[0, 0x7FFF, 0x8000, 0xFFFF] (fun i => (i * 7919 + 3).toUInt16) (·.toUInt64) (· < ·) n
def runU32 (n : Nat) : IO Unit :=
  exercise "u32" #[0, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF] (fun i => (i * 2654435761).toUInt32)
    (·.toUInt64) (· < ·) n
def runChar (n : Nat) : IO Unit :=
  exercise "char" #['a', Char.ofNat 0x10FFFF, '€', '😀', 'Z'] (fun i => chars[i % chars.size]!)
    (·.val.toUInt64) (· < ·) n
def runU64 (n : Nat) : IO Unit :=
  exercise "u64" #[0, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001, 0xFFFFFFFFFFFFFFFF]
    (fun i => i.toUInt64 * 0x9E3779B97F4A7C15) id (· < ·) n
def runUSize (n : Nat) : IO Unit :=
  exercise "usize" #[0, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
    (fun i => (i * 0x9E3779B97F4A7C15).toUSize) (·.toUInt64) (· < ·) n
def runF64 (n : Nat) : IO Unit :=
  exercise "f64" fspecials mkF Float.toBits (· < ·) n
def runF32 (n : Nat) : IO Unit :=
  exercise "f32" f32specials mkF32 (·.toBits.toUInt64) (· < ·) n

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 40
  runU8 n; runBool n; runCol n; runU16 n; runU32 n; runChar n; runU64 n; runUSize n; runF64 n; runF32 n
  -- U+0000 in a Char array (printed as its code point)
  let z : Array Char := (#['\x00', 'b'].push '\x00').set! 1 '\x00'
  IO.println s!"nul {z.toList.map Char.toNat} {z.count '\x00'} {z == #['\x00', '\x00', '\x00']}"
