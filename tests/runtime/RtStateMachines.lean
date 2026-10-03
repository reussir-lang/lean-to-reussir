import Std.Data.HashMap

/-! Runtime test: loops that lean2rr runs as state machines (J4, translation
plan §5.6) with accumulators of every representation. O7SM/O7SM2: records of
String/Float/UInt64/Array/value structure/Option/tuple, closures, IO.Ref,
Thunk, Task, ByteArray, FloatArray, Int, Float32, USize, Unit, Char, Bool,
Option Never, Except, early exits. JpSm3: state machines carrying
Float32/UInt8/16/32/USize/Char/Bool/Unit, closures, Thunk,
Option (Nat × Float), Except, ByteArray, FloatArray, String, HashMap, a value
structure, a structure, Int; an IO loop with an IO.Ref, a StateM loop, an
Except loop with an error exit.
From the round-7 review, area O (rv7/opts, state-machines checks O7SM and
O7SM2), and the round-6 review, area jp (rv6/jp, check 18, JpSm3). -/

namespace O7SM
-- from rv7/opts/O7SM.lean
structure V where v : Nat
structure Acm where
  s : String
  f : Float
  u : UInt64
  a : Array Nat
  vs : V
  o : Option String
  p : Nat × Float

@[noinline] def big (y : Nat) (acc : Acm) (g : Nat → Nat) : Acm :=
  { acc with s := acc.s ++ s!"{y % 10}", f := acc.f + y.toFloat / 2, u := acc.u * 3 + y.toUInt64,
             a := acc.a.push (g y), vs := ⟨acc.vs.v + y⟩, o := (acc.o.map (· ++ "x")),
             p := (acc.p.1 + 1, acc.p.2 * 1.5) }

partial def loop (i : Nat) (acc : Acm) (g : Nat → Nat) (r : IO.Ref Nat) (th : Thunk Nat) (fl : Float) (w : UInt64) (stop : Nat) : Acm :=
  if i ≥ stop then acc
  else
    let rr := if i % 3 == 0 then some (i * 2 + th.get) else if i % 7 == 6 then none else some (i + 1 + fl.toUInt64.toNat)
    match rr with
    | none => { acc with s := acc.s ++ s!"<exit at {i} w={w}>" }
    | some y =>
      let acc := big y acc g
      let acc := if y % 2 == 0 then big (y + 1) acc g else acc
      let acc := if y % 5 == 0 then { acc with s := acc.s ++ "five" } else acc
      let acc := if acc.a.size > 3 then { acc with a := acc.a.extract 1 acc.a.size } else acc
      loop (i + 1) acc (fun x => g x + 1) r th (fl + 0.5) (w + 1) stop

partial def loopN (i : Nat) (acc : Nat) (step : Nat) : Nat :=
  if i > 1000 then acc
  else
    let rr := if i % 4 == 0 then some (acc + step) else if i % 9 == 8 then none else some (acc * 3 % 1000003)
    match rr with
    | none => acc + 1000000 * i
    | some y =>
      let z := y + i
      let z := if z % 2 == 0 then z / 2 else 3 * z + 1
      let z := if z % 3 == 0 then z / 3 else z + 7
      let z := if z % 5 == 0 then z / 5 else z + 11
      let z := if z % 7 == 0 then z / 7 else z + 13
      loopN (i + 1) z (step + 1)

partial def loopArr (i : Nat) (a : Array UInt64) (b : ByteArray) (s : String) : Array UInt64 × ByteArray × String :=
  if i ≥ 50 then (a, b, s)
  else
    let rr := if i % 3 == 0 then some i else if i % 11 == 10 then none else some (i * 2)
    match rr with
    | none => (a.push 999, b.push 9, s ++ "!")
    | some y =>
      let a := a.set! (y % a.size) (a[y % a.size]! + y.toUInt64)
      let a := if y % 2 == 0 then a.push y.toUInt64 else a
      let b := b.push (y % 256).toUInt8
      let s := if y % 5 == 0 then s.push 'x' else s.push 'y'
      let a := if a.size > 10 then a.pop else a
      loopArr (i + 1) a b s

def main : IO Unit := do
  let r ← IO.mkRef 0
  let acc0 : Acm := { s := "", f := 0, u := 1, a := #[], vs := ⟨0⟩, o := some "o", p := (0, 1) }
  for stop in [5, 6, 20, 100] do
    let acc := loop 0 acc0 (· * 2) r (Thunk.mk fun _ => 3) 0.25 7 stop
    IO.println s!"{acc.s} {acc.f} {acc.u} {acc.a} {acc.vs.v} {acc.o} {acc.p}"
  IO.println (loopN 0 1 1)
  let (a, b, s) := loopArr 0 #[1, 2, 3] ByteArray.empty ""
  IO.println s!"{a} {b.toList} {s}"
end O7SM

namespace O7SM2
-- from rv7/opts/O7SM2.lean
inductive Never : Type
structure V where v : Nat
structure V2 where
  a : Nat
  b : String

def useNever (n : Never) : Nat := nomatch n

partial def loopP (i : Nat) (acc : Nat) (g : Nat → Nat) (r : IO.Ref Nat) (th : Thunk Nat) (tk : Task Nat)
    (ba : ByteArray) (fa : FloatArray) (s : String) (z : Int) (f32 : Float32) (us : USize) (tup : Nat × String)
    (u : Unit) (v : V) (v2 : V2) (o : Option (Nat → Nat)) (ch : Char) (b : Bool) (nv : Option Never) (e : Except String Nat) : String :=
  if i > 200 then
    s!"end {acc} {g 1} {th.get} {tk.get} {ba.size} {fa.size} {s.length} {z} {f32} {us} {tup} {u == ()} {v.v} {v2.b} {(o.map (· 2))} {ch} {b} {nv.map useNever} {repr e}"
  else
    let rr := if i % 4 == 0 then some (acc + 1) else if i % 9 == 8 then none else some (acc * 3 % 1000003)
    match rr with
    | none => s!"exit {i} {acc} {g 2} {th.get} {tk.get} {ba.size} {fa.size} {s} {z} {f32} {us} {tup.2} {v.v} {v2.a} {(o.map (· 3))} {ch} {b} {nv.isSome} {repr e}"
    | some y =>
      let w := y + i
      let w := if w % 2 == 0 then w / 2 else 3 * w + 1
      let w := if w % 3 == 0 then w / 3 else w + 7
      let w := if w % 5 == 0 then w / 5 else w + 11
      let w := if w % 7 == 0 then w / 7 else w + 13
      loopP (i + 1) w g r th tk ba fa s z f32 us tup u v v2 o ch b nv e

def main : IO Unit := do
  let r ← IO.mkRef 0
  IO.println (loopP 0 1 (· + 1) r (Thunk.mk fun _ => 5) (Task.pure 6) ⟨#[1, 2]⟩ ⟨#[1.5]⟩ "str" (-7) 2.5 9 (1, "t") () ⟨8⟩ ⟨9, "v2"⟩ (some (· * 2)) 'c' true none (.ok 3))
  IO.println (loopP 1 2 (· + 2) r (Thunk.mk fun _ => 5) (Task.pure 6) ⟨#[]⟩ ⟨#[]⟩ "" 7 0.5 1 (2, "u") () ⟨0⟩ ⟨1, ""⟩ none 'd' false none (.error "err"))
end O7SM2

namespace JpSm3
-- from rv6/jp/JpSm3.lean
/-! State machines (J4) whose loops carry parameters of many types. -/

@[inline] def okn (x : Nat) : Bool := (x % 3 == 0 && x != 9 || x == 7) || (x > 1000 && x < 2000 || x == 42)

structure W where
  v : Nat
deriving Repr

structure P2 where
  f : Float
  u : UInt8
  c : Char
deriving Repr

@[noinline] partial def l1 (i n : Nat) (f32 : Float32) (u8 : UInt8) (u16 : UInt16) (u32 : UInt32) (us : USize) (c : Char) (b : Bool) (u : Unit) : String :=
  if i < n then
    if okn i && i % 2 == 0 then l1 (i+1) n (f32 + 1.5) (u8 + 1) (u16 + 3) (u32 * 3) (us + 7) 'a' (!b) u
    else if okn i then l1 (i+1) n (f32 * 0.5) (u8 * 3) u16 (u32 + 1) (us * 2) 'b' b ()
    else if i == 123456789 then "stop"
    else l1 (i+1) n f32 (u8 - 1) (u16 - 1) u32 us c b u
  else s!"{f32} {u8} {u16} {u32} {us} {c} {b} {u == ()}"

@[noinline] partial def l2 (i n : Nat) (f : Nat → Nat) (t : Thunk Nat) (o : Option (Nat × Float)) (e : Except String Nat) : Nat × String :=
  if i < n then
    if okn i && i % 2 == 0 then l2 (i+1) n (fun y => f y + 1) t (some (i, i.toFloat)) (.ok i)
    else if okn i then l2 (i+1) n f (Thunk.mk fun _ => t.get + 1) none (.error s!"e{i}")
    else if i == 123456789 then (0, "stop")
    else l2 (i+1) n f t o e
  else
    let os := match o with | some (a, b) => s!"{a},{b}" | none => "none"
    let es := match e with | .ok v => s!"ok {v}" | .error m => m
    (f 0 + t.get, os ++ " " ++ es)

@[noinline] partial def l3 (i n : Nat) (ba : ByteArray) (fa : FloatArray) (s : String) (m : Std.HashMap Nat String) (w : W) (p : P2) (z : Int) : String :=
  if i < n then
    if okn i && i % 2 == 0 then l3 (i+1) n (ba.push i.toUInt8) fa (if s.length < 20 then s.push 'x' else s) (m.insert (i % 10) s!"{i}") { v := w.v + 1 } { p with f := p.f + 1.0 } (z - i)
    else if okn i then l3 (i+1) n ba (fa.push i.toFloat) s m w { p with u := p.u + 1, c := 'q' } (z * 2 % 1000000000000)
    else if i == 123456789 then "stop"
    else l3 (i+1) n ba fa s (m.erase (i % 10)) w p z
  else s!"{ba.size} {fa.size} {s} {m.size} {w.v} {p.f} {p.u} {p.c} {z}"

@[noinline] partial def l4 (r : IO.Ref Nat) (i n : Nat) (acc : Array String) : IO (Array String) := do
  if i < n then
    if okn i && i % 2 == 0 then
      r.modify (· + i)
      l4 r (i+1) n acc
    else if okn i then
      if i % 1000 == 7 then l4 r (i+1) n (acc.push s!"{i}") else l4 r (i+1) n acc
    else if i == 123456789 then return acc
    else l4 r (i+1) n acc
  else return acc

@[noinline] partial def l5 (i n : Nat) (st : StateM Nat Unit) : StateM Nat Nat := do
  if i < n then
    if okn i && i % 2 == 0 then modify (· + i); l5 (i+1) n st
    else if okn i then st; l5 (i+1) n st
    else if i == 123456789 then return 0
    else l5 (i+1) n st
  else return (← get)

@[noinline] partial def l6 (i n : Nat) (acc : Nat) : Except String Nat :=
  if i < n then
    if okn i && i % 2 == 0 then l6 (i+1) n (acc + i)
    else if okn i then (if acc > 10^15 then .error s!"big {i}" else l6 (i+1) n (acc * 3))
    else if i == 123456789 then .ok 0
    else l6 (i+1) n acc
  else .ok acc

def main : IO Unit := do
  let n := 1000000
  IO.println (l1 0 n 0.0 0 0 0 0 'z' false ())
  let (a, b) := l2 0 n id (Thunk.pure 1) none (.ok 0)
  IO.println s!"l2 {a} {b}"
  IO.println (l3 0 n .empty .empty "" {} ⟨0⟩ ⟨0.0, 0, 'z'⟩ 5)
  let r ← IO.mkRef 0
  let acc ← l4 r 0 n #[]
  IO.println s!"l4 {← r.get} {acc.size} {acc.toList.take 3}"
  let (v, s) := (l5 0 n (modify (· + 1))).run 0
  IO.println s!"l5 {v} {s}"
  IO.println s!"l6 {repr (l6 0 n 1)} {repr (l6 0 100 1)}"
end JpSm3

def main : IO Unit := do
  IO.println "=== O7SM"
  O7SM.main
  IO.println "=== O7SM2"
  O7SM2.main
  IO.println "=== JpSm3"
  JpSm3.main
