/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1305`:
- `A1306`:
- `A1307`:
- `A1308`:
- `A1311`:
- `A1312`:
- `A1313`:
- `A1314`:
- `A1315`:
- `A1316`:
- `A1317`: -/

namespace A1305

@[noinline] def appG {α : Sort u} (f : α → Nat) (a : α) : Nat := f a + 1
@[noinline] def loopG {α : Sort u} (f : α → Nat) (a : α) (m : Nat) : Nat := (List.range m).foldl (fun acc i => acc + f a + i) 0
@[noinline] def callAt (g : True → Nat) (i : Nat) : Nat := g trivial + i

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let t : True → Nat := fun _ => dbgTrace s!"t {n}" fun _ => n + 2
  let ty : Type → Nat := fun _ => dbgTrace "ty" fun _ => n + 4
  let g := appG (α := True) (fun _ => dbgTrace "g" fun _ => n * 3)
  let ts : List (True → Nat) := [t, fun _ => dbgTrace "inline" fun _ => n]
  let nat : Nat → Nat := fun x => dbgTrace s!"nat {x}" fun _ => x + 5
  IO.eprintln "== made"
  IO.println s!"{appG t trivial} {loopG t trivial (n + 2)}"
  IO.eprintln "== type"
  IO.println s!"{appG ty Nat} {loopG ty String (n + 1)}"
  IO.eprintln "== forwarder"
  IO.println s!"{callAt g 1 + callAt g 2}"
  IO.eprintln "== list"
  IO.println s!"{ts.foldl (fun acc f => acc + appG f trivial + f trivial) 0}"
  IO.eprintln "== nat"
  IO.println s!"{appG nat n + loopG nat (n + 1) 2}"
end A1305

namespace A1306

@[noinline] def countG {α : Type 1} (xs : List α) (f : α → Nat) : Nat := xs.foldl (fun acc x => acc + f x) 0
@[noinline] def keep {α : Sort u} (_ : α) (k : Nat) : Nat := dbgTrace s!"keep {k}" fun _ => k + 1

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let ts : List Type := (List.range (n + 2)).map fun i => if i % 2 == 0 then Nat else String
  let ps : List (PLift True) := (List.range (n + 1)).map fun _ => ⟨trivial⟩
  IO.println s!"{ts.length} {ps.length}"
  IO.eprintln "== count"
  IO.println s!"{countG ts (fun _ => dbgTrace "elem" fun _ => 2)}"
  IO.eprintln "== map"
  IO.println s!"{(ts.map fun _ => dbgTrace "map" fun _ => n).foldl (· + ·) 0}"
  IO.eprintln "== proofs"
  IO.println s!"{ps.foldl (fun acc _ => dbgTrace "proof" fun _ => acc + 1) 0}"
  IO.eprintln "== keep"
  IO.println s!"{keep Nat n + keep trivial (n + 1)}"
end A1306

namespace A1307

@[noinline] def constT {β : Sort u} {γ : Type v} (b : γ) (_ : β) : γ := dbgTrace "constT" fun _ => b
@[noinline] def c3 : Type → Type → Nat := fun _ => dbgTrace "c3 first" fun _ => fun _ => dbgTrace "c3 second" fun _ => 7
structure Rest where
  k : Type → Nat
@[noinline] def atFirst (h : Type → Type → Nat) : Rest := ⟨h Nat⟩
@[noinline] def loopT (r : Rest) (m : Nat) : Nat := (List.range m).foldl (fun acc i => acc + r.k Bool + i) 0

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  let c : Type → Nat := fun _ => dbgTrace s!"c {n}" fun _ => n + 5
  let hs : List (Type → Type → Nat) := [constT c, fun _ _ => n + 6, c3]
  IO.eprintln "== made"
  IO.println s!"{hs.foldl (fun acc h => acc + loopT (atFirst h) (n + 2)) 0}"
  IO.eprintln "== direct"
  IO.println s!"{hs.foldl (fun acc h => acc + h String Nat) n}"
end A1307

namespace A1308

@[noinline] def pick (o : Option Type) : Nat := match o with | some _ => 1 | none => 0
@[noinline] def countSome (os : List (Option Type)) : Nat :=
  os.foldl (fun acc o => match o with | some _ => dbgTrace "some" fun _ => acc + 1 | none => acc) 0

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{pick (if n > 0 then some Nat else none) + pick (some String)}"
  let os : List (Option Type) := (List.range (n + 3)).map fun i => if i % 2 == 0 then some Nat else none
  IO.println s!"{countSome os}"
end A1308

namespace A1311

abbrev LA : Bool → Type
  | true => List Nat
  | false => Nat
abbrev NS : Bool → Type
  | true => Nat
  | false => String
@[noinline] def f : (d : Bool) → Nat → LA d
  | true, n => [n, n + 1]
  | false, n => n
@[noinline] def rdL : (d : Bool) → List (NS d) → Nat
  | true, xs => xs.foldl (· + ·) 0
  | false, xs => xs.length
@[noinline] def sumNat (xs : List Nat) : Nat := xs.foldl (· + ·) 0
@[noinline] def pick : (d : Bool) → LA d → List Nat
  | true, xs => xs
  | false, n => [n]

def caseMain (args : List String) : IO Unit := do
  let k := args.length
  let a := f true (k + 1)
  let b := f true (k + 10)
  let c := if k > 0 then a else b
  IO.println (rdL true (pick true a) + sumNat (pick true c) + rdL false ["x"])
end A1311

namespace A1312

abbrev CN : Bool → Type
  | true => Char
  | false => Nat
@[noinline] def rdC : (d : Bool) → List (CN d) → Nat
  | true, xs => xs.foldl (fun acc c => acc + c.toNat) 0
  | false, xs => xs.foldl (· + ·) 0

def caseMain (args : List String) : IO Unit := do
  let s := "ab" ++ toString args.length
  IO.println s!"{rdC true s.toList} {rdC false (List.range (args.length + 3))}"
end A1312

namespace A1313

abbrev CN : Bool → Type
  | true => Char
  | false => Nat
@[noinline] def mkL : (d : Bool) → Nat → List (CN d)
  | true, n => ['a', Char.ofNat (98 + n % 3)]
  | false, n => [n, n + 1]
@[noinline] def show' (xs : List (CN true)) : String := String.ofList xs
@[noinline] def sumN (xs : List (CN false)) : Nat := xs.foldl (· + ·) 0

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println s!"{show' (mkL true n)} {sumN (mkL false n)}"
end A1313

namespace A1314
@[noinline] def Bench.pin (x : α) : BaseIO α := pure x
/-! Chapter 06 A4 fixture A1314: chapter 03 D72 F6's boundary rule (i) at a root. `v : (b : Bool) → Nat → NS b` returns `n * 2` at `b := true` and `toString n` at `b := false`, so its result class is `Box`; the root `kernel`'s result `List Nat` is fixed by its native Rust signature, and its elements are unboxed from `v`'s results at their own position, so no container crosses the root's boundary. -/
namespace Bench.A1314
abbrev NS : Bool → Type
  | true => Nat
  | false => String
def build (n : Nat) : Nat := n
@[noinline] def v : (b : Bool) → Nat → NS b
  | true, n => n * 2
  | false, n => toString n
def kernel (n : Nat) : List Nat := [v true n, v true (n + 1), String.length (v false n)]
def render (xs : List Nat) : String := toString xs
end Bench.A1314

def caseMain (args : List String) : IO UInt32 := do
  match args with
  | [n] =>
    let input ← Bench.pin (Bench.A1314.build n.toNat!)
    let out ← Bench.pin (Bench.A1314.kernel input)
    IO.println (Bench.A1314.render out)
    return 0
  | _ => IO.eprintln "usage: <prog> SIZE"; return 2
end A1314

namespace A1315

abbrev LTy : Bool → Type
  | true => List Nat
  | false => Nat
abbrev NS : Bool → Type
  | true => Nat
  | false => String
@[noinline] def g : (b : Bool) → List Nat → LTy b
  | true, xs => xs
  | false, xs => xs.length
@[noinline] def sz : (b : Bool) → LTy b → Nat
  | true, xs => xs.foldl (· + ·) 0
  | false, n => n
@[noinline] def mk : (b : Bool) → Nat → NS b
  | true, n => n
  | false, n => toString n

def caseMain (args : List String) : IO Unit := do
  let k := args.length
  let native := List.range (k + 2)
  IO.println (sz true (g true native) + sz true (g true [mk true (k + 3), 1]))
  IO.println (sz false (g false native) + String.length (mk false k))
end A1315

namespace A1316

@[noinline] def pairs (s : String) : List (Σ b : Bool, if b then Nat else Char) :=
  s.toList.map fun c => if c.toNat % 2 == 0 then ⟨true, c.toNat⟩ else ⟨false, c⟩
@[noinline] def score (ps : List (Σ b : Bool, if b then Nat else Char)) : Nat :=
  ps.foldl (fun acc p => match p with
    | ⟨true, n⟩ => acc + (show Nat from n)
    | ⟨false, c⟩ => acc + (if c.isLower then 1 else 100)) 0

def caseMain (args : List String) : IO Unit := do
  let s := "hello" ++ String.join args
  let ps := pairs s
  IO.println s!"{score ps} {ps.length}"
end A1316

namespace A1317

abbrev LS : Bool → Type
  | true => List Char
  | false => List String
@[noinline] def mkLS : Nat → (b : Bool) → LS b
  | n, true => if n % 2 == 0 then ['a', 'c'] else ['b', 'd']
  | n, false => ["s", toString n]

def caseMain (args : List String) : IO Unit := do
  let n := args.length
  IO.println (String.mk (mkLS n true))
  IO.println (String.intercalate "," (mkLS n false))
end A1317

def main : IO Unit := do
  IO.println "-- A1305"
  A1305.caseMain ["x", "y"]
  IO.println "-- A1306"
  A1306.caseMain ["x", "y"]
  IO.println "-- A1307"
  A1307.caseMain ["x", "y"]
  IO.println "-- A1308"
  A1308.caseMain ["x", "y"]
  IO.println "-- A1311"
  A1311.caseMain ["x", "y"]
  IO.println "-- A1312"
  A1312.caseMain ["x", "y"]
  IO.println "-- A1313"
  A1313.caseMain ["x", "y"]
  IO.println "-- A1314"
  let c ← A1314.caseMain ["7"]
  IO.println s!"exit {c}"
  IO.println "-- A1315"
  A1315.caseMain ["x", "y"]
  IO.println "-- A1316"
  A1316.caseMain ["x", "y"]
  IO.println "-- A1317"
  A1317.caseMain ["x", "y"]
