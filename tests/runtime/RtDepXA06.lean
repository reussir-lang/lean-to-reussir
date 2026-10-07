/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `A1096`: Site rule (f): join point parameters close only through their own
  type
- `A1097`: CSLib E01's toStateM: a free state monad interpreted by `liftM`
  into `StateM` (a rank-2 interpreter): T13's run 1 finds `PUnit` and `Nat`
  on one `lcAny` slot and Box mode's rewrite does not type it, support-
  status ...
- `A1098`: Two existential pairs, `(Nat, List Nat)` and `(Nat, Nat)`:
  `List.toString`'s K8 copy is a partial application of a D-2 forwarder
  whose remaining domain, which no argument fills, needs a coercion
- `A1099`: A continuation in a laid-out structure (`ContS r α`, its field
  `run : (α → r) → r`) run at two answer types: Lower's tree breaks Rule
  17.6 (an `RType.fnRef` outside the annotation of a `let` ...
- `A1200`: A1099's continuation structure (`ContS r α`, its field `run : (α
  → r) → r`) run at one answer type: `sumTo`'s call `sumTo k` returns a
  function value at a result generic no parameter names, whose T14 ...
- `A1202`: Condition 2 at a repeated forwarder argument: `run` passes a
  closure capturing a tree `t` to the D-2 forwarder `hopS f n := keepS n f
  f`, which passes it to `keepS`'s stored (consumed, class-typed) `g` ...
- `A587`: Several drops at one point in Lean's order: a closure or a thunk
  that captures a list by reference (a B11 holder) and the list (its root)
  both last used by one call, in either argument order, ...
- `A612`: Drops at one point in Lean's order with a repeated argument (M5,
  D66, `Lem-M5-order`
- `A743`: `Thunk (IO α)` values.
- `A765Field`: The closure of Lean's debugging aids reaches its row whatever
  its spelling. Mode "field".
- `A765Op`: The closure of Lean's debugging aids reaches its row whatever
  its spelling. Mode "op". -/

namespace A1096

@[noinline] def mkQ : (c d : Bool) → if c then List (if d then Nat else String) else Nat
  | true, true => ([4, 5] : List Nat) | true, false => (["xy"] : List String) | false, _ => (5 : Nat)
@[noinline] def getJ : (c d : Bool) → (if c then List (if d then Nat else String) else Nat) → Nat
  | true, d, xs =>
    let ys : List (if d then Nat else String) := match d, xs with
      | true, zs => (let ws : List Nat := zs; ((ws.map (· + 1)) : List Nat))
      | false, zs => zs
    let n := ys.length
    match d, ys with
    | true, (h :: _) => n + (show Nat from h)
    | _, _ => n * 100
  | false, _, n => n
def caseMain (a : List String) : IO Unit := do
  let c := a.length < 100
  for d in [a.isEmpty, !a.isEmpty] do
    IO.println s!"{getJ c d (mkQ c d)}"
end A1096

namespace A1097

inductive FreeM (F : Type → Type) (α : Type) where
  | pure : α → FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
def FreeM.bind {F : Type → Type} {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op k, f => .liftBind op fun z => FreeM.bind (k z) f
instance {F : Type → Type} : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind
def FreeM.lift {F : Type → Type} {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure
inductive StateF (σ : Type) : Type → Type where
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
inductive ReaderF (σ : Type) : Type → Type where
  | read : ReaderF σ σ
def runS {σ α : Type} : FreeM (StateF σ) α → σ → α × σ
  | .pure a, s => (a, s)
  | .liftBind .get k, s => runS (k s) s
  | .liftBind (.set s') k, _ => runS (k PUnit.unit) s'
def runR {σ α : Type} : FreeM (ReaderF σ) α → σ → α
  | .pure a, _ => a
  | .liftBind .read k, s => runR (k s) s
def counter : Nat → FreeM (StateF Nat) Nat
  | 0 => .lift .get
  | k + 1 => do
    let s ← .lift .get
    let _ ← FreeM.lift (StateF.set (s + k))
    counter k
def FreeM.liftM {m : Type → Type} [Monad m] {F : Type → Type} {α : Type} (interp : {ι : Type} → F ι → m ι) : FreeM F α → m α
  | .pure a => Pure.pure a
  | .liftBind op cont => interp op >>= fun r => (cont r).liftM interp
def stateInterp {σ α : Type} : StateF σ α → StateM σ α
  | .get => MonadStateOf.get
  | .set s => MonadStateOf.set s
def caseMain (args : List String) : IO Unit := do
  for n in args.filterMap String.toNat? do
    let st := ((counter n).liftM stateInterp).run 1
    IO.println s!"n={n}: {st.1} {st.2}"
end A1097

namespace A1098

structure AnyS where
  {α : Type}
  [inst : ToString α]
  val : α
@[noinline] def AnyS.show (s : AnyS) : String := s.inst.toString s.val
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 4
  let xs : List AnyS := [
    ⟨((n : Nat), ([n] : List Nat))⟩,
    ⟨((n : Nat), (n : Nat))⟩]
  IO.println (xs.map (·.show))
end A1098

namespace A1099

structure ContS (r α : Type) where
  run : (α → r) → r
@[noinline] def ContS.ret (a : α) : ContS r α := ⟨fun k => k a⟩
@[noinline] def ContS.bind (m : ContS r α) (f : α → ContS r β) : ContS r β := ⟨fun k => m.run (fun a => (f a).run k)⟩
@[noinline] def ContS.go (m : ContS r r) : r := m.run id
@[noinline] def sumTo (n : Nat) : ContS r Nat :=
  match n with
  | 0 => ContS.ret 0
  | k + 1 => (sumTo k).bind (fun s => ContS.ret (s + k + 1))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((sumTo n).go)
  IO.println (((sumTo n).bind (fun s => ContS.ret (toString s ++ "!"))).go)
end A1099

namespace A1200

structure ContS (r α : Type) where
  run : (α → r) → r
@[noinline] def ContS.ret (a : α) : ContS r α := ⟨fun k => k a⟩
@[noinline] def ContS.bind (m : ContS r α) (f : α → ContS r β) : ContS r β := ⟨fun k => m.run (fun a => (f a).run k)⟩
@[noinline] def ContS.go (m : ContS r r) : r := m.run id
@[noinline] def sumTo (n : Nat) : ContS r Nat :=
  match n with
  | 0 => ContS.ret 0
  | k + 1 => (sumTo k).bind (fun s => ContS.ret (s + k + 1))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((sumTo n).go)
end A1200

namespace A1202

inductive T where
  | leaf
  | node (l : T) (n : Nat) (r : T)
def T.sum : T → Nat
  | .leaf => 0
  | .node l n r => l.sum + n + r.sum
def mkT : Nat → T
  | 0 => .leaf
  | k + 1 => .node (mkT k) k .leaf
@[noinline] def inc (x : Nat) : Nat := ([x, 1].foldl (· + ·) 0)
mutual
def keepS : Nat → (Nat → Nat) → (Nat → Nat) → List (Nat → Nat) × Nat
  | 0, g, h => ([g], h 0)
  | n + 1, g, h => let r := keepS n g h; (g :: r.1 ++ (if n > 100 then (hopS inc n).1 else []), h r.2)
@[inline] def hopS (f : Nat → Nat) (n : Nat) : List (Nat → Nat) × Nat := keepS n f f
end
@[noinline] def run (t : T) (n : Nat) : List Nat × Nat :=
  let r := hopS (fun x => x + t.sum) n
  (r.1.map (· 1), r.2)
def caseMain (args : List String) : IO Unit := do
  let k := args.length
  IO.println (run (mkT (k + 3)) (k + 2))
end A1202

namespace A587
@[noinline] def Bench.pin (x : α) : BaseIO α := pure x
/-! Chapter 06 A4 fixture A587: several drops at one point in Lean's order (chapter 04 M5, D66): a
closure or a thunk that captures a list by reference (a B11 holder) and the list (its root) both last
used by one call, in either argument order, then a call that allocates; two lists and a thunk over one of them dying
at one call; and values dying at the top of an arm. Each holder is dropped before its root whatever the
argument order, and every value is Lean's. -/
namespace Bench.A587
def build (n : Nat) : Nat := n
@[noinline] def both (g : Nat → Nat) (xs : List Nat) : Nat := g 1 + xs.length
@[noinline] def both' (xs : List Nat) (g : Nat → Nat) : Nat := g 2 + xs.length * 2
@[noinline] def three (a b : List Nat) (t : Thunk Nat) : Nat := a.length + b.length * 3 + t.get
@[noinline] def k1 (n : Nat) : Nat :=
  let xs := List.range (n % 9)
  let g := fun k => k + xs.length
  let a := g 5
  let r := both g xs
  r + a + (List.range (n % 4 + 2)).length
@[noinline] def k2 (n : Nat) : Nat :=
  let xs := List.range (n % 8)
  let g := fun k => k * 2 + xs.length
  let a := g n
  let r := both' xs g + a
  r + (List.replicate (n % 3 + 1) n).length
@[noinline] def k3 (n : Nat) : Nat :=
  let a := List.range (n % 6)
  let b := List.range (n % 5 + 1)
  let t : Thunk Nat := Thunk.mk (fun _ => a.length + b.length)
  let r := three a b t
  r + (List.range (n % 3 + 1)).length
@[noinline] def k4 (n : Nat) : Nat :=
  let a := List.range (n % 6)
  let b := List.range (n % 4)
  match n % 3 with
  | 0 => (List.range 3).length + n
  | 1 => a.length + b.length + (List.range 2).length
  | _ => b.length * 2 + a.length
@[noinline] def useTX (t : Thunk Nat) (xs : List Nat) : Nat := t.get + xs.length
@[noinline] def useXT (xs : List Nat) (t : Thunk Nat) : Nat := t.get * 2 + xs.length
@[noinline] def k5 (n : Nat) : Nat :=
  let xs := List.range (n % 9)
  let t : Thunk Nat := Thunk.mk (fun _ => xs.length * 2 + n)
  let a := t.get
  let r := useTX t xs
  r + a + (List.range (n % 4 + 2)).length
@[noinline] def k6 (n : Nat) : Nat :=
  let xs := List.range (n % 7)
  let t : Thunk Nat := Thunk.mk (fun _ => xs.length + 3)
  let a := t.get
  let r := useXT xs t
  r + a + (List.replicate (n % 3 + 1) n).length
def kernel (n : Nat) : List Nat := [k1 n, k2 n, k3 n, k4 n, k5 n, k6 n]
def render (xs : List Nat) : String := toString xs
end Bench.A587

def caseMain (args : List String) : IO UInt32 := do
  match args with
  | [n] =>
    let input ← Bench.pin (Bench.A587.build n.toNat!)
    let out ← Bench.pin (Bench.A587.kernel input)
    IO.println (Bench.A587.render out)
    return 0
  | _ => IO.eprintln "usage: <prog> SIZE"; return 2
end A587

namespace A612

@[noinline] def w (a b c : IO.FS.Handle) : IO Unit := do
  a.putStr "1"; b.putStr "2"; c.putStr "3"
@[noinline] def w2 (a b : IO.FS.Handle) : IO Unit := do
  a.putStr "x"; b.putStr "y"
def caseMain : IO Unit := do
  IO.FS.writeFile "out.txt" ""
  let h1 ← IO.FS.Handle.mk "out.txt" .append
  let h2 ← IO.FS.Handle.mk "out.txt" .append
  w h1 h2 h1
  let s ← IO.FS.readFile "out.txt"
  IO.println s
  IO.FS.writeFile "out3.txt" ""
  let k1 ← IO.FS.Handle.mk "out3.txt" .append
  let k2 ← IO.FS.Handle.mk "out3.txt" .append
  w k2 k1 k2
  let s3 ← IO.FS.readFile "out3.txt"
  IO.println s3
  IO.FS.writeFile "out2.txt" ""
  let g1 ← IO.FS.Handle.mk "out2.txt" .append
  let g2 ← IO.FS.Handle.mk "out2.txt" .append
  w2 g1 g2
  let s2 ← IO.FS.readFile "out2.txt"
  IO.println s2
end A612

namespace A743

structure Job where
  name : String
  run : Thunk (IO Nat)

def thunkIO (n : Nat) : Thunk (IO Nat) := Thunk.mk fun _ => pure n
def thunkStr (s : String) : Thunk (IO String) := Thunk.mk fun _ => pure (s ++ "!")
def thunkSay (s : String) : Thunk (IO Unit) := Thunk.mk fun _ => IO.println s!"say {s}"
def thunkConst : Thunk (IO Nat) := Thunk.mk fun _ => pure 42

def caseMain (args : List String) : IO Unit := do
  let n := (args.headD "7").toNat!
  let t := thunkIO n
  IO.println s!"{← t.get} {← t.get}"
  let s := thunkStr s!"s{n}"
  IO.println s!"{← s.get} {← s.get}"
  let u := thunkSay s!"u{n}"
  u.get; u.get
  IO.println s!"{← thunkConst.get}"
  let jobs := [Job.mk "a" (thunkIO (n + 1)), Job.mk "b" thunkConst]
  for j in jobs do
    IO.println s!"{j.name} {← j.run.get} {← j.run.get}"
end A743

namespace A765Field

structure Tracer where
  tag : String
  body : Unit → List String

structure Step where
  g : Nat → Nat

@[noinline] def mkTracer (n : Nat) : Tracer := { tag := s!"t{n}", body := fun _ => [toString n, "x"] }
@[noinline] def viaField (t : Tracer) : List String := dbgTrace t.tag t.body
@[noinline] def sleepField (t : Tracer) : List String := dbgSleep 1 t.body
@[noinline] def inOp (n : Nat) : Nat := n + dbgTrace "op" (fun _ => n + 1)
@[noinline] def sharedField (s : Step) (n : Nat) : Nat := (dbgTraceIfShared "shared" s.g) n
@[noinline] def viaRef (n : Nat) : IO Nat := do
  let r ← IO.mkRef (fun (_ : Unit) => n * 7)
  let g ← r.get
  let h ← r.get
  return dbgTrace "ref" g + dbgSleep 1 h

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.drop 1).headD "3" |>.toNat!
  match args.headD "" with
  | "field" => IO.println (viaField (mkTracer n))
  | "sleep" => IO.println (sleepField (mkTracer n))
  | "op" => IO.println (inOp n)
  | "ref" => IO.println (← viaRef n)
  | "shared" => IO.println (sharedField { g := (· + n) } n)
  | _ => IO.println "none"
  return 0
end A765Field

namespace A765Op

structure Tracer where
  tag : String
  body : Unit → List String

structure Step where
  g : Nat → Nat

@[noinline] def mkTracer (n : Nat) : Tracer := { tag := s!"t{n}", body := fun _ => [toString n, "x"] }
@[noinline] def viaField (t : Tracer) : List String := dbgTrace t.tag t.body
@[noinline] def sleepField (t : Tracer) : List String := dbgSleep 1 t.body
@[noinline] def inOp (n : Nat) : Nat := n + dbgTrace "op" (fun _ => n + 1)
@[noinline] def sharedField (s : Step) (n : Nat) : Nat := (dbgTraceIfShared "shared" s.g) n
@[noinline] def viaRef (n : Nat) : IO Nat := do
  let r ← IO.mkRef (fun (_ : Unit) => n * 7)
  let g ← r.get
  let h ← r.get
  return dbgTrace "ref" g + dbgSleep 1 h

def caseMain (args : List String) : IO UInt32 := do
  let n := (args.drop 1).headD "3" |>.toNat!
  match args.headD "" with
  | "field" => IO.println (viaField (mkTracer n))
  | "sleep" => IO.println (sleepField (mkTracer n))
  | "op" => IO.println (inOp n)
  | "ref" => IO.println (← viaRef n)
  | "shared" => IO.println (sharedField { g := (· + n) } n)
  | _ => IO.println "none"
  return 0
end A765Op

def main : IO Unit := do
  IO.println "-- A1096"
  A1096.caseMain ["x"]
  IO.println "-- A1097"
  A1097.caseMain ["3"]
  IO.println "-- A1098"
  A1098.caseMain ["3"]
  IO.println "-- A1099"
  A1099.caseMain ["5"]
  IO.println "-- A1200"
  A1200.caseMain ["5"]
  IO.println "-- A1202"
  A1202.caseMain ["x", "y"]
  IO.println "-- A587"
  let c ← A587.caseMain ["12"]
  IO.println s!"exit {c}"
  IO.println "-- A612"
  A612.caseMain
  IO.println "-- A743"
  A743.caseMain ["12"]
  IO.println "-- A765Field"
  let c ← A765Field.caseMain ["field"]
  IO.println s!"exit {c}"
  IO.println "-- A765Op"
  let c ← A765Op.caseMain ["op"]
  IO.println s!"exit {c}"
