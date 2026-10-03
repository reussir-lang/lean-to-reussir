import Std.Data.HashMap

/-! Runtime test: `Nat` and `Int` values (small and big) stored in every
kind of container lean2rr builds, as one word each: structure fields
(updated in place and shared), inductive constructors, `Array Nat`,
arrays of structures, `List`, `Option`, `Prod`, a `HashMap`, `IO.Ref`
(get, set, modify, swap, take), `ST.Ref`, closures, `Thunk` and `Task`
results, and values that go through uniform code (`Box`, an existential).
Big values are created, shared, overwritten and dropped many times, and
every result is printed. -/


structure Tally where
  count : Nat
  total : Nat
  delta : Int
  tag : UInt8
  deriving Repr, BEq, Hashable, Inhabited

inductive Tree where
  | leaf
  | node (l : Tree) (key : Nat) (val : Int) (r : Tree)

def Tree.insert : Tree → Nat → Int → Tree
  | .leaf, k, v => .node .leaf k v .leaf
  | .node l k' v' r, k, v =>
    if k < k' then .node (l.insert k v) k' v' r
    else if k' < k then .node l k' v' (r.insert k v)
    else .node l k (v' + v) r

def Tree.sum : Tree → Nat × Int
  | .leaf => (0, 0)
  | .node l k v r =>
    let (a, b) := l.sum
    let (c, d) := r.sum
    (a + k + c, b + v + d)

structure Shown where
  {α : Type}
  val : α
  render : α → String

def big (k : Nat) : Nat := 2 ^ (70 + k % 3)

def stSum (vals : List Nat) : Nat := runST fun σ => do
  let s : ST.Ref σ Nat ← ST.mkRef (big 0)
  for x in vals do
    s.modify (· * 3 + x)
  s.get

@[noinline] def step (a : Tally) (x : Nat) : Tally :=
  { a with count := a.count + 1, total := a.total + x, delta := a.delta - (x : Int) }

def main (args : List String) : IO Unit := do
  let k := args.length
  let vals : List Nat := (List.range 40).map fun i => if i % 3 == 0 then big i + i else i * 1000003
  -- structure fields, updated in place and shared
  let mut acc : Tally := { count := 0, total := big k, delta := -(big k : Int), tag := 7 }
  let mut snapshots : Array Tally := #[]
  for x in vals do
    acc := step acc x
    if x % 5 == 0 then snapshots := snapshots.push acc
  IO.println s!"acc {repr acc} snapshots {snapshots.size} first {repr snapshots[0]!} eq {snapshots[0]! == snapshots[0]!} hash {hash acc}"
  -- a tree of Nat keys and Int values
  let t := vals.foldl (fun t x => t.insert (x % 97 + (if x > 1000000000 then big 1 else 0)) (x : Int)) Tree.leaf
  IO.println s!"tree sum {t.sum}"
  -- Array Nat and arrays of structures
  let mut arr : Array Nat := Array.replicate 8 (big 2)
  for i in [0:20] do
    arr := arr.modify (i % 8) (· + i * big 0)
    arr := arr.push (if i % 2 == 0 then big i else i)
  arr := arr.swapIfInBounds 0 (arr.size - 1)
  IO.println s!"arr {arr.toList} sum {arr.foldl (· + ·) 0} pop {arr.pop.size} back {arr.back?}"
  let accs : Array Tally := (List.range 10).toArray.map fun i => { count := i, total := big i, delta := (i : Int) - (big i : Int), tag := i.toUInt8 }
  IO.println s!"accs {accs.foldl (fun s a => s + a.total) 0} {(accs.map (·.delta)).toList}"
  -- List, Option, Prod
  let opts : List (Option Nat) := vals.map fun x => if x % 2 == 0 then some x else none
  let pairs : List (Nat × Int) := vals.map fun x => (x, -(x : Int))
  IO.println s!"opts {opts.filterMap id |>.length} {(opts.filterMap id).foldl (· + ·) 0} pairs {pairs.foldl (fun s p => s + p.2) 0}"
  -- HashMap with Nat keys and values
  let mut m : Std.HashMap Nat Nat := {}
  for x in vals do
    m := m.insert x (x * x)
    m := m.insert (x % 7) (m.getD (x % 7) 0 + x)
  IO.println s!"map {m.size} {m.getD (big 0) 0} {m.getD 3 0} {(m.toList.map (·.2)).foldl (· + ·) 0}"
  -- IO.Ref: get, set, modify, swap, take
  let r ← IO.mkRef (big 1)
  for x in vals do
    r.modify (· + x)
  let old ← r.swap 5
  r.set (big 2 + (← r.get))
  let taken ← r.modifyGet fun v => (v, 0)
  IO.println s!"ref old {old} taken {taken} now {← r.get}"
  let ri ← IO.mkRef (-(big 1 : Int))
  for x in vals do
    ri.modify (· - (x : Int))
  IO.println s!"int ref {← ri.get}"
  -- ST.Ref
  let stv := stSum vals
  IO.println s!"st {stv % 1000000007}"
  -- closures capturing Nat
  let adders : List (Nat → Nat) := vals.map fun x => fun y => x + y
  IO.println s!"closures {adders.foldl (fun s f => f s) 0}"
  -- Thunk and Task results
  let th : Thunk Nat := Thunk.mk fun _ => vals.foldl (· + ·) (big 2)
  let th2 := th.map (· * 2)
  IO.println s!"thunk {th.get} {th2.get} {th.get}"
  let tasks := (List.range 6).map fun i => Task.spawn fun _ => (List.range 100).foldl (fun s j => s + j * big i) 0
  IO.println s!"tasks {tasks.map Task.get}"
  let io ← IO.asTask (pure (big 1 * big 2))
  match io.get with
  | .ok v => IO.println s!"io task {v}"
  | .error e => IO.println s!"io task error {e}"
  let ti : Task Int := Task.spawn fun _ => -(big 0 : Int) * 3
  IO.println s!"int task {ti.get}"
  -- uniform code: an existential holding Nat and Int
  let shown : List Shown := [⟨big 1, toString⟩, ⟨(5 : Nat), toString⟩, ⟨(-(big 2) : Int), toString⟩, ⟨(-3 : Int), toString⟩, ⟨acc, fun a => toString a.total⟩]
  IO.println s!"shown {shown.map fun s => s.render s.val}"
  -- many short-lived big values (released once each)
  let mut s : Nat := 0
  for i in [0:20000] do
    let b := big i + i
    let p := (b, b * 2)
    s := s + p.2 / b + (if i % 1000 == 0 then b % 1000 else 0)
  IO.println s!"churn {s}"
