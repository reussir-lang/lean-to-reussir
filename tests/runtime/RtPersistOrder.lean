/-! Runtime test: the tasks of a closed term, which it waits for when it is
first evaluated (`lean_mark_persistent`), run in the order the native
workers take them from their queue (by priority, then first in, first out:
here the order they were created in), whatever order the walk reaches them
in. With one worker thread (`RtPersistOrder.pipe`) the traces (stderr)
show that order: tasks created in field order and in reverse, by
`List.map` and `Array.map`, in a tree, a closure, a thunk, and a task that
replaces the task held by a reference next to it (the walk reads the
reference after waiting for the task, as natively).
From the round-7 review, area L, findings RV7L-04 and RV7L-06. -/
@[noinline] def pairRev (_ : Unit) : Task Nat × Task Nat :=
  let t1 := Task.spawn fun _ => dbgTrace "pair: one" fun _ => 1
  let t2 := Task.spawn fun _ => dbgTrace "pair: two" fun _ => 2
  (t2, t1)

structure R where
  a : Task Nat
  n : Nat
  b : Task Nat
  s : String
  c : Task Nat

@[noinline] def rec3 (_ : Unit) : R :=
  let x := Task.spawn fun _ => dbgTrace "rec: x" fun _ => 10
  let y := Task.spawn fun _ => dbgTrace "rec: y" fun _ => 20
  let z := Task.spawn fun _ => dbgTrace "rec: z" fun _ => 30
  { a := z, n := 5, b := x, s := "s", c := y }

@[noinline] def listRev (_ : Unit) : List (Task Nat) :=
  let ts := (List.range 4).map fun i => Task.spawn fun _ => dbgTrace s!"list: {i}" fun _ => i
  ts.reverse

@[noinline] def arr (_ : Unit) : Array (Task Nat) :=
  #[Task.spawn fun _ => dbgTrace "arr[0]" fun _ => 0, Task.spawn fun _ => dbgTrace "arr[1]" fun _ => 1,
    Task.spawn fun _ => dbgTrace "arr[2]" fun _ => 2]

inductive Tree where
  | leaf (t : Task Nat)
  | node (l r : Tree)

@[noinline] def tree (_ : Unit) : Tree :=
  let t1 := Task.spawn fun _ => dbgTrace "tree: 1" fun _ => 1
  let t2 := Task.spawn fun _ => dbgTrace "tree: 2" fun _ => 2
  let t3 := Task.spawn fun _ => dbgTrace "tree: 3" fun _ => 3
  .node (.node (.leaf t1) (.leaf t2)) (.leaf t3)

@[noinline] def sumTree : Tree → Nat
  | .leaf t => t.get
  | .node l r => sumTree l + sumTree r

@[noinline] def opts (_ : Unit) : Array (Option (Task Nat)) :=
  #[some (Task.spawn fun _ => dbgTrace "opt: 0" fun _ => 0), none,
    some (Task.spawn fun _ => dbgTrace "opt: 2" fun _ => 2)]

@[noinline] def clos (_ : Unit) : Nat → Nat :=
  let a := Task.spawn fun _ => dbgTrace "clos: a" fun _ => 1
  let b := Task.spawn fun _ => dbgTrace "clos: b" fun _ => 2
  let c := Task.spawn fun _ => dbgTrace "clos: c" fun _ => 3
  fun x => x + a.get * 100 + b.get * 10 + c.get

@[noinline] def thunk (_ : Unit) : Thunk Nat :=
  let a := Task.spawn fun _ => dbgTrace "thunk: a" fun _ => 1
  let b := Task.spawn fun _ => dbgTrace "thunk: b" fun _ => 2
  Thunk.mk fun _ => a.get * 10 + b.get

-- Created in element order.
@[noinline] def listMap (_ : Unit) : List (Task Nat) :=
  (List.range 4).map fun i => Task.spawn fun _ => dbgTrace s!"listMap: {i}" fun _ => i

@[noinline] def arrMap (_ : Unit) : Array (Task Nat) :=
  (Array.range 4).map fun i => Task.spawn fun _ => dbgTrace s!"arrMap: {i}" fun _ => i

-- Created in field order inside one initializer (not closed terms of their own).
unsafe def mkPairU (_ : Unit) : Task Nat × Task Nat := unsafeBaseIO do
  let k ← IO.mkRef 3
  let a := Task.spawn fun _ => dbgTrace "fifo: first created" fun _ => unsafeBaseIO k.get
  let b := Task.spawn fun _ => dbgTrace "fifo: second created" fun _ => unsafeBaseIO k.get
  pure (a, b)
@[implemented_by mkPairU] opaque mkPair (u : Unit) : Task Nat × Task Nat

-- A reference holding T1 (created first) and a task t0 that replaces it
-- with T2: T1 runs first, then t0, then T2.
unsafe def mkWriteU (_ : Unit) : IO.Ref (Task Nat) × Task Nat := unsafeBaseIO do
  let r ← IO.mkRef (Task.spawn fun _ => dbgTrace "write: T1 (replaced)" fun _ => 1)
  let t0 := Task.spawn fun _ => dbgTrace "write: t0 writes" fun _ =>
    unsafeBaseIO (do r.set (Task.spawn fun _ => dbgTrace "write: T2 (written)" fun _ => 2); pure 0)
  pure (r, t0)
@[implemented_by mkWriteU] opaque mkWrite (u : Unit) : IO.Ref (Task Nat) × Task Nat

def main : IO Unit := do
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  IO.eprintln "start"
  let p := pairRev ()
  IO.eprintln s!"pair {p.1.get} {p.2.get}"
  let r := rec3 ()
  IO.eprintln s!"rec {r.a.get} {r.b.get} {r.c.get} {r.n} {r.s}"
  let l := listRev ()
  IO.eprintln s!"list {l.map Task.get}"
  let a := arr ()
  IO.eprintln s!"arr {a.map Task.get}"
  let t := tree ()
  IO.eprintln s!"tree {sumTree t}"
  let o := opts ()
  IO.eprintln s!"opts {o.map (·.map Task.get)}"
  let f := clos ()
  IO.eprintln s!"clos {f 1000}"
  let th := thunk ()
  IO.eprintln s!"thunk {th.get}"
  let lm := listMap ()
  IO.eprintln s!"listMap {lm.map Task.get}"
  let am := arrMap ()
  IO.eprintln s!"arrMap {am.map Task.get}"
  let (fa, fb) := mkPair ()
  IO.eprintln s!"fifo {fa.get} {fb.get}"
  let (wr, wt) := mkWrite ()
  IO.eprintln s!"write {wt.get} {(← wr.get).get}"
  let _ ← IO.wait busy
