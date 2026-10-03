/-! Runtime test: a closed term's tasks are waited for, when it is first
evaluated, in the order of native `lean_mark_persistent`, which pushes an
object's fields (a closure's captured values, an array's elements) in order
on its stack and looks at the last one first. With one worker thread, busy
with another task (`RtPersistOrder.pipe`), the tasks run in that order, as
their traces show (stderr). -/
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
  let _ ← IO.wait busy
