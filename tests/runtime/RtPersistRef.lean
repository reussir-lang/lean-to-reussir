/-! Runtime test: a closed term that holds references (`IO.Ref`, made with
unsafe IO behind `implemented_by`) is walked through them when it is first
evaluated, as native `lean_mark_persistent` does (it pushes a reference's
value): the tasks a reference holds have run before the term is used,
whether the reference is the term itself, a field of a structure, or holds
a structure, an array, a closure or a one-field structure. One worker
thread, busy with another task (`RtPersistRef.pipe`), so the traces
(stderr) come in a fixed order. -/
unsafe def mkRefU (_ : Unit) : IO.Ref (Task Nat) :=
  unsafeBaseIO (IO.mkRef (Task.spawn fun _ => dbgTrace "ref task runs" fun _ => 3))
@[implemented_by mkRefU] opaque mkRef' (u : Unit) : IO.Ref (Task Nat)

structure Holder where
  n : Nat
  r : IO.Ref (Task Nat)
  deriving Nonempty

unsafe def mkHolderU (_ : Unit) : Holder :=
  { n := 7, r := unsafeBaseIO (IO.mkRef (Task.spawn fun _ => dbgTrace "holder task runs" fun _ => 4)) }
@[implemented_by mkHolderU] opaque mkHolder (u : Unit) : Holder

structure Pair where
  a : Task Nat
  b : Task Nat
  deriving Nonempty

unsafe def mkPairRefU (_ : Unit) : IO.Ref Pair :=
  unsafeBaseIO (IO.mkRef { a := Task.spawn fun _ => dbgTrace "pair.a runs" fun _ => 1,
                           b := Task.spawn fun _ => dbgTrace "pair.b runs" fun _ => 2 })
@[implemented_by mkPairRefU] opaque mkPairRef (u : Unit) : IO.Ref Pair

unsafe def mkArrRefU (_ : Unit) : IO.Ref (Array (Task Nat)) :=
  unsafeBaseIO (IO.mkRef #[Task.spawn fun _ => dbgTrace "arr[0] runs" fun _ => 0,
                           Task.spawn fun _ => dbgTrace "arr[1] runs" fun _ => 1])
@[implemented_by mkArrRefU] opaque mkArrRef (u : Unit) : IO.Ref (Array (Task Nat))

unsafe def mkFnRefU (_ : Unit) : IO.Ref (Nat → Nat) :=
  let t := Task.spawn fun _ => dbgTrace "fn task runs" fun _ => 5
  unsafeBaseIO (IO.mkRef fun x => x + t.get)
@[implemented_by mkFnRefU] opaque mkFnRef (u : Unit) : IO.Ref (Nat → Nat)

structure Single where
  t : Task Nat
  deriving Nonempty

unsafe def mkSingleRefU (_ : Unit) : IO.Ref Single :=
  unsafeBaseIO (IO.mkRef { t := Task.spawn fun _ => dbgTrace "one task runs" fun _ => 8 })
@[implemented_by mkSingleRefU] opaque mkSingleRef (u : Unit) : IO.Ref Single

def main : IO Unit := do
  let busy ← IO.asTask (do IO.sleep 50; return 1)
  IO.eprintln "main"
  let r := mkRef' ()
  let t ← r.get
  IO.eprintln "after ref"
  let h := mkHolder ()
  IO.eprintln s!"after holder {h.n}"
  let p ← (mkPairRef ()).get
  IO.eprintln "after pair"
  let a ← (mkArrRef ()).get
  IO.eprintln "after array"
  let f ← (mkFnRef ()).get
  IO.eprintln "after closure"
  let o ← (mkSingleRef ()).get
  IO.eprintln s!"after one {o.t.get}"
  IO.eprintln s!"values {t.get} {(← h.r.get).get} {p.a.get} {p.b.get} {a.map Task.get} {f 1}"
  let _ ← IO.wait busy
