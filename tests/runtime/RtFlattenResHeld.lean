/-! Runtime test: optimization `flatten-structs` leaves a loop alone when its
record holds a resource in a field whose type depends on a value (`σ.Res`,
`lcAny` in mono code): a file handle, and a promise. The whole-program
analysis `ResourceFlow` follows the handle from `IO.FS.Handle.mk` and the
promise from `IO.Promise.new` into the records (as constructor arguments),
so every declaration that takes or returns such a record keeps Lean's code,
and so Lean's inferred borrows (`RtFlattenResHeld.l2r-debug`), and the
resources are released when native Lean releases them:
- `heldLoop`: k steps over a record `⟨count, handle⟩`, each writing a line
  through the handle and reading the file back (the lines stay in the
  handle's buffer while the record lives), returning the record;
- `heldLast`: a helper that writes through the record's handle, its last
  use of the record, and then reads the file;
- `promLoop`, `promCheck`: the same with a promise, whose result task the
  helper asks about after its last use of the record (the last reference to
  an unresolved promise resolves the task with `none`). -/

structure Strat where
  Res : Type
  put : Res → String → IO Unit

structure HSt (σ : Strat) where
  count : Nat
  res : σ.Res

@[noinline] def heldLoop (σ : Strat) (path : System.FilePath) : Nat → HSt σ → Nat → IO (Nat × HSt σ)
  | 0, st, acc => pure (acc, st)
  | k + 1, st, acc => do
    σ.put st.res s!"line {st.count}\n"
    let len := (← IO.FS.readFile path).length
    heldLoop σ path k { st with count := st.count + 1 } (acc + len)

@[noinline] def heldLast (σ : Strat) (st : HSt σ) (path : System.FilePath) : IO String := do
  σ.put st.res "last"
  IO.FS.readFile path

def handleStrat : Strat := ⟨IO.FS.Handle, fun h s => h.putStr s⟩

structure PStrat where
  Res : Type
  task : Res → Task (Option Nat)
  tag : Nat

structure PSt (σ : PStrat) where
  count : Nat
  res : σ.Res

@[noinline] def promLoop (σ : PStrat) : Nat → PSt σ → Nat → IO (Nat × PSt σ)
  | 0, st, acc => pure (acc, st)
  | k + 1, st, acc => do
    let f ← IO.hasFinished (σ.task st.res)
    promLoop σ k { st with count := st.count + σ.tag } (acc + if f then 1 else 0)

@[noinline] def promCheck (σ : PStrat) (st : PSt σ) : IO Bool := do
  let t := σ.task st.res
  IO.hasFinished t

def promStrat : PStrat := ⟨IO.Promise Nat, fun p => p.result?, 1⟩

def main (args : List String) : IO Unit := do
  let k := (args.head?.bind String.toNat?).getD 3
  let dir : System.FilePath := "rtflattenresheld-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let σ := handleStrat
  let h ← IO.FS.Handle.mk a .write
  let (acc, st) ← heldLoop σ a k ⟨0, h⟩ 0
  IO.println s!"loop read {acc}, count {st.count}"
  IO.println s!"last read [{← heldLast σ st a}]"
  IO.println s!"after {(← IO.FS.readFile a).length}"
  let τ := promStrat
  let p ← IO.Promise.new (α := Nat)
  let t ← IO.mapTask (fun o => pure (o.getD 7)) p.result? (sync := true)
  let (pacc, pst) ← promLoop τ k ⟨0, p⟩ 0
  IO.println s!"promise loop finished {pacc}, count {pst.count}"
  IO.println s!"promise: finished inside {← promCheck τ pst}"
  match ← IO.wait t with
  | .ok v => IO.println s!"after: {v}"
  | .error e => IO.println s!"after: error {e}"
