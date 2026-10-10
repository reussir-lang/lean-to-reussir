/-! Runtime test: a handle reaches a loop record's field whose type depends
on a value (`σ.Res`, `lcAny` in mono code) only through an `IO.Ref`:
`stash` sets the reference, `runRef` swaps the handle out, writes through
it and moves it into the record of `spin`. The analysis `ResourceFlow`
joined an extern's arguments only with its result, and `ST.Ref.set`'s
result (`EST.Out ε σ Unit`) has no node, so the stored handle joined
nothing (review of the analysis, finding 2): the record looked
resource-free and `flatten-structs` split `spin`. Natively `spin`'s record
is owned (it is rebuilt at each step) and released when the last step
starts, so the handle is flushed and closed before `IO.FS.readFile`: the
read sees `data`. Split, the worker's handle parameter was borrowed, the
caller kept the handle until `spin` returned, and the read saw nothing.
An extern's arguments are now joined with each other too
(`RtFlattenResRef.l2r-debug`: `spin` is left alone). -/

structure Strat where
  Res : Type
  put : Res → String → IO Unit

structure HSt (σ : Strat) where
  count : UInt64
  res : σ.Res

@[noinline] def spin (σ : Strat) (path : System.FilePath) : Nat → HSt σ → IO String
  | 0, _ => IO.FS.readFile path
  | k + 1, st => spin σ path k { st with count := st.count + 1 }

@[noinline] def mkEmpty (σ : Strat) : IO (IO.Ref (Option σ.Res)) := IO.mkRef none

@[noinline] def stash (σ : Strat) (r : IO.Ref (Option σ.Res)) (x : σ.Res) : IO Unit :=
  r.set (some x)

@[noinline] def runRef (σ : Strat) (path : System.FilePath) (k : Nat) (r : IO.Ref (Option σ.Res)) :
    IO String := do
  match ← r.swap none with
  | some res =>
    σ.put res "data"
    spin σ path k ⟨0, res⟩
  | none => pure "empty"

def handleStrat : Strat := ⟨IO.FS.Handle, fun h s => h.putStr s⟩

def main (args : List String) : IO Unit := do
  let k := (args.head?.bind String.toNat?).getD 3
  let dir : System.FilePath := "rtflattenresref-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let h ← IO.FS.Handle.mk a .write
  let r ← mkEmpty handleStrat
  stash handleStrat r h
  IO.println s!"read [{← runRef handleStrat a k r}]"
  IO.println s!"after {(← IO.FS.readFile a).length}"
