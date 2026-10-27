/-! Runtime test: a value that holds a handle only through a closure, a
thunk or a task, passed to a parameter Lean borrows: natively the caller
holds it until the call returns, so each helper reads the file before the
handle is flushed, and the caller's release after the call flushes it. lean2rr
keeps such an argument until the call returns too (`borrowKeeps` and
`boxedTarget` with `mayHoldRelease`, Lower/Borrow); before, Reussir released
it at its last use inside the helper (`T1` for native's `1`, final `T1` for
`1T`). Shapes: a thunk (`Thunk.get` borrows), a record holding an
`IO.FS.Stream` whose flag only is read, an optional callback, a stream at an
unused parameter, a `ReaderT` context, the record's helper as a function
value (its `_boxed` variant), a task asked `IO.hasFinished`. Every handle
appends, so the file shows the order of the closes. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"rtbc-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) : IO Unit := do
  IO.println s!"{name}: {← IO.FS.readFile s!"rtbc-{name}.txt"}"
  IO.FS.removeFile s!"rtbc-{name}.txt"

/-- A: a thunk (`Thunk.get` borrows). -/
@[noinline] def mkThunk (h : IO.FS.Handle) : Thunk IO.FS.Handle := Thunk.pure h

@[noinline] def useThunk (p : System.FilePath) (t : Thunk IO.FS.Handle) (c : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  if c then t.get.putStr "x"; h1.putStr "y"
  else IO.println s!"  useThunk: {← IO.FS.readFile p}"

/-- B: a structure holding a stream over a file; the helper reads only the
flag. -/
structure Cfg where
  out : IO.FS.Stream
  flag : Bool

@[noinline] def useCfg (p : System.FilePath) (cfg : Cfg) : IO Unit := do
  let h1 ← hnd p "1"
  if cfg.flag then h1.putStr "y"
  IO.println s!"  useCfg: {← IO.FS.readFile p}"

/-- C: an optional callback that captured a handle; the helper only asks
whether there is one. -/
@[noinline] def mkCb (h : IO.FS.Handle) : Option (Unit → IO Unit) := some fun _ => h.putStr "!"

@[noinline] def useCb (p : System.FilePath) (cb : Option (Unit → IO Unit)) : IO Unit := do
  let h1 ← hnd p "1"
  if cb.isNone then h1.putStr "y"
  IO.println s!"  useCb: {← IO.FS.readFile p}"

/-- D: a stream passed to a parameter the helper does not use (an
interface's argument). -/
@[noinline] def useStream (p : System.FilePath) (_s : IO.FS.Stream) (n : Nat) : IO Unit := do
  let h1 ← hnd p (toString n)
  h1.flush
  IO.println s!"  useStream: {← IO.FS.readFile p}"

/-- E: a `ReaderT` context holding a stream; the action reads only the flag. -/
@[noinline] def finish (p : System.FilePath) : ReaderT Cfg IO Unit := do
  let c ← read
  let h1 ← hnd p "1"
  if c.flag then h1.putStr "y"
  IO.println s!"  finish: {← IO.FS.readFile p}"

/-- F: the helper of B as a function value (natively its `_boxed` variant
releases the borrowed argument after the call). -/
@[noinline] def runWith (f : Cfg → IO Unit) (cfg : Cfg) : IO Unit := f cfg

/-- G: a task holding a handle (`IO.hasFinished` borrows). -/
@[noinline] def mkTask (h : IO.FS.Handle) : Task IO.FS.Handle := Task.pure h

@[noinline] def useTask (p : System.FilePath) (t : Task IO.FS.Handle) : IO Unit := do
  let h1 ← hnd p "1"
  if !(← IO.hasFinished t) then h1.putStr "y"
  IO.println s!"  useTask: {← IO.FS.readFile p}"

def main : IO Unit := do
  let p ← fresh "thunk"
  useThunk p (mkThunk (← hnd p "T")) false; report "thunk"
  let p ← fresh "cfg"
  useCfg p { out := .ofHandle (← hnd p "S"), flag := false }; report "cfg"
  let p ← fresh "cb"
  useCb p (mkCb (← hnd p "C")); report "cb"
  let p ← fresh "stream"
  useStream p (.ofHandle (← hnd p "S")) 1; report "stream"
  let p ← fresh "reader"
  (finish p).run { out := .ofHandle (← hnd p "S"), flag := false }; report "reader"
  let p ← fresh "boxed"
  runWith (useCfg p) { out := .ofHandle (← hnd p "S"), flag := false }; report "boxed"
  let p ← fresh "task"
  useTask p (mkTask (← hnd p "K")); report "task"
