/-! Runtime test: values that hold handles through closures in a program
that casts (`unsafeCast`), where flatten-structs decides by type which values
may hold a resource (`mayHoldRelease`: closures, thunks and tasks count). A
record of two closures over different handles whose helper calls one
closure: natively the record is owned and dies at the projection, so the
other closure's handle closes before the helper reads its file (`B`);
split, the unused closure would be a borrowed parameter of the worker, kept
until the call returns (`` for `B`). The record of RtBorrowClosure whose
flag only is read: natively the caller holds it until the call returns. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"rtbcc-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) : IO Unit := do
  IO.println s!"{name}: {← IO.FS.readFile s!"rtbcc-{name}.txt"}"
  IO.FS.removeFile s!"rtbcc-{name}.txt"

structure Two where
  a : Unit → IO Unit
  b : Unit → IO Unit

@[noinline] def useTwo (pb : System.FilePath) (r : Two) : IO Unit := do
  r.a ()
  IO.println s!"  useTwo: {← IO.FS.readFile pb}"

structure Cfg where
  out : IO.FS.Stream
  flag : Bool

@[noinline] def useCfg (p : System.FilePath) (cfg : Cfg) : IO Unit := do
  let h1 ← hnd p "1"
  if cfg.flag then h1.putStr "y"
  IO.println s!"  useCfg: {← IO.FS.readFile p}"

@[noinline] unsafe def strsAsBytes (a : Array String) : Array UInt8 := unsafeCast a

unsafe def main : IO Unit := do
  let pa ← fresh "twoa"
  let pb ← fresh "twob"
  let ha ← hnd pa "A"
  let hb ← hnd pb "B"
  useTwo pb { a := fun _ => ha.putStr "a", b := fun _ => hb.putStr "b" }
  report "twoa"; report "twob"
  let p ← fresh "cfg"
  useCfg p { out := .ofHandle (← hnd p "S"), flag := false }; report "cfg"
  IO.println s!"cast {(strsAsBytes #["a", "bc"]).size}"
