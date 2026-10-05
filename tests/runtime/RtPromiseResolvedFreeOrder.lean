/-! Runtime test (review RS6-01): a resolved promise released inside a free
releases its value in the free's order. Each part frees one container that
holds a handle and a promise resolved with another handle (the promise's
task holds the only reference to it). Both handles append to one temporary
file with buffered output, so the file shows the order of their closes.
Natively the free reaches the promise in its turn, frees its task and
closes the handle it holds there (a constructor's last field first; an
array from its last element). Only an unresolved promise's resolution
waits for the end of the free (`leanrt::task::defer_promise_drop`); a
resolved one has nothing to resolve. -/

structure S where
  h : IO.FS.Handle
  p : IO.Promise (Option IO.FS.Handle)

def setup (path : System.FilePath) (r : IO.Ref (Option S)) : IO Unit := do
  let h1 ← IO.FS.Handle.mk path .append
  let h2 ← IO.FS.Handle.mk path .append
  h1.putStr "one\n"
  h2.putStr "two\n"
  let p ← IO.Promise.new
  p.resolve (some h2)
  r.set (some { h := h1, p := p })

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  -- a structure { h := h1, p } with p holding h2: p's task first natively
  let r ← IO.mkRef (none : Option S)
  setup path r
  r.set none
  IO.print (← IO.FS.readFile path)
  -- an array #[pB, hA], pB holding h4: freed from its last element, so hA,
  -- then pB's task (h4)
  IO.FS.writeFile path ""
  let hA ← IO.FS.Handle.mk path .append
  let h4 ← IO.FS.Handle.mk path .append
  hA.putStr "A\n"
  h4.putStr "four\n"
  let pB ← IO.Promise.new
  pB.resolve (some h4)
  let r2 ← IO.mkRef (#[] : Array (IO.FS.Handle ⊕ IO.Promise (Option IO.FS.Handle)))
  r2.set #[.inr pB, .inl hA]
  r2.set #[]
  IO.print (← IO.FS.readFile path)
  -- an array #[hA', pC], pC holding h5: pC's task (h5) first, then hA'
  IO.FS.writeFile path ""
  let hA' ← IO.FS.Handle.mk path .append
  let h5 ← IO.FS.Handle.mk path .append
  hA'.putStr "A'\n"
  h5.putStr "five\n"
  let pC ← IO.Promise.new
  pC.resolve (some h5)
  r2.set #[.inl hA', .inr pC]
  r2.set #[]
  IO.print (← IO.FS.readFile path)
  IO.FS.removeFile path
