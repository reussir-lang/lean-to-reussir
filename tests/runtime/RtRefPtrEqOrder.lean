/-! Runtime test: `ST.Ref.ptrEq r1 r2` as the last use of both references
(second hunt of the release order). Natively the call borrows both and the
caller releases them after it, the last argument first (`explicitRc`'s
`addDecAfterFullApp`), so `r2` and what it holds go before `r1`: two
handles write `21` (lean2rr wrote `12`), two unresolved promises run their
`sync` dependents `p2` then `p1`. `oneDies`: only `r2` dies at the
comparison, `r1` after its next use (`2`, then `x1`); `self`: a reference
compared with itself. -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

@[noinline] def handles (path : System.FilePath) : IO Unit := do
  let r1 ← IO.mkRef (← hnd path "1")
  let r2 ← IO.mkRef (← hnd path "2")
  let same ← (ST.Ref.ptrEq r1 r2 : IO Bool)
  IO.println s!"handles: ptrEq {same}, file {← IO.FS.readFile path}"

@[noinline] def promises : IO Unit := do
  let p1 ← IO.Promise.new (α := Nat)
  let p2 ← IO.Promise.new (α := Nat)
  let _ ← IO.mapTask (sync := true) (fun r => IO.println s!"  p1 dependent {r}") p1.result?
  let _ ← IO.mapTask (sync := true) (fun r => IO.println s!"  p2 dependent {r}") p2.result?
  let r1 ← IO.mkRef p1
  let r2 ← IO.mkRef p2
  let same ← (ST.Ref.ptrEq r1 r2 : IO Bool)
  IO.println s!"promises: ptrEq {same}"

@[noinline] def oneDies (path : System.FilePath) : IO Unit := do
  let r1 ← IO.mkRef (← hnd path "1")
  let r2 ← IO.mkRef (← hnd path "2")
  let same ← (ST.Ref.ptrEq r1 r2 : IO Bool)
  IO.println s!"oneDies: ptrEq {same}, file {← IO.FS.readFile path}"
  (← r1.get).putStr "x"

@[noinline] def self (path : System.FilePath) : IO Unit := do
  let r ← IO.mkRef (← hnd path "s")
  let same ← (ST.Ref.ptrEq r r : IO Bool)
  IO.println s!"self: ptrEq {same}, file {← IO.FS.readFile path}"

def main : IO Unit := do
  for (n, act) in [("handles", handles), ("oneDies", oneDies), ("self", self)] do
    let p : System.FilePath := s!"refptreq-{n}.txt"
    IO.FS.writeFile p ""
    act p
    IO.println s!"  {n} end: {← IO.FS.readFile p}"
    IO.FS.removeFile p
  promises
