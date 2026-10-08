/-! Runtime test: the release time of a handle read from an array with
`a[i]!` (`Array.get!Internal α inst a i`) and passed to a function that
borrows it (plan §5.8, "Borrowing"). lean2rr's `borrowedVars` took the
read's argument 1 for the array; for `get!Internal` that is the
`Inhabited` instance. With an instance the function only borrows (a
parameter) and an array it owns, the element counted as borrowed too: the
caller did not keep it, the array died at the read, and the handle closed
inside the callee (hunt3 own, `pick read [hello]`).
- `pick d path i`: the array is the function's own, the instance a
  parameter: natively the handle stays open during `helper`;
- `pickLent arr path i`: the array is a parameter (lent by the caller,
  which keeps it): the handle stays open too. -/

@[noinline] def helper (h : Option IO.FS.Handle) (path : System.FilePath) : IO String := do
  match h with
  | some x => x.putStr "hello"
  | none => pure ()
  IO.FS.readFile path

@[noinline] def mkArr (path : System.FilePath) : IO (Array (Option IO.FS.Handle)) := do
  let h ← IO.FS.Handle.mk path .write
  return #[some h]

@[noinline] def pick (d : Inhabited (Option IO.FS.Handle)) (path : System.FilePath) (i : Nat) :
    IO String := do
  let arr ← mkArr path
  helper (@getElem! _ _ _ _ _ d arr i) path

@[noinline] def pickLent (arr : Array (Option IO.FS.Handle)) (path : System.FilePath) (i : Nat) :
    IO String :=
  helper arr[i]! path

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := "rtborrowgetbang-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let dflt : Option IO.FS.Handle := if args.length > 5 then none else none
  IO.println s!"pick read [{← pick ⟨dflt⟩ a args.length}] after [{← IO.FS.readFile a}]"
  let b := dir / "b.txt"
  let arr ← mkArr b
  IO.println s!"pickLent read [{← pickLent arr b args.length}] after [{← IO.FS.readFile b}]"
  IO.FS.removeDirAll dir
