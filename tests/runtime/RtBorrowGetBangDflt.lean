/-! Runtime test: `a[i]!` out of bounds returns the `Inhabited` instance's
value, so the read's result (`Array.get!Internal α inst a i`) derives from
both the instance and the array: natively it is borrowed only when both
are (Lean's `explicitRc` takes all its parents; its inference owns it when
either is owned). Here the array is a borrowed parameter but the instance
(`⟨some h⟩`) is built by the function and dies at the read: natively the
result is owned and released after `helper` returns, so the handle stays
open while `helper` reads the file (nothing read). After hunt3 own's fix of
`get!Internal`'s array position, lean2rr counted the result borrowed when
the array alone was: `pickDflt read [hello]` (review of hunt3 own). -/

@[noinline] def helper (h : Option IO.FS.Handle) (path : System.FilePath) : IO String := do
  match h with
  | some x => x.putStr "hello"
  | none => pure ()
  IO.FS.readFile path

@[noinline] def pickDflt (arr : Array (Option IO.FS.Handle)) (h : IO.FS.Handle)
    (path : System.FilePath) (i : Nat) : IO String :=
  helper (@getElem! _ _ _ _ _ ⟨some h⟩ arr i) path

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := "rtborrowgetbangdflt-tmp"
  IO.FS.createDirAll dir
  let a := dir / "a.txt"
  let h ← IO.FS.Handle.mk a .write
  let arr : Array (Option IO.FS.Handle) := if args.length > 7 then #[none] else #[]
  IO.println s!"pickDflt read [{← pickDflt arr h a (args.length + 3)}] after [{← IO.FS.readFile a}]"
  IO.FS.removeDirAll dir
