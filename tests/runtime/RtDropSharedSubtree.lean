/-! Runtime test (tests for the destructor port): the order of the closes
when one free reaches a value through two fields of one record. The
value is

    R { a := Y { x := w, h := hY }, b := w }   with   w := W { h := hW, k := 1 }

so `w` has two references, `Y.x` and `R.b`. (`W` and `Y` have two fields
each, so that neither is a value struct.) `build` opens the two handles
on one file in append mode and writes the tag `Y` with `hY` and `W` with
`hW`. The output is buffered, so a tag reaches the file only when its
handle is closed: the file shows the order of the closes. `report`
prints the file and empties it.

Natively a free decrements every field of a cell, pushes each field whose
count reaches zero, and then frees the last pushed first (`lean_del_core`
and `lean_dec_ref_cold`). For `R`: `a` (the `Y`) reaches zero and is
pushed; `b` (`w`) goes from 2 to 1. Then `Y` is freed: `x` (`w`) reaches
zero and is pushed, then `hY`. `hY` is popped and closed first, then `w`
is freed, and `hW` is closed. So each part prints `YW`.

- `ref`: `R` in an `IO.Ref (Option R)` that is set to `none`. The free
  starts in the runtime (`lean_st_ref_set`).
- `arr`: `R` in an `Array (Option R)` whose element `clear` replaces with
  `none` (`Array.set!`, not inlined). The free starts in the runtime.
- `user`: `R` made by `build` and dropped by `main` after `consume`, a
  call that is not inlined and does not look at it. The free starts in
  user code (`lean_dec`).

What the test pins: a free that goes into each field before it
decrements the next field (Reussir's drop glue) finds `w`'s count zero
only at `R.b`, after it has reached `hY`. If the runtime pushes both
closes and pops the last pushed first, `hW` is closed first (`WY`). -/

structure W where
  h : IO.FS.Handle
  k : Nat

structure Y where
  x : W
  h : IO.FS.Handle

structure R where
  a : Y
  b : W

def path : System.FilePath := "dss-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

@[noinline] def build : IO R := do
  let hW ← openW "W"
  let hY ← openW "Y"
  let w : W := { h := hW, k := 1 }
  pure { a := { x := w, h := hY }, b := w }

@[noinline] def clear (a : Array (Option R)) : Array (Option R) := a.set! 0 none

@[noinline] def consume (_ : R) : Nat := 1

def report (tag : String) : IO Unit := do
  IO.println s!"{tag} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

def main : IO Unit := do
  IO.FS.writeFile path ""
  let r ← IO.mkRef (none : Option R)
  r.set (some (← build))
  r.set none
  report "ref"
  IO.println s!"arr size {(clear #[some (← build)]).size}"
  report "arr"
  IO.println s!"user {consume (← build)}"
  report "user"
  IO.FS.removeFile path
