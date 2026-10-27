/-! Runtime test, a documented difference (translation plan §10, "Fields
of a cast value that native code reuses"): a unique value read through
`unsafeCast` as another inductive whose constructor reads fewer fields (a
view, as in RtCastViewFewer). `S.b` holds a reference, a handle and a
number; `T.b` reads only the reference. Natively `scoreImpl` reuses the
unique `S.b` cell for its result, and Lean's reset of the cell
(`ExpandResetReuse.mkFastPath`) releases only the unread fields of `T.b`'s
one-field layout: the handle in field 1 is never released, so it stays
open, and its text reaches the file only when the C library flushes its
streams at exit (`.native.out`: the file is empty at each read). lean2rr
releases the matched value with all its fields at the view: the handle is
closed and flushed before the first read (`.l2r.out`). -/

inductive S where
  | a (n : Nat) (s : String) (arr : Array Nat)
  | b (r : IO.Ref Nat) (h : IO.FS.Handle) (k : Nat)

inductive T where
  | a (n : Nat)
  | b (r : IO.Ref Nat)

@[inline] def scoreT (t : T) : IO Nat :=
  match t with
  | .a n => pure (n + 1)
  | .b r => r.get

unsafe def scoreImpl (s : S) : IO Nat := scoreT (unsafeCast s : T)
@[implemented_by scoreImpl] opaque score (s : S) : IO Nat

@[noinline] def mkB (r : IO.Ref Nat) (h : IO.FS.Handle) (k : Nat) : S := S.b r h k

def main (args : List String) : IO Unit := do
  let r ← IO.mkRef (41 + args.length)
  let h ← IO.FS.Handle.mk "RtCastViewUnique.out1" .write
  h.putStr "unique"
  let y ← score (mkB r h 4)
  IO.println s!"unique {y} [{← IO.FS.readFile "RtCastViewUnique.out1"}]"
  for i in [0:2] do
    IO.println s!"step {i} [{← IO.FS.readFile "RtCastViewUnique.out1"}]"
