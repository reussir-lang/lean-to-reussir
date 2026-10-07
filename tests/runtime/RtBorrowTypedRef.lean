/-! Runtime test: the release time of borrowed resources (plan §5.8) in a
program that also has references of precise types (cross-test XT-2,
fixture A621). lean2rr gave a reference created at a precise type its own
mono type `_l2r.TypedRef α`, which is not a Lean constant; Lean's borrow
inference, which lean2rr runs on its mono declarations, failed on it
(`toImpureType`: unknown constant), and the failure was swallowed: the
whole program then released every borrowed handle inside the callee.
Since rule 1 a reference has one type whatever its contents (no
`TypedRef`); the test keeps checking the release times of borrowed handles
in a program with references at precise types.
- `writeThenRead h`: a helper writes to a handle it borrows, then reads the
  file: natively the handle is still open, its byte still buffered (`""`);
- `keepB hb hb`: a structure holding a handle, lent (`@&`) and stored in a
  reference (`IO.Ref HB`, a typed reference) by the same call;
- `m3 g4 g3 g3`: a handle passed to a borrowed and an owned parameter;
- an `IO.Ref Nat` counter and an `IO.Ref HB`, both typed references.
The texts come from the command line. -/

structure HB where
  h : IO.FS.Handle
  n : Nat

@[noinline] def mkR (b : HB) : IO (IO.Ref HB) := IO.mkRef b

@[noinline] def writeThenRead (h : IO.FS.Handle) (s : String) (path : String) : IO String := do
  h.putStr s
  IO.FS.readFile path

@[noinline] def keep (a : IO.FS.Handle) : IO (IO.Ref IO.FS.Handle) := IO.mkRef a

@[noinline] def m3 (a b c : IO.FS.Handle) (s : Array String) : IO Unit := do
  a.putStr s[0]!; b.putStr s[1]!
  let r ← keep c
  (← r.get).putStr s[2]!

@[noinline] def keepB (a : @& HB) (b : HB) (s : String) : IO (IO.Ref HB) := do
  a.h.putStr s
  IO.mkRef b

def fresh (name : String) : IO IO.FS.Handle := do
  IO.FS.writeFile name ""
  IO.FS.Handle.mk name .append

def main (args : List String) : IO Unit := do
  let s := args.toArray
  let count ← IO.mkRef (0 : Nat)
  let h ← IO.FS.Handle.mk "f.txt" .write
  IO.println s!"inside: {repr (← writeThenRead h s[0]! "f.txt")}"
  IO.println s!"after: {repr (← IO.FS.readFile "f.txt")}"
  count.modify (· + 1)
  let g3 ← fresh "p2.txt"
  let g4 ← IO.FS.Handle.mk "p2.txt" .append
  m3 g4 g3 g3 s
  IO.println (← IO.FS.readFile "p2.txt")
  count.modify (· + 1)
  let h1 ← fresh "q1.txt"
  let hb : HB := ⟨h1, 1⟩
  let r ← keepB hb hb s[0]!
  (← r.get).h.putStr s[2]!
  IO.println (← IO.FS.readFile "q1.txt")
  let g ← IO.FS.Handle.mk "g.txt" .write
  let r2 ← mkR ⟨g, 1⟩
  (← r2.get).h.putStr s[1]!
  IO.println s!"g: {repr (← IO.FS.readFile "g.txt")} count {← count.get}"
