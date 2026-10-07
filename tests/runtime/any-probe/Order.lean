-- Native Lean's order of observable releases for a boxed value (the
-- any-probe's order scenarios o1, o4, o5 check lean2rr's LAny against
-- it): file handles opened for appending write their text when closed.
-- Lean 4.34.0 prints BA (a box of H2(A, B) dropped), 321 (a chain of
-- boxes C(1, C(2, C(3))) dropped) and BA (IO.Ref.set over a box of
-- H2(A, B)): lean_dec frees a box's payload last field first.
structure H2 where
  a : IO.FS.Handle
  b : IO.FS.Handle

inductive C where
  | nil
  | cell (h : IO.FS.Handle) (next : C)

def mkH (p : System.FilePath) (s : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr s
  return h

-- A value at an erased (boxed) type, as lean2rr's `Box`.
structure AnyBox where
  {α : Type}
  v : α

@[noinline] def dropBox (_ : AnyBox) : IO Unit := pure ()

unsafe def toNSImpl {α : Type} (x : α) : NonScalar := unsafeCast x
@[implemented_by toNSImpl] opaque toNS {α : Type} (x : α) : NonScalar

@[noinline] def mkBox (a b : IO.FS.Handle) : NonScalar := toNS (H2.mk a b)
@[noinline] def mkChain (h1 h2 h3 : IO.FS.Handle) : NonScalar := toNS (C.cell h1 (C.cell h2 (C.cell h3 .nil)))
@[noinline] unsafe def dropNS (x : NonScalar) : IO Unit := do
  if ptrAddrUnsafe x == 0 then IO.println "zero"

unsafe def main : IO Unit := do
  let p1 : System.FilePath := "any-order-native-o1.txt"
  IO.FS.writeFile p1 ""
  let a ← mkH p1 "A"
  let b ← mkH p1 "B"
  dropNS (mkBox a b)
  IO.println s!"native o1 box of H2(A, B) dropped = {← IO.FS.readFile p1}"
  let p4 : System.FilePath := "any-order-native-o4.txt"
  IO.FS.writeFile p4 ""
  let h3 ← mkH p4 "3"
  let h2 ← mkH p4 "2"
  let h1 ← mkH p4 "1"
  dropNS (mkChain h1 h2 h3)
  IO.println s!"native o4 chain C(1, C(2, C(3))) dropped = {← IO.FS.readFile p4}"
  let p5 : System.FilePath := "any-order-native-o5.txt"
  IO.FS.writeFile p5 ""
  let ref ← IO.mkRef (toNS (⟨← mkH p5 "A", ← mkH p5 "B"⟩ : H2))
  ref.set (toNS ())
  IO.println s!"native o5 IO.Ref set over a box of H2(A, B) = {← IO.FS.readFile p5}"
