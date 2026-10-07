/-! Runtime test: the order of releases when one free defers several boxes
and records in a row (review of the deferral of a box's word, 22bcf89:
`any::release_last` defers a box's tagged word as one pending cell, and a
record cell with a wide header can follow it on the pending stack; since
the release table it defers the payload's cell, to which a later wide
cell may link). `Pack`
has three fields of erased type (each a one-word box holding an `H`
record) and a record field `r` between them; freeing a `Pack` inside a free
defers x's box, y's box, r's cell (wide header), z's box. Natively
`lean_del` pushes x y r z and pops z r y x. Also a `Pack` dropped as the
last reference given up by an array set, and a pack whose boxes hold
records of two handles. Each handle's text reaches the shared temporary
file when it is closed. -/

structure H where
  h : IO.FS.Handle
  n : Nat

structure H2 where
  a : IO.FS.Handle
  b : IO.FS.Handle

structure Rec where
  h : IO.FS.Handle
  n : Nat

structure Pack where
  {α : Type}
  x : α
  {β : Type}
  y : β
  r : Rec
  {γ : Type}
  z : γ

def hnd (path : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr s!"{tag} "
  return h

def showFile (label : String) (path : System.FilePath) : IO Unit := do
  IO.println s!"{label}: {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

@[noinline] def consumeArr (a : Array Pack) : Nat := a.size
@[noinline] def setAt (arr : Array Pack) (i : Nat) (x : Pack) : Array Pack := arr.set! i x
@[noinline] def mkH (h : IO.FS.Handle) (n : Nat) : H := ⟨h, n⟩
@[noinline] def mkRec (h : IO.FS.Handle) (n : Nat) : Rec := ⟨h, n⟩

def main : IO Unit := do
  let (h0, path) ← IO.FS.createTempFile
  h0.flush
  -- 1. An array of two packs freed: each element's box is freed inside the
  --    free, and each pack defers x's box, y's box, r's cell, z's box.
  let ax ← hnd path "ax"; let ay ← hnd path "ay"; let ar ← hnd path "ar"; let az ← hnd path "az"
  let bx ← hnd path "bx"; let by_ ← hnd path "by"; let br ← hnd path "br"; let bz ← hnd path "bz"
  let pa : Pack := { x := mkH ax 1, y := mkH ay 2, r := mkRec ar 3, z := mkH az 4 }
  let pb : Pack := { x := mkH bx 1, y := mkH by_ 2, r := mkRec br 3, z := mkH bz 4 }
  IO.println s!"array of two packs: {consumeArr #[pa, pb]}"
  showFile "  freed" path
  -- 2. An array set gives up the last reference to a pack (outside a free).
  let cx ← hnd path "cx"; let cy ← hnd path "cy"; let cr ← hnd path "cr"; let cz ← hnd path "cz"
  let ex ← hnd path "ex"; let ey ← hnd path "ey"; let er ← hnd path "er"; let ez ← hnd path "ez"
  let pc : Pack := { x := mkH cx 1, y := mkH cy 2, r := mkRec cr 3, z := mkH cz 4 }
  let pe : Pack := { x := mkH ex 1, y := mkH ey 2, r := mkRec er 3, z := mkH ez 4 }
  let arr := setAt #[pc] 0 pe
  IO.println s!"after the set ({arr.size})"
  showFile "  set over pack c" path
  IO.println s!"rest: {consumeArr arr}"
  showFile "  rest freed" path
  -- 3. A pack whose boxes hold records of two handles, freed inside a free.
  let ia ← hnd path "ia"; let ib ← hnd path "ib"; let ja ← hnd path "ja"; let jb ← hnd path "jb"
  let orr ← hnd path "or"; let oz ← hnd path "oz"
  let outer : Pack := { x := (⟨ia, ib⟩ : H2), y := (⟨ja, jb⟩ : H2), r := mkRec orr 5, z := mkH oz 6 }
  IO.println s!"pack of pairs: {consumeArr #[outer]}"
  showFile "  freed" path
  IO.FS.removeFile path
