/-! Runtime test (port to upstream Reussir's drop scopes, 2026-11-18): the
order of the closes where native Lean releases a value whose constructor
it knows. Lean's `ExplicitRC` then emits `lean_dec_ref_known(x, n)`: when
the cell is not shared, the `n` fields are released in field order, each
completely (a `lean_dec` of its own), then the cell; when it is shared,
the cell's count goes down by one. Elsewhere it emits `lean_dec`, which
frees the whole value as one free, last pushed first. Lean knows the
constructor of a value bound by a constructor application in the same
function (one that reset/reuse did not turn into a reuse), and of a
matched value inside a constructor's alternative.

Each handle's buffered tag reaches the shared file when the handle is
closed, so the file shows the order.

- `tree`: `node (node leaf a leaf) r (node leaf b leaf)` built in `main`,
  passed to a function that borrows it, released after the call: `ARB`
  (one free from the root would give `BRA`).
- `list`: `[1, 2, 3, 4]` built in `main`, released after `length`: the
  head, then the tail as one free: `1432`.
- `struct`: `{i := {x, y}, h}`: the field `i` is released completely
  first, as one free (`yx`), then `h`: `yxh` (one free: `hyx`).
- `shared`: the tree is also in a reference. The release after the call
  only decrements the cell: nothing is closed (`shared1` prints nothing),
  and the reference's `set` frees the tree as one free: `BRA`.
- `unknown`: the same tree made by a function that is not inlined:
  `lean_dec`, one free: `BRA`.
- `scrut`: a matched value whose alternative reads its first field, with
  another handle `h` that dies at the alternative's start: `h` first, then
  the matched value's other fields in field order: `hbca`.
- `built`: a value bound by a constructor and a handle die at the start of
  a branch: the value first (bound later), its fields in field order:
  `abh`.
- `reuse`: a matched value's cell is reused for a new value, which is
  released after a call that borrows it. Natively it is a `reuse`, not a
  constructor: `lean_dec`.
- `alone-tree`, `alone-struct`, `alone-list`: a value bound by a
  constructor that dies alone at the start of a branch (review RV7, A-1):
  `ARB`, `yxh`, `1432`, as after a call. Reussir's own drop gave one free
  for the tree (`BRA`) and went through the structure and the list in
  place (`xyh`, `1234`).
- `alone-unknown`: a structure from another function that dies alone at
  the start of a branch: `lean_dec`, one free, last pushed first: `hyx`
  (in place: `xyh`). -/
inductive Tr where
  | leaf : Tr
  | node : Tr → IO.FS.Handle → Tr → Tr

def Tr.size : Tr → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

structure Two where
  x : IO.FS.Handle
  y : IO.FS.Handle

structure P where
  i : Two
  h : IO.FS.Handle

inductive W where
  | two (a b : IO.FS.Handle)
  | three (a b c : IO.FS.Handle)
  | none

def path : System.FilePath := "dkc-tmp.txt"

@[noinline] def openW (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk path .append
  h.putStr tag
  pure h

def report (tag : String) : IO Unit := do
  IO.println s!"{tag} {← IO.FS.readFile path}"
  IO.FS.writeFile path ""

@[noinline] def dropTree (t : Tr) : Nat := t.size
@[noinline] def peekP (p : P) : IO Unit := p.h.putStr ""

@[noinline] def mkTree : IO Tr := do
  let a ← openW "A"
  let r ← openW "R"
  let b ← openW "B"
  pure (.node (.node .leaf a .leaf) r (.node .leaf b .leaf))

@[noinline] def mkW (c : Bool) : IO W := do
  if c then return .three (← openW "a") (← openW "b") (← openW "c") else return .none

@[noinline] def peek (w : W) : IO Unit := do
  match w with
  | .none => IO.println "none"
  | _ => IO.println "some"

@[noinline] def use2 (w : W) (h : IO.FS.Handle) : IO Unit := do
  match w with
  | .two a _ => a.putStr ""; h.putStr ""
  | .three a _ _ => a.putStr ""; h.putStr ""
  | .none => h.putStr ""

@[noinline] def flag (n : Nat) : IO Bool := pure (n > 0)
@[noinline] def consume (t : Tr) (r : IO.Ref Tr) : IO Unit := r.set t
@[noinline] def consumeP (t : P) (r : IO.Ref (Option P)) : IO Unit := r.set (some t)
@[noinline] def consumeL (t : List IO.FS.Handle) (r : IO.Ref (List IO.FS.Handle)) : IO Unit := r.set t

@[noinline] def mkP : IO P := do
  let x ← openW "x"
  let y ← openW "y"
  let h ← openW "h"
  pure { i := { x, y }, h }

@[noinline] def swap (w : W) : IO Unit := do
  match w with
  | .two a b =>
    let v := W.two b a
    peek v
  | _ => pure ()

def main : IO Unit := do
  IO.FS.writeFile path ""
  -- tree
  let a ← openW "A"
  let r ← openW "R"
  let b ← openW "B"
  IO.println s!"size {dropTree (.node (.node .leaf a .leaf) r (.node .leaf b .leaf))}"
  report "tree"
  -- list
  let hs : List IO.FS.Handle := [← openW "1", ← openW "2", ← openW "3", ← openW "4"]
  IO.println s!"length {hs.length}"
  report "list"
  -- struct
  let x ← openW "x"
  let y ← openW "y"
  let h ← openW "h"
  let p : P := { i := { x, y }, h }
  peekP p
  report "struct"
  -- shared
  let a ← openW "A"
  let r ← openW "R"
  let b ← openW "B"
  let t : Tr := .node (.node .leaf a .leaf) r (.node .leaf b .leaf)
  let ref ← IO.mkRef t
  IO.println s!"size {dropTree t}"
  report "shared1"
  ref.set .leaf
  report "shared2"
  -- unknown
  IO.println s!"size {dropTree (← mkTree)}"
  report "unknown"
  -- scrut
  let h ← openW "h"
  let w ← mkW true
  match w with
  | .two _ _ => IO.println "two"
  | .three a _ _ => a.putStr ""
  | .none => h.putStr "x"
  report "scrut"
  -- built
  let h ← openW "h"
  let a ← openW "a"
  let b ← openW "b"
  let q : W := .two a b
  peek q
  if ← flag 1 then IO.println "skip" else use2 q h
  report "built"
  -- reuse
  let a ← openW "a"
  let b ← openW "b"
  swap (.two a b)
  report "reuse"
  -- one value alone at the start of a branch
  let tr ← IO.mkRef Tr.leaf
  let pr ← IO.mkRef (none : Option P)
  let lr ← IO.mkRef ([] : List IO.FS.Handle)
  let a ← openW "A"
  let r ← openW "R"
  let b ← openW "B"
  let t : Tr := .node (.node .leaf a .leaf) r (.node .leaf b .leaf)
  IO.println s!"size {dropTree t}"
  if ← flag 1 then IO.println "skip" else consume t tr
  report "alone-tree"
  let x ← openW "x"
  let y ← openW "y"
  let h ← openW "h"
  let p : P := { i := { x, y }, h }
  peekP p
  if ← flag 1 then IO.println "skip" else consumeP p pr
  report "alone-struct"
  let hs : List IO.FS.Handle := [← openW "1", ← openW "2", ← openW "3", ← openW "4"]
  IO.println s!"length {hs.length}"
  if ← flag 1 then IO.println "skip" else consumeL hs lr
  report "alone-list"
  let p ← mkP
  if ← flag 1 then IO.println "skip" else consumeP p pr
  report "alone-unknown"
  tr.set .leaf
  pr.set none
  lr.set []
  IO.FS.removeFile path
