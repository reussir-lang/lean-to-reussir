/-!
Callbacks that only `initialize` blocks store, in a program that casts (a
user `implemented_by` with an `unsafe` implementation) and makes a resource
(a promise), as the `Lean` package's environment extensions do.

`register` takes a descriptor, a structure of a name and a callback, reads
both at its start (one `match`) and applies the callback at its own type
(`Array Nat → Array Nat`). In the descriptor the callback is at the
uniform type `Box → Box` (one layout per datatype). flatten-structs splits
`register`'s parameter: Lean owns it natively and the structure dies where
its fields are read (Opt/Flatten, `castParamFree`), so the caller passes the
callback at its own type. Left whole, `register` converted the callback back
from `Box → Box`, and `conv-liveness` reached the uniform type's application
function, with an arm for every callback of that type the `initialize`
blocks store (`storedNat`, `storedStr`, `storedList`, never applied): their
code, and in the `Lean` package all the code such callbacks reach, was
generated (a program importing `Cslib.Init` with a one-line `main`: 18,138
live functions with the split, 198,768 without). The output is checked by
run.sh, the generated functions by flatten-cast-check.sh.

Split structures that hold a handle through a closure, a thunk or a task
(every handle appends its tag, so a file shows the order of the closes):
- `g1t` passes a structure's `Thunk IO.FS.Handle` field to a helper that
  reads it only with `Thunk.get` (Lean borrows it) and then reads the
  file; `g1o` an optional callback that the helper only asks `isNone`.
  Natively the structure is owned (its `name` goes to an owned parameter),
  so the projected field is an increment, released after the helper
  returns: the helper reads `1`. In the worker the inference took the field
  as borrowed (lent), so it was released inside the helper (`T1`, `O1`):
  inside a rewritten declaration the parameters count as owned
  (Lower/Borrow, `borrowInfo`). From the review of xlate-regress.
- `g2` reads its callback at its start and calls it after a file read.
- `g3` reads both fields and a `cases` follows at once (Lean's `pushProj`
  moves the projections into the branches); one branch calls the
  callback, the other does not.
-/

structure Descr (σ : Type) where
  name : String
  fin : σ → σ

@[noinline] def storedNat (n : Nat) : Nat := (List.range n).foldl (· + ·) 0 + 7
@[noinline] def storedStr (s : String) : String := s ++ s.toUpper ++ "x"
@[noinline] def storedList (l : List Nat) : List Nat := l.reverse ++ l.map (· * 3)

initialize nats : IO.Ref (List (Descr Nat)) ← IO.mkRef [{ name := "n", fin := storedNat }]
initialize strs : IO.Ref (List (Descr String)) ← IO.mkRef [{ name := "s", fin := storedStr }]
initialize lists : IO.Ref (List (Descr (List Nat))) ← IO.mkRef [{ name := "l", fin := storedList }]

@[noinline] def register (d : Descr (Array Nat)) : IO Unit := do
  let { name, fin } := d
  let a := fin #[1, 2, 3]
  IO.println s!"{name} {a.size} {a}"

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"rtfcc-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) : IO Unit := do
  IO.println s!"{name}: {← IO.FS.readFile s!"rtfcc-{name}.txt"}"
  IO.FS.removeFile s!"rtfcc-{name}.txt"

structure S where
  cb : Unit → IO Unit
  name : String

@[noinline] def mkCb (h : IO.FS.Handle) : Unit → IO Unit := fun _ => h.putStr "!"

structure SThk where
  t : Thunk IO.FS.Handle
  name : String

@[noinline] def mkThunk (h : IO.FS.Handle) : Thunk IO.FS.Handle := Thunk.pure h

@[noinline] def useT (p : System.FilePath) (t : Thunk IO.FS.Handle) (name : String) : IO Unit := do
  let h1 ← hnd p "1"
  let n := name ++ "!"
  if (← t.get.isTty) || n.length == 100 then h1.putStr "y"
  IO.println s!"  useT {n}: {← IO.FS.readFile p}"

@[noinline] def g1t (p : System.FilePath) (s : SThk) : IO Unit :=
  useT p s.t s.name

structure SO where
  cb : Option (Unit → IO Unit)
  name : String

@[noinline] def useO (p : System.FilePath) (cb : Option (Unit → IO Unit)) (name : String) : IO Unit := do
  let h1 ← hnd p "1"
  let n := name ++ "!"
  if cb.isNone || n.length == 100 then h1.putStr "y"
  IO.println s!"  useO {n}: {← IO.FS.readFile p}"

@[noinline] def g1o (p : System.FilePath) (s : SO) : IO Unit :=
  useO p s.cb s.name

@[noinline] def g2 (p : System.FilePath) (s : S) : IO Unit := do
  let cb := s.cb
  let n := s.name ++ "?"
  IO.println s!"  g2 {n}: {← IO.FS.readFile p}"
  cb ()
  IO.println s!"  g2 after: {← IO.FS.readFile p}"

@[noinline] def use3 (p : System.FilePath) (cb : Unit → IO Unit) (name : String) : IO Unit := do
  cb ()
  IO.println s!"  use3 {name ++ "!"}: {← IO.FS.readFile p}"

@[noinline] def use4 (p : System.FilePath) (name : String) : IO Unit := do
  let h1 ← hnd p "1"
  let n := name ++ "!"
  if n.length == 100 then h1.putStr "y"
  IO.println s!"  use4 {n}: {← IO.FS.readFile p}"

@[noinline] def g3 (p : System.FilePath) (b : Bool) (s : S) : IO Unit :=
  let cb := s.cb
  let name := s.name
  if b then use3 p cb name else use4 p name

unsafe def bumpImpl (n : Nat) : Nat := n + 1
@[implemented_by bumpImpl] def bump (n : Nat) : Nat := n + 1

def main : IO Unit := do
  let ns ← nats.get
  let n := ns.length
  register { name := "reg", fin := fun a => a.push (bump n) }
  register { name := "two", fin := fun a => (a.push n).push (bump (bump n)) }
  IO.println s!"{ns.map (·.name)} {(← strs.get).map (·.name)} {(← lists.get).map (·.name)}"
  let p : IO.Promise Nat ← IO.Promise.new
  p.resolve 42
  IO.println s!"{p.result!.get}"
  let p ← fresh "e1t"
  g1t p { t := mkThunk (← hnd p "T"), name := "n" }; report "e1t"
  let p ← fresh "e1o"
  g1o p { cb := some (mkCb (← hnd p "O")), name := "n" }; report "e1o"
  let p ← fresh "e2"
  g2 p { cb := mkCb (← hnd p "C"), name := "n" }; report "e2"
  let p ← fresh "e3t"
  g3 p true { cb := mkCb (← hnd p "C"), name := "n" }; report "e3t"
  let p ← fresh "e3f"
  g3 p false { cb := mkCb (← hnd p "C"), name := "n" }; report "e3f"
