/-! Runtime test: the order in which values that die together at the start
of a branch (an `if`) or a match arm are released (bug hunt hunt-front b2
to b4 and its judge). Natively Lean's `ExplicitRC.addPrologForAlt`
releases them at the start of the arm, newest binding first; a `cases`
gives its scrutinee a new index, the newest, in a constructor's arm
(`withCtorAlt`), not in the default arm: a scrutinee whose fields the arm
does not read goes first, and in a branch nested in that arm it counts as
bound at the `cases`; a scrutinee whose fields the arm reads (a scalar
field too) is released after its last projection, after the arm's other
releases; a structure's projection is no `cases`. Each handle writes its
tag into its buffer, which reaches the file when the handle is closed, so
the file shows the order: two handles `21`, three `321`, a scrutinee
holding a handle `S` in a field the arm does not read `21S` (`1S` with one
other handle), `S21` when the arm reads no field. Promises show it through
their `sync` dependents: `p2` before `p1`. Reussir released them oldest
first, and a scrutinee before the others (`12`, `123`, `S12`); lean2rr
now releases them itself in native's order (`l2r_release_after`; plan
§5.8, "Release order at the start of a branch"; ownership.md, "Values
that die at the start of an arm are released newest first"), by each Lean
variable's binding order, which the names lean2rr gives a variable later
keep (a converted field, a field `lazy-fields` binds where it is used:
`BA`, `2S`), with closures, structures holding one and tasks among the
values that may hold a resource (`1CS`, `SC1b`; the review's shapes,
where ordering by lean2rr's name numbers, or a closure the order left out,
went wrong). -/

def hnd (p : System.FilePath) (tag : String) : IO IO.FS.Handle := do
  let h ← IO.FS.Handle.mk p .append
  h.putStr tag
  return h

/-- Two and three handles that die at the start of a branch. -/
@[noinline] def branch2 (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  if b then
    IO.println s!"  branch2: {← IO.FS.readFile p}"
  else
    h1.putStr "a"; h2.putStr "b"

@[noinline] def branch3 (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  let h3 ← hnd p "3"
  if b then
    IO.println s!"  branch3: {← IO.FS.readFile p}"
  else
    h1.putStr "a"; h2.putStr "b"; h3.putStr "c"

/-- Two unresolved promises dropped at the start of a branch: each
resolves its `result?` task with `none`, which runs its `sync` printer. -/
@[noinline] def promises (b : Bool) : IO Unit := do
  let p1 ← IO.Promise.new (α := Nat)
  let p2 ← IO.Promise.new (α := Nat)
  let _ ← IO.mapTask (sync := true) (fun r => IO.println s!"  p1 {r}") p1.result?
  let _ ← IO.mapTask (sync := true) (fun r => IO.println s!"  p2 {r}") p2.result?
  if b then
    IO.println "  both dropped"
  else
    p1.resolve 1; p2.resolve 2

/-- The error arm of an IO call that throws, with two handles open. -/
@[noinline] def mayFail (b : Bool) : IO Nat := if b then throw (IO.userError "fail") else pure 1

@[noinline] def errorArm (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  let n ← mayFail b
  h1.putStr s!"{n}"; h2.putStr "x"

/-- Scrutinees that hold a handle (`S`) in a field. -/
inductive R where
  | two (h : IO.FS.Handle) (n : Nat)
  | none

inductive R2 where
  | two (h : IO.FS.Handle) (n : UInt64)
  | none

@[noinline] def mkR (p : System.FilePath) (b : Bool) : IO R :=
  if b then do pure (.two (← hnd p "S") 5) else pure .none

@[noinline] def mkR2 (p : System.FilePath) (b : Bool) : IO R2 :=
  if b then do pure (.two (← hnd p "S") 7) else pure .none

/-- The arm reads the `Nat` field, not the handle: one other handle. -/
@[noinline] def readOne (p : System.FilePath) (b : Bool) : IO Unit := do
  let r ← mkR p b
  let h1 ← hnd p "1"
  match r with
  | .two _ n => IO.println s!"  readOne {n}: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

/-- The same with two other handles, one bound before the scrutinee. -/
@[noinline] def readTwo (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let r ← mkR p b
  let h2 ← hnd p "2"
  match r with
  | .two _ n => IO.println s!"  readTwo {n}: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"; h2.putStr "m"

/-- The arm reads only a scalar (`UInt64`) field. -/
@[noinline] def readScalar (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let r ← mkR2 p b
  let h2 ← hnd p "2"
  match r with
  | .two _ n => IO.println s!"  readScalar {n}: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"; h2.putStr "m"

/-- The arm reads no field: the scrutinee goes first. -/
@[noinline] def readNone (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let r ← mkR p b
  let h2 ← hnd p "2"
  match r with
  | .two _ _ => IO.println s!"  readNone: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"; h2.putStr "m"

/-- The arm reads a field only in one branch of a nested `if`. -/
@[noinline] def readNested (p : System.FilePath) (b c : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let r ← mkR p b
  let h2 ← hnd p "2"
  match r with
  | .two _ n =>
    if c then IO.println s!"  readNested then {n}: {← IO.FS.readFile p}"
    else IO.println s!"  readNested else: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"; h2.putStr "m"

@[noinline] def keepR (r : R) : IO Unit := match r with
  | .two h _ => h.putStr "k"
  | .none => pure ()

/-- The scrutinee lives on into a nested `if` (the `then` branch passes it
whole) and dies at the start of the `else` branch with `h1`, bound after
it: there it counts as bound at the `match`, so it goes first (`S1`). -/
@[noinline] def nestedScrut (p : System.FilePath) (b c : Bool) : IO Unit := do
  let r ← mkR p b
  let h1 ← hnd p "1"
  match r with
  | .two _ n =>
    if c then IO.println s!"{n}"; keepR r; h1.putStr "x"
    else IO.println s!"  nestedScrut else: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

/-- A structure's projection is no `cases` natively (one alternative): the
structure keeps its place in the binding order (`2S1`). -/
structure P where
  h : IO.FS.Handle
  n : Nat

@[noinline] def mkP (p : System.FilePath) : IO P := do pure ⟨← hnd p "S", 6⟩

@[noinline] def keepP (s : P) : IO Unit := s.h.putStr "k"

@[noinline] def structNested (p : System.FilePath) (c : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let s ← mkP p
  let h2 ← hnd p "2"
  let n := s.n
  if c then IO.println s!"{n}"; keepP s; h1.putStr "x"; h2.putStr "y"
  else IO.println s!"  structNested else: {← IO.FS.readFile p}"

/-- A match on an enumeration with a default arm. -/
inductive K where
  | a | b | c

@[noinline] def enumDefault (p : System.FilePath) (k : K) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  match k with
  | .a => h1.putStr "a"; h2.putStr "a"
  | _ => IO.println s!"  enumDefault: {← IO.FS.readFile p}"

/-- A default arm on a scrutinee that holds a handle: natively the
scrutinee keeps its own index there (no `withCtorAlt`). -/
inductive R3 where
  | a (h : IO.FS.Handle)
  | b (h : IO.FS.Handle)
  | c (h : IO.FS.Handle)
  | none

@[noinline] def mkR3 (p : System.FilePath) (k : Nat) : IO R3 :=
  match k with
  | 0 => do pure (.a (← hnd p "S"))
  | 1 => do pure (.b (← hnd p "S"))
  | 2 => do pure (.c (← hnd p "S"))
  | _ => pure .none

@[noinline] def scrutDefault (p : System.FilePath) (k : Nat) : IO Unit := do
  let r ← mkR3 p k
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  match r with
  | .none => h1.putStr "n"; h2.putStr "m"
  | _ => IO.println s!"  scrutDefault: {← IO.FS.readFile p}"

/-- After a join point: the branches of the first `if` meet in the code
of the second, where the handles die. -/
@[noinline] def joinShape (p : System.FilePath) (b c : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  let tag ← if b then do IO.print ""; pure "x" else pure "y"
  if c then
    IO.println s!"  joinShape {tag}: {← IO.FS.readFile p}"
  else
    h1.putStr tag; h2.putStr tag

/-- The same in a join point's body large enough to be outlined (a function
of its own, J3, which takes the handles by their names), three handles. -/
@[noinline] def joinOutlined (p : System.FilePath) (b c : Bool) (k : Nat) : IO Unit := do
  let h1 ← hnd p "1"
  let h2 ← hnd p "2"
  let h3 ← hnd p "3"
  let tag ← if b then do IO.print ""; pure "x" else pure "y"
  IO.println s!"  joinOutlined {tag} {k}"
  IO.println s!"  joinOutlined {tag} {k + 1}"
  IO.println s!"  joinOutlined {tag} {k + 2} {k * 3}"
  IO.println s!"  joinOutlined {tag} {k + 3} {k * 4} {k * k}"
  IO.println s!"  joinOutlined {tag} {k + 4} {k * 5} {k * k * k}"
  if c then
    IO.println s!"  joinOutlined: {← IO.FS.readFile p}"
  else
    h1.putStr tag; h2.putStr tag; h3.putStr tag

/-- A loop's exit: the two handles the loop carries die at the start of the
exit branch (each step writes a dot through the older one, which it then
drops, and opens a new one). -/
@[noinline] partial def loopExit (p : System.FilePath) (n : Nat) (a b : IO.FS.Handle) : IO Unit := do
  if n == 0 then
    IO.println s!"  loopExit: {← IO.FS.readFile p}"
  else
    a.putStr "."
    let c ← hnd p s!"N{n}"
    loopExit p (n - 1) b c

/-- The same loop with a join point large enough to be outlined, which
calls the loop back: the loop is one state machine (J4), whose arms take
the handles from its slots by their names. -/
@[noinline] partial def machineExit (p : System.FilePath) (n : Nat) (a b : IO.FS.Handle) : IO Unit := do
  let tag ← if n % 2 == 0 then do IO.print ""; pure "e" else pure "o"
  IO.println s!"  machineExit {tag} {n}"
  IO.println s!"  machineExit {tag} {n + 1} {n * 3}"
  IO.println s!"  machineExit {tag} {n + 2} {n * 4} {n * n}"
  IO.println s!"  machineExit {tag} {n + 3} {n * 5} {n * n * n}"
  if n == 0 then
    IO.println s!"  machineExit: {← IO.FS.readFile p}"
  else
    a.putStr "."
    let c ← hnd p s!"N{n}"
    machineExit p (n - 1) b c

/-- A field of the type parameter (a box in the record) converted to its
own type at the arm's start, after the other binders: `a` (an `R` holding
handle `A`, field 0) and `b` (handle `B`, field 1) die at the inner `else`,
`b` first (`BA`): the conversion keeps its field's place. -/
inductive E (α : Type) where
  | mk (a : α) (b : IO.FS.Handle)
  | nil

@[noinline] def useR (r : R) : IO Unit := match r with
  | .two h _ => h.putStr "x"
  | .none => pure ()

@[noinline] def mkE (p : System.FilePath) : IO (E R) := do
  pure (.mk (.two (← hnd p "A") 1) (← hnd p "B"))

@[noinline] def convField (p : System.FilePath) (c : Bool) : IO Unit := do
  let e ← mkE p
  match e with
  | .mk a b =>
    IO.println "  convField arm"
    if c then useR a; b.putStr "y"
    else IO.println s!"  convField else: {← IO.FS.readFile p}"
  | .nil => pure ()

/-- A field that `lazy-fields` binds where it is used (the arm returns `w`
whole in its `then` branch): `h` keeps its place at the arm's start, older
than `h2`, and both die at the inner `else` (`2S`). -/
inductive W where
  | mk (h : IO.FS.Handle) (n : Nat)
  | nil

@[noinline] def mkW (p : System.FilePath) : IO W := do pure (.mk (← hnd p "S") 4)

@[noinline] def lazyField (p : System.FilePath) (w : W) (c d : Bool) : IO W := do
  match w with
  | .mk h n =>
    let h2 ← hnd p "2"
    if c then
      h2.putStr "c"
      pure w
    else
      if d then
        h.putStr s!"{n}"; h2.putStr "y"; pure .nil
      else
        IO.println s!"  lazyField: {← IO.FS.readFile p}"
        pure .nil
  | .nil => pure .nil

/-- A closure (holding handle `C`) dies with the scrutinee `q` and `h1`:
arm `.a` reads `n`, so `q` goes last there (`1CS`); arm `.b` reads no
field, so `q` goes first (`SC`), and `h1` after its write (`1b`). A
closure, a structure holding one and a task may hold a resource too. -/
@[noinline] def mkWriter (h : IO.FS.Handle) : String → IO Unit := fun s => h.putStr s

inductive Q where
  | a (h : IO.FS.Handle) (n : Nat)
  | b (h : IO.FS.Handle)
  | none

@[noinline] def mkQ (p : System.FilePath) (k : Nat) : IO Q :=
  match k with
  | 0 => do pure (.a (← hnd p "S") 5)
  | 1 => do pure (.b (← hnd p "S"))
  | _ => pure .none

@[noinline] def flipClosure (p : System.FilePath) (k : Nat) : IO Unit := do
  let w := mkWriter (← hnd p "C")
  let q ← mkQ p k
  let h1 ← hnd p "1"
  match q with
  | .a _ n => IO.println s!"  flipClosure a {n}: {← IO.FS.readFile p}"
  | .b _ => h1.putStr "b"; IO.println s!"  flipClosure b: {← IO.FS.readFile p}"
  | .none => w "w"; h1.putStr "n"

structure Wr where
  f : String → IO Unit
  tag : Nat

@[noinline] def mkWr (h : IO.FS.Handle) : IO Wr := pure ⟨fun s => h.putStr s, 1⟩

@[noinline] def flipRecord (p : System.FilePath) (k : Nat) : IO Unit := do
  let w ← mkWr (← hnd p "C")
  let q ← mkQ p k
  let h1 ← hnd p "1"
  match q with
  | .a _ n => IO.println s!"  flipRecord a {n}: {← IO.FS.readFile p}"
  | .b _ => h1.putStr "b"; IO.println s!"  flipRecord b: {← IO.FS.readFile p}"
  | .none => w.f "w"; h1.putStr "n"

@[noinline] def mkTask (h : IO.FS.Handle) : Task IO.FS.Handle := Task.pure h

@[noinline] def flipTask (p : System.FilePath) (k : Nat) : IO Unit := do
  let t := mkTask (← hnd p "C")
  let q ← mkQ p k
  let h1 ← hnd p "1"
  match q with
  | .a _ n => IO.println s!"  flipTask a {n}: {← IO.FS.readFile p}"
  | .b _ => h1.putStr "b"; IO.println s!"  flipTask b: {← IO.FS.readFile p}"
  | .none => t.get.putStr "w"; h1.putStr "n"

/-- A scrutinee holding two handles in fields the arm does not read, with
two other handles: the scrutinee's own fields close in field order
(`PQ`, plan §10, "Order of releases in one free") after the others. -/
inductive S2 where
  | two (p : IO.FS.Handle) (q : IO.FS.Handle)
  | none

@[noinline] def mkS2 (p : System.FilePath) (b : Bool) : IO S2 :=
  if b then do pure (.two (← hnd p "P") (← hnd p "Q")) else pure .none

@[noinline] def twoFields (p : System.FilePath) (b : Bool) : IO Unit := do
  let h1 ← hnd p "1"
  let s ← mkS2 p b
  let h2 ← hnd p "2"
  match s with
  | .two _ _ => IO.println s!"  twoFields: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"; h2.putStr "m"

/-- Two scrutinees renumbered by nested constructors' arms (`match r, q`),
both bound before the matches, die together at a nested branch's start:
the inner one (`q`, handle `T`) is the newer, so it goes first (`TS`), also
when nothing is bound between the two matches. -/
@[noinline] def mkRt (p : System.FilePath) (tag : String) (b : Bool) : IO R :=
  if b then do pure (.two (← hnd p tag) 5) else pure .none

@[noinline] def matchPair (p : System.FilePath) (b c : Bool) : IO Unit := do
  let r ← mkRt p "S" b
  let q ← mkRt p "T" b
  match r, q with
  | .two _ n, .two _ m =>
    if c then IO.println s!"{n} {m}"; keepR r; keepR q
    else IO.println s!"  matchPair else: {← IO.FS.readFile p}"
  | _, _ => keepR r; keepR q

@[noinline] def nested2 (p : System.FilePath) (b c : Bool) : IO Unit := do
  let r ← mkRt p "S" b
  let q ← mkRt p "T" b
  match r with
  | .two _ n =>
    match q with
    | .two _ m =>
      if c then IO.println s!"{n} {m}"; keepR r; keepR q
      else IO.println s!"  nested2 else: {← IO.FS.readFile p}"
    | .none => keepR r
  | .none => keepR q

@[noinline] def nested2b (p : System.FilePath) (b c : Bool) : IO Unit := do
  let q ← mkRt p "T" b
  let r ← mkRt p "S" b
  match r with
  | .two _ n =>
    match q with
    | .two _ m =>
      if c then IO.println s!"{n} {m}"; keepR r; keepR q
      else IO.println s!"  nested2b else: {← IO.FS.readFile p}"
    | .none => keepR r
  | .none => keepR q

/-- Code cut out of a constructor's arm keeps the scrutinee's renumbering:
`r` and `h1` (bound after `r`; a call before the `match` keeps Lean's
`pushProj` from moving its binding into the arm) die at the `else` start
inside a join point declared in the arm and outlined (J3), inside a loop's
state machine running such a join point (J4), and inside a part that
`Outline` cut out of the arm's long path: `r` first (`S1`). -/
@[noinline] def jpCut (p : System.FilePath) (b c d : Bool) (k : Nat) : IO Unit := do
  let r ← mkRt p "S" b
  let h1 ← hnd p "1"
  IO.println "  jpCut"
  match r with
  | .two _ n =>
    let tag ← if d then do IO.print ""; pure "x" else pure "y"
    IO.println s!"  jpCut {tag} {k}"
    IO.println s!"  jpCut {tag} {k + 1}"
    IO.println s!"  jpCut {tag} {k + 2} {k * 3}"
    IO.println s!"  jpCut {tag} {k + 3} {k * 4} {k * k}"
    IO.println s!"  jpCut {tag} {k + 4} {k * 5} {k * k * k}"
    if c then IO.println s!"{n}"; keepR r; h1.putStr "x"
    else IO.println s!"  jpCut else: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

@[noinline] partial def machineCut (p : System.FilePath) (n : Nat) (r : R) : IO Unit := do
  let h1 ← hnd p s!"{n}"
  IO.println s!"  machineCut {n}"
  match r with
  | .two _ m =>
    let tag ← if n % 2 == 0 then do IO.print ""; pure "e" else pure "o"
    IO.println s!"  machineCut {tag} {n} {m}"
    IO.println s!"  machineCut {tag} {n + 1} {n * 3}"
    IO.println s!"  machineCut {tag} {n + 2} {n * 4} {n * n}"
    IO.println s!"  machineCut {tag} {n + 3} {n * 5} {n * n * n}"
    if n == 0 then
      IO.println s!"  machineCut end: {← IO.FS.readFile p}"
    else
      keepR r
      h1.putStr "x"
      machineCut p (n - 1) r
  | .none => h1.putStr "n"

@[noinline] def partCut (p : System.FilePath) (b c : Bool) : IO Unit := do
  let r ← mkRt p "S" b
  let h1 ← hnd p "1"
  IO.println "  partCut"
  match r with
  | .two _ n =>
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    IO.print ""
    if c then IO.println s!"{n}"; keepR r; h1.putStr "x"
    else IO.println s!"  partCut else: {← IO.FS.readFile p}"
  | .none => h1.putStr "n"

def fresh (name : String) : IO System.FilePath := do
  let p : System.FilePath := s!"droparm-{name}.txt"
  IO.FS.writeFile p ""
  return p

def report (name : String) : IO Unit := do
  IO.println s!"{name}: {← IO.FS.readFile s!"droparm-{name}.txt"}"
  IO.FS.removeFile s!"droparm-{name}.txt"

def main (args : List String) : IO Unit := do
  let b := args.isEmpty
  branch2 (← fresh "b2") b; report "b2"
  branch3 (← fresh "b3") b; report "b3"
  promises b
  let p ← fresh "err"
  try errorArm p b catch e => IO.println s!"  caught {e}: {← IO.FS.readFile p}"
  report "err"
  readOne (← fresh "r1") b; report "r1"
  readTwo (← fresh "r2") b; report "r2"
  readScalar (← fresh "rs") b; report "rs"
  readNone (← fresh "rn") b; report "rn"
  readNested (← fresh "rnt") b true; report "rnt"
  readNested (← fresh "rne") b false; report "rne"
  nestedScrut (← fresh "ns") b false; report "ns"
  structNested (← fresh "sn") false; report "sn"
  enumDefault (← fresh "ed") (if b then .b else .a); report "ed"
  scrutDefault (← fresh "sd") (if b then 1 else 3); report "sd"
  joinShape (← fresh "js") b b; report "js"
  joinShape (← fresh "jn") (!b) b; report "jn"
  joinOutlined (← fresh "jo") b b 7; report "jo"
  let p ← fresh "le"
  loopExit p 2 (← hnd p "A") (← hnd p "B"); report "le"
  let p ← fresh "me"
  machineExit p 2 (← hnd p "A") (← hnd p "B"); report "me"
  convField (← fresh "cf") (!b); report "cf"
  let p ← fresh "lf"
  let _ ← lazyField p (← mkW p) (!b) (!b); report "lf"
  flipClosure (← fresh "fc0") (if b then 0 else 2); report "fc0"
  flipClosure (← fresh "fc1") (if b then 1 else 2); report "fc1"
  flipRecord (← fresh "fr0") (if b then 0 else 2); report "fr0"
  flipRecord (← fresh "fr1") (if b then 1 else 2); report "fr1"
  flipTask (← fresh "ft0") (if b then 0 else 2); report "ft0"
  flipTask (← fresh "ft1") (if b then 1 else 2); report "ft1"
  twoFields (← fresh "tf") b; report "tf"
  matchPair (← fresh "mp") b (!b); report "mp"
  nested2 (← fresh "n2") b (!b); report "n2"
  nested2b (← fresh "n2b") b (!b); report "n2b"
  jpCut (← fresh "jc") b (!b) b 3; report "jc"
  let p ← fresh "mc"
  machineCut p 1 (← mkRt p "S" b); report "mc"
  partCut (← fresh "pc") b (!b); report "pc"
