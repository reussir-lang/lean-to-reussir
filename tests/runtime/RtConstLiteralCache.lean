/-! Runtime test (size survey 2026-10-10, optimization `literal-consts`): a
constant whose code is one string literal (the closed terms Lean extracts
for the literals of `word`, `taskWord` and `initWord`, and the program
constant `banner`) has no once-cell accessor; a read calls the runtime's
literal cache, which makes the string at the first read and keeps it. As
natively, where such a constant is made once and shared:
- a read in a loop (`lengths`) allocates nothing (RtConstLiteralCache.alloc
  compares the allocations at two loop lengths with native's);
- a literal read first in a task (`taskWord`), in an `initialize` action
  (`initWord`) and in the evaluation of a constant before `main`
  (`startupLen`) gives its text;
- a read value is never unique: `String.push` on it copies it, so the next
  read gives the literal again;
- two reads of one literal are one object (`sameObj`, `ptrEq`).
The argument is the loop's length (default 1000). -/

@[noinline] def word (i : Nat) : String :=
  if i % 3 == 0 then "fizz" else if i % 3 == 1 then "buzz" else "fizzbuzz"

-- The total length of `n` words: one literal read per iteration.
def lengths (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + (word i).length
  return s

@[noinline] def taskWord (i : Nat) : String :=
  if i % 2 == 0 then "task-even" else "task-odd"

@[noinline] def initWord (i : Nat) : String :=
  if i % 2 == 0 then "init-even" else "init-odd"

initialize initGreeting : String ← do
  let w := initWord 0
  IO.println s!"initialize: {w}"
  pure (w.push '!')

def startupLen : Nat := (word 2).length + (word 5).length

def banner : String := "banner"

unsafe def sameObjImpl (a b : String) : Bool := ptrEq a b

@[implemented_by sameObjImpl] def sameObj (a b : String) : Bool := a == b

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000
  IO.println (lengths n)
  let t := Task.spawn fun _ => (List.range 10).foldl (fun k i => k + (taskWord i).length) 0
  IO.println s!"task: {t.get} {taskWord 1}"
  IO.println s!"init: {initGreeting} {initWord 0} {initWord 1} {startupLen}"
  let w := word 0
  let w2 := w.push '!'
  IO.println s!"{w2} {w} {word 0} {word 3} {sameObj (word 0) (word 3)}"
  IO.println s!"{banner.push '?'} {banner} {sameObj banner banner}"
