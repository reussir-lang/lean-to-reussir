/-! Runtime test of the optimization `unread-consts`: natively a module's
initializer evaluates every constant, read or not, in order. lean2rr leaves
out a constant that no kept code reads when its evaluation cannot show
(RtUnreadConsts.l2r-debug lists the decisions), and keeps every other one
at its place: a constant that traces or panics shows at startup, before
`main`, in native order, also when nothing reads it. -/

structure Point where
  x : Nat
  y : Nat
  deriving Repr, BEq, Hashable

def t (s : String) (n : Nat) : Nat := dbgTrace s fun _ => n

-- Unread, without effects: left out.
def pureTable : Array Nat := #[1, 2, 3, 4, 5]
def pureText : String := "a literal that nothing reads"
def pureSum : Nat := (List.range 100).foldl (· + ·) 0
def purePoint : Point := { x := 1, y := 2 }

-- Unread, with effects: kept, in order.
def traced1 : Nat := t "traced1" 1
def panics : Nat := panic! "a constant panics at startup"
def readsPastEnd : Nat := pureTable[9]!
def traced2 : Nat := t "traced2" 2

-- Read only by a kept constant: kept, before it (`pureTable` too).
def helper : Array Nat := #[40, 2]
def tracedReader : Nat := t s!"tracedReader reads {helper}" helper.size

-- Recursion of the program's own code: kept (it shows nothing, but its
-- termination is not Lean's library's).
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n
def viaProgramRec : Nat := sumTo 10
partial def countDown (n : Nat) : Nat := if n == 0 then 0 else countDown (n - 1)
def viaPartial : Nat := countDown 5

-- Read by `main`: kept.
def readList : List Nat := [5, 6, 7]

def traced3 : Nat := t "traced3" 3

def main : IO Unit := do
  IO.println s!"main: {readList}"
