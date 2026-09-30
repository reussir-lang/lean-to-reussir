/-
lean2rr classic corpus: `monadic-interp` (written for this corpus).

An interpreter for a small imperative language (integers, variables,
functions, while/for loops with break/continue, return, throw/try-catch,
print), written in the monad `ReaderT Ctx (ExceptT Signal (StateT St IO))`
with do-notation throughout: early `return`, Lean-level `for`/`repeat` loops
with `break`/`continue` (also from inside `catch` handlers), `throw` and
`try ... catch` for the interpreted language's control flow and errors,
`withReader`, `modify`/`get`. A static checker runs in
`ExceptT String (StateM Nat)` over `Id`, and a small example shows the two
orders of `StateT` and `ExceptT` giving different results. The driver also
throws and catches `IO` errors and uses `try ... finally`.

Size argument n (default 30000): the loop bound of the interpreted
Collatz and prime-counting programs.
-/

/-! ## Syntax -/

inductive BinOp where
  | add | sub | mul | div | mod | lt | le | eq | ne | land | lor
deriving Repr, BEq

inductive Expr where
  | num (v : Int)
  | var (name : String)
  | neg (a : Expr)
  | bin (op : BinOp) (a b : Expr)
  | call (fn : String) (args : List Expr)

inductive Stmt where
  | assign (x : String) (e : Expr)
  | block (ss : List Stmt)
  | ite (c : Expr) (t e : Stmt)
  | while (c : Expr) (body : Stmt)
  | forRange (x : String) (lo hi : Expr) (body : Stmt)
  | brk
  | cont
  | ret (e : Expr)
  | throw (e : Expr)
  | tryCatch (body : Stmt) (x : String) (handler : Stmt)
  | print (label : String) (e : Expr)

structure Func where
  params : List String
  body : Stmt

/-! ## Semantics -/

structure Ctx where
  funcs : List (String × Func)
  depth : Nat := 0
  maxDepth : Nat := 100

structure St where
  vars : Array (String × Int) := #[]
  steps : Nat := 0
  calls : Nat := 0
  printed : Nat := 0

/-- Non-local control flow and errors of the interpreted language. -/
inductive Signal where
  | error (msg : String)
  | thrown (v : Int)
  | brk
  | cont
  | ret (v : Int)

def Signal.describe : Signal → String
  | .error msg => s!"runtime error: {msg}"
  | .thrown v => s!"uncaught throw {v}"
  | .brk => "break outside loop"
  | .cont => "continue outside loop"
  | .ret v => s!"return {v}"

abbrev M := ReaderT Ctx (ExceptT Signal (StateT St IO))

def tick : M Unit := modify fun st => { st with steps := st.steps + 1 }

def lookupVar (x : String) : M Int := do
  let st ← get
  for (k, v) in st.vars do
    if k == x then return v
  throw (.error s!"unbound variable {x}")

def setVar (x : String) (v : Int) : M Unit :=
  modify fun st => Id.run do
    let vars := st.vars
    for h : i in [0:vars.size] do
      if vars[i].1 == x then
        return { st with vars := vars.set i (x, v) }
    return { st with vars := vars.push (x, v) }

def evalBin : BinOp → Int → Int → M Int
  | .add, a, b => pure (a + b)
  | .sub, a, b => pure (a - b)
  | .mul, a, b => pure (a * b)
  | .div, a, b => if b == 0 then throw (.error "division by zero") else pure (a / b)
  | .mod, a, b => if b == 0 then throw (.error "modulo by zero") else pure (a % b)
  | .lt, a, b => pure (if a < b then 1 else 0)
  | .le, a, b => pure (if a ≤ b then 1 else 0)
  | .eq, a, b => pure (if a == b then 1 else 0)
  | .ne, a, b => pure (if a != b then 1 else 0)
  | .land, a, b => pure (if a != 0 && b != 0 then 1 else 0)
  | .lor, a, b => pure (if a != 0 || b != 0 then 1 else 0)

mutual
  partial def eval : Expr → M Int
    | .num v => pure v
    | .var x => lookupVar x
    | .neg a => return - (← eval a)
    | .bin .land a b => do
      -- short-circuit: `b` is not evaluated when `a` is false
      if (← eval a) == 0 then return 0
      return if (← eval b) == 0 then 0 else 1
    | .bin op a b => do evalBin op (← eval a) (← eval b)
    | .call f args => do
      let ctx ← read
      let some fn := ctx.funcs.lookup f
        | throw (.error s!"unknown function {f}")
      if ctx.depth ≥ ctx.maxDepth then
        throw (.error s!"call depth exceeded in {f}")
      let vals ← args.mapM eval
      if vals.length != fn.params.length then
        throw (.error s!"arity mismatch calling {f}")
      let saved := (← get).vars
      modify fun st => { st with vars := (fn.params.zip vals).toArray, calls := st.calls + 1 }
      let result ← try
          withReader (fun c => { c with depth := c.depth + 1 }) (exec fn.body)
          pure 0
        catch e =>
          match e with
          | .ret v => pure v
          | e => do
            modify fun st => { st with vars := saved }
            throw e
      modify fun st => { st with vars := saved }
      return result

  partial def exec : Stmt → M Unit
    | .assign x e => do tick; setVar x (← eval e)
    | .block ss => do
      for s in ss do
        exec s
    | .ite c t e => do
      tick
      if (← eval c) != 0 then exec t else exec e
    | .while c body => do
      repeat
        tick
        if (← eval c) == 0 then break
        try
          exec body
        catch e =>
          match e with
          | .brk => break
          | .cont => continue
          | e => throw e
    | .forRange x lo hi body => do
      let lo ← eval lo
      let hi ← eval hi
      for i in [lo.toNat : hi.toNat] do
        tick
        setVar x i
        try
          exec body
        catch e =>
          match e with
          | .brk => break
          | .cont => continue
          | e => throw e
    | .brk => throw .brk
    | .cont => throw .cont
    | .ret e => do throw (.ret (← eval e))
    | .throw e => do throw (.thrown (← eval e))
    | .tryCatch body x handler => do
      try
        exec body
      catch e =>
        match e with
        | .thrown v => setVar x v; exec handler
        | .error msg => setVar x (-(msg.length : Int)); exec handler
        | e => throw e
    | .print label e => do
      let v ← eval e
      modify fun st => { st with printed := st.printed + 1 }
      IO.println s!"  {label} = {v}"
end

/-! ## A static checker in `ExceptT String (StateM Nat)` (over `Id`) -/

/-- Counts statements; rejects `break`/`continue` outside loops and `return`
  outside functions. -/
partial def check (inLoop inFun : Bool) : Stmt → ExceptT String (StateM Nat) Unit
  | s => do
    modify (· + 1)
    match s with
    | .block ss => for s in ss do check inLoop inFun s
    | .ite _ t e => do check inLoop inFun t; check inLoop inFun e
    | .while _ b => check true inFun b
    | .forRange _ _ _ b => check true inFun b
    | .brk => unless inLoop do throw "break outside loop"
    | .cont => unless inLoop do throw "continue outside loop"
    | .ret _ => unless inFun do throw "return outside function"
    | .tryCatch b _ h => do check inLoop inFun b; check inLoop inFun h
    | _ => pure ()

def checkProgram (funcs : List (String × Func)) (main : Stmt) : Except String Nat × Nat :=
  let act : ExceptT String (StateM Nat) Nat := do
    for (_, f) in funcs do
      check false true f.body
    check false false main
    return (← get)
  act.run.run 0

/-- The same action in both transformer orders: with `StateT` outside, a
  caught exception rolls the state back; with `ExceptT` outside it does not. -/
def orderDemo : Nat × Nat :=
  let a : StateT Nat (Except String) Nat := do
    set 10
    try
      set 20
      throw "boom"
    catch _ => pure ()
    get
  let b : ExceptT String (StateM Nat) Nat := do
    set 10
    try
      set 20
      throw "boom"
    catch _ => pure ()
    get
  let ra := match a.run 0 with | .ok (v, _) => v | .error _ => 0
  let rb := match b.run.run 0 with | (.ok v, _) => v | (.error _, _) => 0
  (ra, rb)

/-! ## Programs -/

def v (x : String) : Expr := .var x
instance : OfNat Expr n := ⟨.num n⟩
instance : Add Expr := ⟨.bin .add⟩
instance : Sub Expr := ⟨.bin .sub⟩
instance : Mul Expr := ⟨.bin .mul⟩
instance : Div Expr := ⟨.bin .div⟩
instance : Mod Expr := ⟨.bin .mod⟩
instance : Neg Expr := ⟨.neg⟩
def lt (a b : Expr) : Expr := .bin .lt a b
def le (a b : Expr) : Expr := .bin .le a b
def eq (a b : Expr) : Expr := .bin .eq a b
def ne (a b : Expr) : Expr := .bin .ne a b
def and (a b : Expr) : Expr := .bin .land a b
def set (x : String) (e : Expr) : Stmt := .assign x e
def skip : Stmt := .block []

def collatz (limit : Nat) : Stmt := .block [
  set "total" 0, set "best" 0, set "bestI" 0,
  .forRange "i" 1 (.num limit + 1) (.block [
    set "x" (v "i"), set "steps" 0,
    .while (lt 1 (v "x")) (.block [
      .ite (eq (v "x" % 2) 0) (set "x" (v "x" / 2)) (set "x" (3 * v "x" + 1)),
      set "steps" (v "steps" + 1)]),
    set "total" (v "total" + v "steps"),
    .ite (lt (v "best") (v "steps")) (.block [set "best" (v "steps"), set "bestI" (v "i")]) skip]),
  .print "collatz total steps" (v "total"),
  .print "collatz longest (start*1000+steps)" (v "bestI" * 1000 + v "best")]

def primes (limit : Nat) : Stmt := .block [
  set "count" 0, set "last" 0,
  .forRange "i" 2 (.num limit) (.block [
    .ite (and (lt 2 (v "i")) (eq (v "i" % 2) 0)) .cont skip,
    set "d" 3, set "prime" 1,
    .while (le (v "d" * v "d") (v "i")) (.block [
      .ite (eq (v "i" % v "d") 0) (.block [set "prime" 0, .brk]) skip,
      set "d" (v "d" + 2)]),
    .ite (eq (v "prime") 1) (.block [set "count" (v "count" + 1), set "last" (v "i")]) skip]),
  .print "prime count" (v "count"),
  .print "last prime" (v "last")]

def funcs : List (String × Func) := [
  ("fib", { params := ["n"], body := .block [
      .ite (lt (v "n") 2) (.ret (v "n")) skip,
      .ret (.call "fib" [v "n" - 1] + .call "fib" [v "n" - 2])] }),
  ("gcd", { params := ["a", "b"], body := .block [
      .while (ne (v "b") 0) (.block [set "t" (v "a" % v "b"), set "a" (v "b"), set "b" (v "t")]),
      .ret (v "a")] }),
  ("deep", { params := ["n"], body := .block [
      .ite (eq (v "n") 0) (.ret 0) skip,
      .ret (1 + .call "deep" [v "n" - 1])] }),
  ("find", { params := ["target"], body := .block [
      -- early return from inside a loop
      .forRange "k" 0 1000 (.ite (eq (v "k" * v "k") (v "target")) (.ret (v "k")) skip),
      .ret (-1)] })]

def calls : Stmt := .block [
  .print "fib(18)" (.call "fib" [18]),
  set "g" 0,
  .forRange "i" 1 200 (set "g" (v "g" + .call "gcd" [v "i" * 7919, 360360])),
  .print "sum of gcds" (v "g"),
  .print "find(1369)" (.call "find" [1369]),
  .print "find(1370)" (.call "find" [1370]),
  .print "deep(50)" (.call "deep" [50])]

def exceptions : Stmt := .block [
  set "acc" 0,
  .forRange "i" 0 20 (.tryCatch (.block [
      .ite (eq (v "i" % 7) 3) (.throw (v "i" * 100)) skip,
      set "acc" (v "acc" + 1000 / (v "i" - 12))]) "e"
    (set "acc" (v "acc" + v "e"))),
  .print "exception accumulator" (v "acc"),
  .tryCatch (set "r" (.call "deep" [500])) "e" (set "r" (v "e")),
  .print "deep(500) caught" (v "r"),
  .tryCatch (.tryCatch (.throw 7) "e" (.throw (v "e" * 6))) "e2" (set "r" (v "e2")),
  .print "rethrown" (v "r"),
  .tryCatch (set "r" (.call "nosuch" [])) "e" (set "r" (v "e")),
  .print "unknown function caught" (v "r")]

def failing : Stmt := .block [
  set "x" 5,
  .print "before" (v "x"),
  set "y" (v "x" / (v "x" - 5)),
  .print "unreachable" (v "y")]

def uncaughtThrow : Stmt := .block [.forRange "i" 0 10 (.ite (eq (v "i") 4) (.throw (v "i" + 1000)) skip)]

def badBreak : Stmt := .block [set "x" 1, .brk]

/-! ## Driver -/

def runProgram (name : String) (prog : Stmt) : IO Unit := do
  IO.println s!"{name}:"
  let (r, st) ← ((exec prog).run { funcs }).run.run {}
  let outcome := match r with
    | .ok () => "ok"
    | .error (.ret v) => s!"returned {v}"
    | .error sig => sig.describe
  IO.println s!"  => {outcome}; steps={st.steps} calls={st.calls} printed={st.printed} vars={st.vars.size}"

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 30000
  let programs : List (String × Stmt) :=
    [("collatz", collatz n), ("primes", primes n), ("calls", calls),
     ("exceptions", exceptions), ("failing", failing), ("uncaught", uncaughtThrow), ("bad-break", badBreak)]

  -- Static checks (pure, over Id).
  for (name, prog) in programs do
    match checkProgram funcs prog with
    | (.ok count, _) => IO.println s!"check {name}: ok ({count} statements)"
    | (.error msg, count) => IO.println s!"check {name}: rejected after {count} statements: {msg}"
  IO.println s!"transformer order demo: {orderDemo}"

  -- Run everything, even programs the checker rejects.
  for (name, prog) in programs do
    runProgram name prog

  -- IO exceptions: throw, catch, finally, early return from the loop.
  let mut log : Array String := #[]
  for i in [0:9] do
    try
      if i % 3 == 2 then throw (IO.userError s!"io error {i}")
      log := log.push s!"ok {i}"
    catch e =>
      log := log.push s!"caught '{e}'"
      if i == 5 then break
  IO.println s!"io: {log.toList}"
  let r ← try
      tryFinally (do
          IO.println "in body"
          throw (IO.userError "from body") : IO Nat)
        (IO.println "finally ran")
    catch e => do
      IO.println s!"caught after finally: {e}"
      pure 42
  if r == 42 then
    return 0
  IO.println "not reached"
  return 1
