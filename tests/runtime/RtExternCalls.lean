/-!
The Lean definition of an `@[extern]` of the program calls other externs,
which follow the same rules (translation plan §5.8): another extern of the
program (its Lean definition runs too, also as a function value and a
partial application), an extern whose C symbol is the runtime's
`lean_nat_add` (its definition runs: an extern of the program is never
bound to Lean's runtime), one whose symbol binds to an
`@[export]` definition, and a function with `@[implemented_by]` whose
target is an extern. Natively the C code in `RtExternCalls.ffi.c` runs.
-/

@[extern "rt_calls_inc"]
def inc (n : Nat) : Nat := n + 1

@[extern "rt_calls_inc_twice"]
def incTwice (n : Nat) : Nat := inc (inc n)

@[extern "rt_calls_apply_all"]
def applyAll (fs : List (Nat → Nat)) (n : Nat) : Nat := fs.foldl (fun acc f => f acc) n

@[extern "lean_nat_add"]
def natAdd (a b : Nat) : Nat := a + b

@[extern "rt_calls_sum"]
def sumList (xs : @& List Nat) : Nat := xs.foldl natAdd 0

@[export rt_calls_triple]
def tripleImpl (n : Nat) : Nat := 3 * n

@[extern "rt_calls_triple"]
opaque triple : Nat → Nat

@[extern "rt_calls_tri_sum"]
def triSum (xs : List Nat) : Nat := sumList (xs.map triple)

@[extern "rt_calls_target"]
def target (n : Nat) : Nat := n * 5

@[implemented_by target]
def spec (n : Nat) : Nat := n + n + n + n + n

@[extern "rt_calls_via_spec"]
def viaSpec (n : Nat) : Nat := spec n + inc n

def main : IO Unit := do
  IO.println (incTwice 5)
  IO.println (applyAll [inc, incTwice, natAdd 10, triple] 1)
  IO.println (sumList [1, 2, 3, 2 ^ 64])
  IO.println (triSum [1, 2, 3])
  IO.println (viaSpec 4)
