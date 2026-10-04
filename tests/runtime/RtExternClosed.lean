/-!
`@[extern]` definitions of the program reached only from startup work: a
constant (natively evaluated at startup, its value a closed term), an
`initialize` declaration's action, and a constant that is a function value.
lean2rr compiles their Lean definitions (natively the C code in
`RtExternClosed.ffi.c` runs).
-/

@[extern "rt_closed_table"]
def mkTable (n : Nat) : Array Nat := (List.range n).toArray.map (· * 7 % 11)

def table : Array Nat := mkTable 12

@[extern "rt_closed_seed"]
def seed (n : UInt64) : UInt64 := n * 6364136223846793005 + 1442695040888963407

initialize counter : IO.Ref UInt64 ← IO.mkRef (seed 3)

@[extern "rt_closed_greet"]
def greeting (u : Unit) : String := "hi"

def greetConst : String := greeting () ++ "!"

@[extern "rt_closed_scale"]
def scale (k n : Nat) : Nat := k * n

def scaleBy3 : Nat → Nat := scale 3

def main : IO Unit := do
  IO.println table
  IO.println (← counter.get)
  counter.modify seed
  IO.println (← counter.get)
  IO.println greetConst
  IO.println ([1, 2].map scaleBy3)
