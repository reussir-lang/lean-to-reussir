/-!
`@[extern "sym"]` definitions of the program: lean2rr compiles Lean code
plus Lean's runtime library only, so each runs its Lean definition
(translation plan §5.8, "Lean-only target"; a correct library makes it
equivalent to its C code). Natively the C code in `RtExternBody.ffi.c`,
which `run.sh` links into the native build only, runs. Plain (`myDouble`,
the repro `apps/probe/ExtBody.lean`), recursive (structural, well-founded,
`partial`), polymorphic, scalar, `IO`, `@&` and function-value uses.
`myAdd`'s C symbol is the runtime's `lean_nat_add`: an extern of the
program is never bound to Lean's runtime (the owner's decision of
2026-10-04), so its definition runs too (natively the runtime's addition,
the same result).
-/

@[extern "my_custom_double"]
def myDouble (n : Nat) : Nat := n + n

@[extern "my_fib"]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

@[extern "my_log2"]
def log2 (n : Nat) : Nat := if n < 2 then 0 else log2 (n / 2) + 1
termination_by n
decreasing_by omega

@[extern "my_collatz"]
partial def collatz (n steps : Nat) : Nat :=
  if n ≤ 1 then steps else collatz (if n % 2 == 0 then n / 2 else 3 * n + 1) (steps + 1)

@[extern "my_swap"]
def mySwap {α β : Type} (p : α × β) : β × α := (p.2, p.1)

@[extern "my_mix"]
def myMix (a b : UInt64) : UInt64 := a * 31 + b

@[extern "my_greet"]
def greet (name : @& String) : String := "hello, " ++ name

@[extern "my_count"]
def countUp (r : IO.Ref Nat) (k : Nat) : IO Nat := do
  r.modify (· + k)
  r.get

-- The symbol of `Nat.add` (Lean's runtime library): its definition runs.
@[extern "lean_nat_add"]
def myAdd (a b : @& Nat) : Nat := a + b

def main : IO Unit := do
  IO.println (myDouble 21)
  IO.println ((List.range 15).map fib)
  IO.println ((List.range 10).map (fun i => log2 (3 ^ i)))
  IO.println (collatz 27 0)
  IO.println (mySwap (1, "one"))
  IO.println (mySwap ("x", [true]))
  IO.println (myMix 7 9)
  IO.println (greet "world")
  let r ← IO.mkRef 10
  IO.println (← countUp r 5)
  IO.println (← countUp r 7)
  IO.println (myAdd 6 7)
  IO.println ([1, 2, 3].map myDouble)
