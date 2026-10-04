/-!
Externs of the program applied to literals in a branch that does not run
(review RV8E-11): natively their calls are C calls, which Lean's compiler
does not evaluate at compile time, and the program prints its labels.
`myShl` re-declares `lean_nat_shiftl` (Lean's `Nat.shiftLeft`; an extern
of the program is never bound to Lean's runtime, so its `noinline`
definition runs); `bodyShl` is an extern
of the program whose C code is in `RtExternFold.ffi.c` (its Lean definition
runs); `exportShl` (`opaque`) is bound to `shlImpl`'s `@[export]`, called
through a `noinline` declaration, not renamed to `shlImpl` (review REB-01:
renamed, its literal call was folded and stopped lean2rr). The literal
calls would panic at run time ("Nat.shiftl exponent is too big") if the
branch ran.
-/

@[extern "lean_nat_shiftl"]
def myShl (a b : @& Nat) : Nat := a <<< b

@[extern "rt_fold_shl"]
def bodyShl (a b : @& Nat) : Nat := a <<< b

@[export rt_fold_shl_impl]
def shlImpl (a b : Nat) : Nat := a <<< b

@[extern "rt_fold_shl_impl"]
opaque exportShl : Nat → Nat → Nat

def main (args : List String) : IO Unit := do
  if args.length > 100 then
    IO.println s!"redirected: {(myShl 1 (2 ^ 64)).log2}"
    IO.println s!"body: {(bodyShl 1 (2 ^ 64)).log2}"
    IO.println s!"export: {(exportShl 1 (2 ^ 64)).log2}"
  IO.println s!"redirected small: {myShl args.length 3} {myShl 1 70}"
  IO.println s!"body small: {bodyShl (args.length + 1) 3} {bodyShl 1 70}"
  IO.println s!"export small: {exportShl (args.length + 1) 3} {exportShl 1 70}"
