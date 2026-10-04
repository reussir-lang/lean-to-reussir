/-!
`@[extern]` declarations of the program in their other forms (review
rv8/ext round 1, ExtImpl): inline C (`@[extern c inline "…"]`, natively C
pasted at each call), a per-backend entry (`@[extern c "sym"]`), an extern
with `@[implemented_by]` (natively and here its callers call the target,
`fastImpl`, not the C code nor the body), and an `@[implemented_by]` target
that is itself an extern. lean2rr compiles their Lean definitions; the C
code (`RtExternForms.ffi.c`) is linked into the native build only.
-/

def fastImpl (n : Nat) : Nat := n + 1000
@[extern "rt_forms_slow", implemented_by fastImpl]
def slow (n : Nat) : Nat := n + 1

@[extern "rt_forms_target"]
def target (n : Nat) : Nat := n * 3
@[implemented_by target]
def spec (n : Nat) : Nat := n + n + n

@[extern c inline "#1 + #2"]
def addInline (a b : UInt64) : UInt64 := a + b

@[extern c inline "(#1 == 0 ? 7 : #1)"]
def orSeven (a : UInt32) : UInt32 := if a == 0 then 7 else a

@[extern c inline "lean_nat_add(#1, #1)"]
def dblNat (n : @& Nat) : Nat := n + n

@[extern c "rt_forms_c"]
def perBackend (n : UInt32) : UInt32 := n + 5

def main : IO Unit := do
  IO.println s!"slow {slow 1} {[1, 2].map slow}"
  IO.println s!"spec {spec 4} {[1, 2].map spec}"
  IO.println s!"addInline {addInline 2 3} {[1, 2].map (addInline 10)}"
  IO.println s!"orSeven {orSeven 0} {orSeven 9}"
  IO.println s!"dblNat {dblNat 21} {dblNat (2 ^ 70)}"
  IO.println s!"perBackend {perBackend 1} {[1, 2].map perBackend}"
