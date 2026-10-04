/-!
`opaque` re-declarations of functions of Lean's runtime with `{α : Type}`
where Lean's declaration has `{α : Type u}` (review RV8E-09). The C ABI is
the same, so natively the runtime's functions run. An extern of the program
is never bound to Lean's runtime (the owner's decision of 2026-10-04;
translation plan §5.8, "Externs of the program"), and these have no Lean
definition: lean2rr refuses them, naming the library's declarations to
call instead (`Array.push`, `Array.size`). Used directly, at `Array Nat`
and `Array String`, through a closure, and in a constant (all reported).
Native Lean compiles the program (`lean -c`).
-/

@[extern "lean_array_push"]
opaque push0 {α : Type} (a : Array α) (v : α) : Array α

@[extern "lean_array_get_size"]
opaque sizeAny {α : Type} (a : @& Array α) : Nat

def k : Nat := sizeAny #["a", "b"]

def main : IO Unit := do
  IO.println s!"push0 nat: {push0 #[1, 2] 3}"
  IO.println s!"push0 string: {push0 #["x"] "y"}"
  IO.println s!"push0 closure: {[#[1], #[2]].map (push0 · 9)}"
  IO.println s!"sizeAny closure: {[#[1], #[2, 3]].map sizeAny}"
  IO.println s!"sizeAny constant: {k}"
