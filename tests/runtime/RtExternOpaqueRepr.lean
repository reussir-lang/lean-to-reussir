/-!
An `opaque` re-declaration of `lean_string_push` with `UInt32` where Lean's
declaration (`String.push`) has `Char` (review RV8E-10). Both are a 32-bit
scalar at the C level, so natively the runtime's function runs. An extern
of the program is never bound to Lean's runtime (the owner's decision of
2026-10-04; translation plan §5.8, "Externs of the program"), and it has
no Lean definition, so lean2rr refuses it, naming the library's
declaration to call instead (`String.push`).
-/

@[extern "lean_string_push"]
opaque pushCode (s : String) (c : UInt32) : String

def main : IO Unit := do
  IO.println s!"direct: {pushCode "ab" 99}"
  IO.println s!"closure: {["x", "y"].map (pushCode · 33)}"
