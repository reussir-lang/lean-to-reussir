/-! Runtime test: function values that capture nothing, boxed as typed
immediates (rule 1 boxes a list's and an array's elements; the one-word
box keeps a function value's nullary variant as `(num << 32) | index`,
`l2r_any_of_fn`), among them partial applications `tagT Nat`, `two Nat
String` whose erased parameters the target does not take (rule 4: `p<j>`
with `j > 0` and no field), at a type with a phantom domain
(`(β : Type) → Nat → Nat`) and at the same type without it: the enum they
share numbers its variants once (`l2r_fn_of_index_T`). -/
@[noinline] def tagT (_ : Type) (x : Nat) : Nat := dbgTrace s!"tagT {x}" fun _ => x + 1
@[noinline] def two (_ : Type) (_ : Type) (x : Nat) : Nat := x * 2
@[noinline] def apAll (fs : List (Nat → Nat)) (k : Nat) : Nat := fs.foldl (fun a f => a + f k) 0
@[noinline] def apTy (fs : List ((β : Type) → Nat → Nat)) (k : Nat) : Nat := fs.foldl (fun a f => a + f Nat k) 0
def main (args : List String) : IO Unit := do
  let n := args.length
  IO.println (apAll [tagT Nat, two Nat String, (· + n)] 3)
  IO.println (apTy [two Nat, fun _ x => x + 7] 4)
  let arr : Array (Nat → Nat) := #[tagT Bool, two Bool Bool]
  IO.println (arr.foldl (fun a f => a + f n) 0)
