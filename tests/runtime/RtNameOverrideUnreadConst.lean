/-! Runtime test (review of a bug hunt of the names lean2rr recognizes,
2026-10-27; optimization `unread-consts`): a program's own `unsafe`
implementation named `stepI._override`, the `implemented_by` of `stepI`.
`UnreadConsts.isComputedFieldImpl` took every `p._override` that is `p`'s
`implemented_by` for a computed-field implementation Lean made, so neither
the taint of an `@[implemented_by]` of the program nor the check of the
program's `unsafe` code applied, and the unread constant `spin` was left
out. With an implementation that gives the step 0 (the specification
`stepI_pos` says at least 1), natively the module initializer evaluates
`spin` and never ends, while lean2rr ran `main`. Here the implementation
gives 8, so `spin` ends natively too; the `.l2r-debug` file checks that it
is kept (dev left it out). Now `p._override` counts only for a
constructor or the `casesOn` of a type with computed fields, or a
`@[computed_field]` function: the unread constant `treeInfo` over the type
`Tree`, whose computed field and constructors have Lean's `_override`
implementations, is still left out. -/

unsafe def stepI._override (n : Nat) : Nat := n + 1

@[implemented_by stepI._override]
def stepI (n : Nat) : Nat := n - n + 1

theorem stepI_pos (n : Nat) : 0 < stepI n := by simp [stepI]

def spin : Nat := Id.run do
  let mut acc := 0
  for i in ({ start := 0, stop := 100, step := stepI 7, step_pos := stepI_pos 7 } : Std.Legacy.Range) do
    acc := acc + i
  return acc

inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)
with
  @[computed_field] weight : Tree → Nat
    | .leaf n => n
    | .node l r => l.weight + r.weight

def treeInfo : Nat :=
  let t := Tree.node (.leaf 3) (.node (.leaf 4) (.leaf 5))
  t.weight + (match t with | .leaf n => n | .node _ _ => 1)

def main (args : List String) : IO Unit := do
  IO.println s!"main ran {args.length}"
  let t := Tree.node (.leaf args.length) (.leaf 2)
  IO.println s!"{t.weight} {stepI 3}"
