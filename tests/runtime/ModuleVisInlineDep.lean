module

/-! Companion module of RtModuleVisInline (`RtModuleVisInline.deps`), a
`module` file: `f` is a public `def` without `@[expose]`, so its body is
not exported to a `module` importer, natively neither for the kernel nor
for the compiler (its mono code is private). `f`'s one call, `noisyP rfl`,
is a closed term of this module (`f._closed_1`), whose evaluation traces
`noisy`. -/

@[noinline] public def noisyP (_h : 1 = 1) : Nat := dbgTrace "noisy" fun _ => 7

public def f (_x : Nat) : Nat := noisyP rfl

/-- Inlines `f` natively too (same module): its closed term is `f`'s. -/
@[noinline] public def h (x : Nat) : Nat := f x + 1
