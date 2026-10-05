/-! Runtime test for the optional pass `conv-liveness` (plan §5.3, "Only
for live code"): the helpers are generated only for the function values and
`Box` variants that live code builds, so every place that builds one must
be seen, including those outside `main`'s own code. The program can cast
(`idSafe` is implemented by an `unsafe` function), so its unboxing
functions also get cast arms.
- an initializer builds a closure and stores it in a reference (in a
  `Box`); `main` applies it, at the closure's own type and, through a
  package, at the uniform type (a wrapper built by a conversion function);
- a partial application built only inside an application function: `f n`
  of a target of arity 3 (`p1_add3`), stored in a list, then applied to
  two more arguments;
- a closure a task runs (the runtime calls the task dispatch, which applies
  it), whose result is boxed in the task's state;
- an existential package whose payload is read back at its own type, and
  one cast by `unsafeCast` to an isomorphic structure. -/

initialize hook : IO.Ref (Nat → Nat) ← IO.mkRef (fun n => n * 3 + 1)

unsafe def idImpl (n : Nat) : Nat := n
@[implemented_by idImpl] def idSafe (n : Nat) : Nat := n

def add3 (a b c : Nat) : Nat := a + 10 * b + 100 * c

structure Fn3 where
  α : Type
  f : α
  part : α → Nat → List (Nat → Nat → Nat)

@[noinline] def partFn3 (p : Fn3) (n : Nat) : List (Nat → Nat → Nat) := p.part p.f n

structure PkgF where
  α : Type
  r : IO.Ref (Nat → α)
  render : α → String

@[noinline] def readF (p : PkgF) (n : Nat) : IO String := do
  return p.render ((← p.r.get) n)

structure A where
  x : Nat
  s : String

structure B where
  y : Nat
  t : String

structure Pkg where
  α : Type
  v : α

@[noinline] def pkgA (k : Nat) : Pkg := ⟨A, ⟨k + 5, "a"⟩⟩
@[noinline] unsafe def asB (p : Pkg) : String := match (unsafeCast p.v : B) with
  | ⟨y, t⟩ => s!"{y} {t}"

unsafe def main (args : List String) : IO Unit := do
  let k := idSafe args.length
  let h ← hook.get
  IO.println s!"hook {h (k + 4)}"
  IO.println s!"hook uniform {← readF { α := Nat, r := hook, render := toString } (k + 5)}"
  let p : Fn3 := ⟨Nat → Nat → Nat → Nat, add3, fun f n => [f n, f (n + 1)]⟩
  for g in partFn3 p k do
    IO.println s!"partial {g 1 2} {g 3 (k + 4)}"
  let t ← IO.asTask (do return (← hook.get) (k + 10))
  match ← IO.wait t with
  | .ok v => IO.println s!"task {v}"
  | .error _ => pure ()
  IO.println s!"cast {asB (pkgA k)}"
