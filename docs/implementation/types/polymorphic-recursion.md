# Polymorphic recursion: keeping instances and types finite

Polymorphic recursion (a function calling itself at `α`, `List α`,
`List (List α)`, …; a nested datatype; a monad transformer applied to
itself) would need infinitely many instances. Reussir's own monomorphizer
cannot handle it, so lean2rr cuts it and sends the rest to the uniform
instance, whose type arguments are all `lcAny` (values in `Box`). Plan
[§2.6](../../translation-plan.md#26-when-a-type-is-not-statically-known)
has the rules. Paths are relative to `lean2rr/LeanToReussir/`.

### Growth is detected along the instantiation path

- **What:** When an instance of `d` is requested at type arguments that
  strictly contain those of an instance of `d` on the path of instances
  that led to the request (`parentOf`), the request goes to the uniform
  instance at once. The path crosses other declarations of the cycle (a
  `where` helper, a mutual partner) and stops at the nearest uniform
  instance of `d`.
- **Why:** One instance per level up to the size bound made a nested
  datatype example 156k lines of `.rr` (4k after, 7445b63). Growth through
  a helper (`nestI` → `nestI.helper` → `nestI` at `StateT Nat m`) was only
  seen once the path was followed (adv3 CN3-06, dcbb31c).
- **Where:** `Mono.lean`: `instanceName` (`grows`, `onPath`,
  `parentOf`).
- **Remove only if:** never.

### Type functions grow by size

- **What:** For a type-function argument (a monad `m` becoming
  `StateT Nat m`), a strictly larger argument counts as growth. Growth
  through a type function gets one typed instance at `F lcAny`, which
  adapts the dictionary the uniform instance passes; its own request at
  `F (F lcAny)` goes to the uniform instance.
- **Why:** After beta reduction the callee's type function no longer
  contains the caller's, so the containment test missed it and only the
  size bound stopped the growth ~43 levels later: 34 s, 3 GB and a 101 MB
  `.rr`, or out of memory (adv2 PRG-01, 44c3bbf). The uniform instance has
  no static dictionary, so the typed `F lcAny` instance is the one that can
  use the dictionary it receives.
- **Where:** `Mono.lean`: `instanceName` (`grows`: `isLambda` and
  `treeSizeUpTo`).
- **Remove only if:** never.

### The uniform instance's requests at `lcAny`-built types stay uniform

- **What:** A request made under the uniform instance of `d` for `d` at
  a type built from its `lcAny` (`List lcAny`, `lcAny × lcAny`) goes to the
  uniform instance too, not to a new typed instance.
- **Why:** A typed instance there would receive whatever the uniform code
  passes, converted structurally on every call, and a value only
  `unsafeCast` to that type (natively any object) could not be converted
  at all (adv4 RP4-03/RP4-07, aefebc6).
- **Where:** `Mono.lean`: `instanceName` (the `k.typeArgs.all (· ==
  anyExpr)` case).
- **Remove only if:** never.

### Bounds cut growth that no path shows

- **What:** A type argument deeper than 64, or of 256 tree nodes or more,
  becomes `lcAny`. Past 1024 instances of one declaration, every further
  instance is the uniform one, with no static dictionaries either.
- **Why:** The set of instances must stay finite whatever the program.
  Tree size is bounded as well as depth because a type such as `α × α`
  doubles at each step, and later stages traverse it as a tree (adv
  round 1, 3f59239).
- **Where:** `Mono.lean`: `MonoConfig.maxTypeArgSize` (64),
  `MonoConfig.maxInstancesPerDecl` (1024), `normTypeArg`, `treeSizeUpTo`,
  `instanceName`; static dictionaries: `staticDict?` (depth 64).
- **Remove only if:** never. The values can change; the `--stats` dry run
  (`Specialize.lean`: `visitConstApp`) bounds its type arguments the same way
  (round 7 RV7F-03, 4ad6df7).

### A field type that grows is the uniform instantiation

- **What:** While the fields of an inductive are translated, a requested
  instantiation of the same inductive that strictly contains the arguments
  of one on the path (or that is built from the `lcAny` of the uniform
  instantiation on the path, or that has 256 instantiations of its
  inductive on the path already) is translated at the uniform
  instantiation instead: schematically, `Nest Nat` is
  `enum Nest_Nat { nil, cons(Nat, Nest_Box) }`. Only an inductive whose
  block uses its types at other arguments than its parameters (an `unsafe
  inductive`) is checked; a safe one is never cut.
- **Why:** `unsafe inductive Nest α | nil | cons (x : α) (rest : Nest (α × α))`
  made lean2rr translate `Nest (Nat × Nat)`, `Nest ((Nat × Nat) × …)`, …
  until it ran out of memory (round 6 TY6-01, f23fb89).
- **Where:** `LowerBase.lean`: `nonUniformInductive`, `usesOtherArgs`,
  `typeGrowsOnPath`, `nominalArgs`, `nominalType` (`pendingBoundary` is the
  path); plan [§5.1](../../translation-plan.md#51-type-translation),
  "Polymorphic recursion in a type".
- **Remove only if:** never.

### Result types of polymorphically recursive functions

- **What:** Stage 3 counts a self call that binds the result at another
  type than the declaration's own among the call sites' result types, so
  the uniform instance's result stays uniform.
- **Why:** See [type-recovery.md](type-recovery.md#result-types-come-from-the-returned-values-and-from-the-callers)
  (adv2 PrgPoly1).
- **Where:** `MonoRetype.lean`: `callSites` (its self-call case),
  `CallSites`.
- **Remove only if:** never.
