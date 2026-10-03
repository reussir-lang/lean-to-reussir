# Stage 3: recovering types mono lost

Mono can type a binder `lcAny` although its value has one precise type: types
inferred during the passes go through erased signatures, and Lean's
uniform-representation library code casts with `unsafeCast`, which LCNF
erases. A binder left at `lcAny` is a `Box`, converted at every precise use
(an array element by element). Stage 3 recovers the types the program
determines, by a bounded whole-program fixpoint (whatever is not recovered
stays `lcAny`). It is required, not optional
(`stage3-types` in `Opt/Registry.lean`). Plan
[§4](../../translation-plan.md#4-stage-3--check-and-recover-lost-types).
`lean2rr --emit retyped` prints its result. Paths are relative to
`lean2rr/LeanToReussir/`.

### Types come from what flows in, never from uses

- **What:** A binder's type is recomputed from its definition: a `cases`
  field from the constructor at the discriminant's type, only when that
  type is the constructor's inductive (or `T._impl` for a type with
  computed fields) applied to its parameters, never `lcAny`; a call from the
  callee's signature, a join-point parameter from its jump arguments when
  all are known and agree. A use at a precise type does not retype the
  binder. The one exception is a placeholder `let z := ◾`, which has no
  value to convert and gets the type its uses agree on.
- **Why:** With a type that depends on a value (`data : Array t.denote`),
  a use as `Array Nat` speaks only for the branch where `t = .nat`. Moving
  the conversion from the use to the binder made it run, and fail
  ("INTERNAL PANIC"), on the other paths (adversarial review, 1c940d5).
  Field types taken for any discriminant whose type had a constant head
  gave an `lcAny` scrutinee of a dependent or existential type the
  parameters' types: wrong fields, `Array.map (·.1)` placeholders and an
  "unreachable" panic (round 7 RV7F-01, root of RV7D-01; e318fbd; tests
  `RtDepFields`, `RtLcAnyProj`).
- **Where:** `MonoRetype.lean`: `localRetype`, `ctorFieldTypes`,
  `collectUses`, `fromUses` (placeholders only), `refineTo?`, `refines`.
- **Remove only if:** never.

### Constructor applications are typed conservatively

- **What:** A constructor application gets the type its argument types
  determine by first-order matching. A type parameter that two arguments
  give differently, or that an argument leaves `lcAny`, stays `lcAny`. A
  parameter that no field determines (the error type of `EST.Out.ok`)
  comes from the type the binder already has.
- **Why:** A `cons` of a `Name × String` onto a `List Dynamic` was retyped
  `List (Name × String)`, whose tail could then not be converted (I18Dyn,
  797dfaa).
- **Where:** `MonoRetype.lean`: `ctorAppType`, `matchTy`,
  `ctorFieldTypes`.
- **Remove only if:** never.

### Result types come from the returned values and from the callers

- **What:** A declaration whose result is `lcAny` gets `T` when all its
  returned values have type `T`: results of its own saturated self calls do
  not count, nor do constructors without fields of `T`'s own inductive.
  It also gets `T` when every saturated call binds the result at `T` and
  the declaration is used nowhere else (not as a closure, not
  over-applied). A self call that binds the result at another type than
  the declaration's own counts as a call site.
- **Why:** The conversion moves from every caller to the callee's
  `return` (for a constant: once instead of at every read). The self-call
  case is polymorphic recursion into the uniform instance: `FSeq.flatten`
  at `lcAny` calls itself at `lcAny × lcAny`, so the one typed caller's
  `List (Nat × Nat)` does not hold at the deeper levels, and the program
  panicked "unreachable" (adv2 PrgPoly1, 513379f; runtime test
  `RtPolyRecResult`).
- **Where:** `MonoRetype.lean`: `returnTypes`, `refineSignature`
  (from the returns); `callSites`, `CallSites` (`escapes`) and the second
  loop of `paramsFromCallers` (from the callers).
- **Remove only if:** never.

### `map` loops return the type of the values they store

- **What:** The loop of `Array.mapMUnsafe` or `Array.mapFinIdxMUnsafe`
  (recognized by name, as Lean's specializations of it or their `_redArg`
  part) returns `Array β` when every value it stores with `Array.uset`,
  placeholders aside, has type `β`, and the loop's array stays within the
  loop.
- **Why:** The result of `xs.map f` is bound at `Array NonScalar`, that is
  `Array lcAny`, and so is every loop parameter it reaches; each `ys[i]!`
  then converted the whole array (quadratic, F02, 011966c).
- **Where:** `MonoRetype.lean`: `isMapLoop`, `mapLoopElem?`,
  `refineSignature`. Loops whose element representation changes:
  [../optional-passes.md](../optional-passes.md) (`split-map-loops`) and
  [../representations/arrays.md](../representations/arrays.md#maps-that-change-the-element-representation-write-a-new-array).
- **Remove only if:** Lean's `Array.map` stops casting through
  `NonScalar`.

### Parameters take the type every caller passes

- **What:** A parameter whose type holds an erased array (`Array lcAny`,
  `Option (Array lcAny)`, …) or a typed reference gets `T` when every call
  site passes it at `T`. The assumption is checked: the body is retyped
  under it, and the self calls must pass `T` back. Only call sites in
  declarations reachable from the entry point count, and a partial
  application that leaves the parameter open blocks the rule.
- **Why:** This is what makes `xs.map (· * 2)` run on the precise array,
  in place. Other `lcAny` parameters are left alone: code over `Dynamic`
  casts its value, in branches a runtime check rules out, to types a
  precise parameter could not be converted to.
- **Where:** `MonoRetype.lean`: `paramsFromCallers`, `selfCallsAgree`,
  `CallSites`.
- **Remove only if:** never.

### Externs at unknown types are re-instantiated

- **What:** A saturated call of a polymorphic extern instantiated at
  `lcAny` (`Array.uget` and `Array.uset` at `NonScalar`) is redirected to
  the extern's instance at the type arguments its arguments determine,
  provided every argument then has exactly the expected type or is a
  placeholder. Over-applied calls (the element of an array of functions,
  applied) are covered too.
- **Why:** An extern does not depend on its type arguments; only the
  representation changes. Over-applied, the whole captured array was
  converted on every call (FN-02: 3.33 s → 0.06 s, native 0.05 s;
  1fcb07f).
- **Where:** `MonoRetype.lean`: `reinstantiate?`, `externInstance`.
- **Remove only if:** never.

### References created at a precise type are typed

- **What:** An instance of `ST.Prim.mkRef` at a precise `α` returns
  `typedRef α`, a type only lean2rr uses, and the rules above carry it to
  the binders the reference flows into.
- **Why:** Mono types every `ST.Ref` `lcAny`; without this an
  `IO.Ref Nat` counter or a `StateRefT` state goes through a `Box` and a
  dispatch at every access (see
  [../representations/references.md](../representations/references.md)).
- **Where:** `MonoRetype.lean`: `typeMkRef`; `MonoTypesKeep.lean`:
  `typedRefName`, `hasTypedRef`.
- **Remove only if:** never.
