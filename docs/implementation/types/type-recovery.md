# Stage 3: recovering types mono lost

Mono can type a binder `lcAny` although its value has one precise type: types
inferred during the passes go through erased signatures, and Lean's
uniform-representation library code casts with `unsafeCast`, which LCNF
erases. A binder left at `lcAny` is a `Box`, unboxed at every precise use.
(Data types have one representation whatever their type arguments, so
`List lcAny` and `List Nat` are one type; Stage 3 types locals, it no
longer chooses layouts.) Stage 3 recovers the types the program
determines, by a bounded whole-program fixpoint (whatever is not recovered
stays `lcAny`). It is required, not optional
(`stage3-types` in `Opt/Registry.lean`). Plan
[§4](../../translation-plan.md#4-stage-3--check-and-recover-lost-types).
`lean2rr --emit retyped` prints its result. Paths are relative to
`lean2rr/LeanToReussir/`. The last entry is a related step that runs
before Stage 3: data that Lean's `toLCNF` typed `◾`.

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
  over-applied). A saturated self call counts as a call site too, except a
  tail call (`let y := f …; return y`) that binds the result at the
  declaration's own result type.
- **Why:** The unboxing moves from every caller to the callee's
  `return` (for a constant: once instead of at every read). The callers'
  binders give the type of the outermost call only. A tail self call
  returns its value as the declaration's result, so by induction it has
  that type too. Any other self call can give a value of another type:
  polymorphic recursion into the uniform instance (`FSeq.flatten` at
  `lcAny` calls itself at `lcAny × lcAny`, so the one typed caller's
  `List (Nat × Nat)` does not hold at the deeper levels: adv2 PrgPoly1,
  513379f; runtime test `RtPolyRecResult`), or a self call whose binder has
  the declaration's own result type `lcAny` but whose value has a type
  computed from a value (`f {α} (n) (x : α) : α` at `lcAny`, called at
  `Big 70` and calling itself at `T k`: hunt MONO-01; runtime test
  `RtSelfCallResult`). Both programs panicked "unreachable".
- **Where:** `MonoRetype.lean`: `returnTypes`, `refineSignature`
  (from the returns); `callSites`, `CallSites` (`escapes`),
  `constAppsTail`, `resultsFromCallers` (from the callers).
- **Remove only if:** never.

### Externs at unknown types type their results

- **What:** A saturated call of a polymorphic extern instantiated at
  `lcAny` (`Array.uget` and `Array.uset` at `NonScalar`) whose arguments
  determine the type arguments binds its result at the type the extern
  returns at them. The base extern's declared parameter types are matched
  strictly against the argument types, and every argument must then have
  exactly its parameter's mono type (`toMonoTypeKeep`, as Stage 2 types an
  extern instance) or be a placeholder. Over-applied calls (the element of
  an array of functions, applied) are covered too. The callee stays the
  instance at `lcAny`.
- **Why:** The result binder gets its precise type: unboxed once, at the
  call (Stage 4 converts an extern call's result to the binder's type).
  An extern does not depend on its type arguments, and with one
  representation per datatype the instance at the precise types would
  differ only in its result type: the call was redirected to a new
  instance, built through Stage 2's passes, until rule 1 (simplicity
  review of rule 1, finding 2). (Before arrays had one representation, an
  over-applied call converted the whole captured array on every call:
  FN-02, 1fcb07f.)
- **Where:** `MonoRetype.lean`: `externResultType?`, `fwdCode`.
- **Remove only if:** never.

### A parameter of type `lcErased` that receives data gets `lcAny`

- **What:** A parameter of type `lcErased` (of a join point, of a local
  function applied directly, or of a declaration with code called
  directly, also partially) that receives data at some jump or call gets
  the type `lcAny`: a boxed data parameter (also in its function's type).
  Data is a variable not bound to `◾` whose type is not `lcErased` and not
  a type former type (a sort, or a function type that ends in one). A
  retyped parameter is data in turn, so the step repeats until nothing
  changes. It runs on Stage 1's instances (before `toMono`, which passes
  `◾` at every call to a declaration's erased parameter) and again on
  Stage 2's output (a join point that Lean's mono passes made). A jump or
  call that passes `◾` to a retyped parameter passes `box(0)` (rule 4e).
  Rule 4 and its flow analysis (`ErasedDomains`) read the new type: the
  parameter is kept and is a `Box`.
- **Why:** A Lean 4.34.0 compiler bug (plan
  [§10](../../translation-plan.md#10-known-divergences-and-unsupported-features),
  "Compiler: Lean bugs we do not reproduce"): `toLCNF` joins the types of
  a `match`'s arms with `joinTypes`, which gives `◾` when one arm gives a
  type or a proof, so the join point after `let v : T b := match b with |
  true => fun _ => True | false => n` gets a parameter of type `lcErased`
  that the `false` arm passes `n` to; Lean's specializer copies that type
  to the declaration it makes for a lambda over `v`. Native Lean and rule 4
  remove such a parameter and compute with `box(0)`: a wrong value
  (`f2 false 41` gave 1, the kernel 42) or a crash (a `String`, an
  `Array`; tests `RtJoinErased*`). A type or proof parameter never receives a variable
  of a data type (proofs and types have the type `lcErased` or a type
  former type), so it stays erased: the classic corpus's `--emit retyped`
  output is the same with and without the step.
- **Where:** `ErasedData.lean`: `retypeErasedData`; `ErasedData.scan`
  (the parameters that receive data), `rewrite` and `retypeParams` (the
  new types); `../Main.lean`: `pipeline` (after `monomorphize` and after
  `runStage2`).
- **Remove only if:** Lean's `toLCNF` and `mkCasesResultType` stop
  typing such a `match` `◾` (`joinTypes` gives `lcAny` for `◾` and data).
  Not covered now: data that a closure carries to an erased domain, and
  data that Lean's `simp` already replaced by `◾` (a `let` of type `◾`).
