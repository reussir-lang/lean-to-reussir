# Optional passes

Every optimization is a module of `lean2rr/LeanToReussir/Opt/` registered by
one line in `Opt/Registry.lean` (`optimizations`), and all are on by
default but one: `unread-fields` is off by default, by the owner's
decision of 2026-10-08, an exception to the rule that every optional pass
is on (`--enable-opt unread-fields`, or `L2R_ENABLE_OPTS=unread-fields`,
turns it on). `lean2rr --list-opts` prints the registry; `--disable-opt NAME`
(or `L2R_DISABLE_OPTS=a,b` for `scripts/l2r.py`) turns one off for a run.
The core translation is correct with all of them off. No pass is switched
per program or benchmark: each restricts itself only through checks it
makes automatically on every program, the "guard" column: what soundness
requires, and for some passes bounds on code size or translation work, or
the shapes where the pass applies at all. Plan
[§1](../translation-plan.md#code-structure-and-passes) ("Code structure
and passes").

## The passes, in installation order

| Pass | What it does | Guard (soundness; other limits) | Details |
|---|---|---|---|
| `unread-fields` (off by default) | before Stage 3, a value that a constructor stores in a field no kept code reads (a callback an initializer registers for Lean's elaborator; data, such as a `ToExpr` instance's `toTypeExpr`) becomes `◾`, with the unused parameters of declarations and join points; what only those reached is left out, and the `Lean` package's `initialize` constants that kept code no longer reads do not run | a field counts as read when kept code projects it or uses its binder in a match, and every field of a type that an extern takes by its declared parameter types (not a type variable), of `IO.FS.Stream`, the IO results, tasks, thunks, references and promises; a `let` that may have an effect stays; never a field of a type the runtime represents itself (`builtinTypeNames`); nothing in a program that can cast (`programCasts`, on the code kept); in a program whose kept code creates tasks, only a value that cannot hold a task (nor can a closure's captured values); in one whose kept code makes resources, no value that may hold one | below |
| `field-order` | record fields by decreasing alignment, no padding | none needed: every access goes through the constructor layout | [records](representations/records.md#fields-are-ordered-by-decreasing-alignment) |
| `value-structs` | a structure with one relevant field is a `[value]` struct | not when the field's type is being translated (no type contains itself by value) | [records](representations/records.md#one-field-structures-are-value-structs) |
| `compact-arrays` | an `Array` of a scalar is `RVec<u8\|u16\|u32\|u64\|f32\|f64>` of its storage kind; the loops of `Array.map` typed at their element types (Stage 3); `Array lcAny` parameters typed from their callers when they get compact arrays; a field `Array α` boxed in an inductive the program uses with a compact array | the whole-program check (`compactArrayKinds`) turns a storage kind off when a value of it could meet an array of boxes: a crossing at any edge of the reachable code, a flow class that holds `Array lcAny`, or a program that casts (axioms that state a `Bool` equation aside); a typed `map` loop only in Lean's shape, its stored values checked once typed; a parameter only when every caller passes one type and its own calls agree | [compact arrays](representations/compact-arrays.md) |
| `placeholder-cache` | placeholders that would allocate built once, in a once-cell | only heap placeholders; a placeholder is never inspected | [placeholders](representations/placeholders.md#placeholders-that-allocate-are-built-once) |
| `boxed-consts` | a constant whose boxing allocates boxed once, in a once-cell (native Lean's `_boxed_const`) | only a variable bound to a declaration without parameters that runs once (cached) or cannot trace or panic (`cheap-consts`) and whose value is not a literal that boxes as an immediate (`constIsImmediate`), or to a `UInt64` literal from 2^63, at a type whose boxing can allocate (`boxAllocates`), outside the body of a declaration without parameters (`inConstBody`: it runs once); a constant is pure, so one box does as well as a new one | below |
| `float-lits` | float literals folded to their bits at compile time | literal arguments only (the functions are pure and total): a `let` of a literal, a `Bool` discriminant inside an alternative that fixes it, a join point parameter to which every jump passes the same literal; work bound: exponent ≤ 2000, mantissa (or `Float.ofNat`'s argument) at most 4096 bits | below |
| `cheap-consts` | constants of small literals recomputed at each use | `isCheapConst`: unboxed types only, every `Nat`/`Int` small (`Nat` literals and `Nat.succ` < 2^63, `Int.ofNat`/`Int.negSucc` of `int32` values), other constructors, total scalar conversions, other cheap constants; no strings | below |
| `prelude-repr` | `Nat.repr`/`Int.repr` by the runtime's GMP code | none needed: the same strings (unary calls only) | [nat-int](representations/nat-int.md#natrepr-of-0127-shares-one-string-per-number) |
| `jp-sink` | join points moved to the smallest code containing their jumps | moves only, never duplicates; binders are unique | [join points](control-flow/join-points.md#join-points-are-sunk-before-the-choice-jp-sink) |
| `jp-small` | small join points duplicated at their jumps (J1′) | none needed for soundness (a copy runs the same code once per path); code-size bounds: own body ≤ 40, a copy ≤ 480 (join points jumped to once counted at full size), extra copies ≤ 2000 (4000 for a loop's continuation); never a J2 join point | [join points](control-flow/join-points.md#small-join-points-are-duplicated-within-three-bounds-jp-small) |
| `state-machines` | J4 entered without allocation: every variant nullary (the entry enum then a `[value]` enum, a scalar tag), values passed in parameter slots; a jump passes on unchanged the slots its arm does not bind | a jump puts only placeholders in the slots it does not fill (a fresh one, or a slot its arm does not bind, which holds one), never live values; a type without a finite placeholder (`zeroFinite`) gets no slot | [state machines](control-flow/state-machines.md#state-machines-entered-without-allocation-state-machines) |
| `lazy-fields` | fields of a live matched value bound where used | shared values matched at their own type; variables another hook bound again are left alone; applies only where the value is stored, returned or passed whole | [cases](control-flow/cases.md#fields-of-a-live-matched-value-are-bound-where-they-are-used-lazy-fields) |
| `nullary-scrutinee` | in a field-less arm, the matched value rebuilt | only arms of constructors without fields that use the value | [cases](control-flow/cases.md#the-matched-value-of-a-nullary-arm-is-rebuilt-nullary-scrutinee) |
| `sink-proj` | structure projections sunk into the branches that use them | the projection is unused later in the block and in the condition, and no binder clashes; applies only where some branches use it while another keeps the structure whole | [cases](control-flow/cases.md#structure-projections-move-into-the-branches-that-use-them-sink-proj) |
| `fresh-rebuild` | an arm returning a fresh matched value returns it rebuilt | the value is freshly built (whole-program analysis); the arm binds every field and only returns it | [cases](control-flow/cases.md#fresh-values-returned-whole-are-rebuilt-fresh-rebuild) |
| `flatten-structs` | a structure argument of a loop (join point, self-recursive function) and a structure or two-constructor result passed as its fields at their precise types (worker/wrapper) | a value is split only where its fields are known at every jump, self-call and return; a whole use keeps that level whole, except two rebuilds that add no allocation: a loop's parameter at the loop's exit after a step that built a new value (the first step peeled into the wrapper), and a call's result (each value built at most once per run of its scope); a value whose object is inspected (`ptrAddrUnsafe`, `dbgTraceIfShared`, `isExclusiveUnsafe`) or that the caller passed in is never rebuilt; a result level stays whole when callers (or the wrapper) only use it whole, or when a shared object may arrive there; results with function types or without finite placeholders are not split; in a program that creates resources, declarations with resource parameters or results are left alone (their inferred borrows stay Lean's); bounds: 8 levels, 16 variables, peeled bodies of at most 300 nodes | below |
| `conv-liveness` | unboxing, application and conversion helpers generated only for what live code reaches; unreachable functions dropped | none needed for soundness: an arm left out matches a variant that no live code builds, so no value of it exists at run time; every identifier of raw text, of the prelude and of atoms is a root, every arm of other matches counts, and a variant that text names counts as built | [liveness](conversions/liveness.md) |
| `merge-fns` | generated functions equal up to their own and local names merged: a copy calls the first, calls of a copy call the first | the canonical texts are equal (the same code once names are renamed in binding order, inside atoms too); a copy keeps its name and calls the function its first ends at, never itself; nothing is removed; a function called from one place only stays (LLVM inlines it there), except startup code (`_init`, `l2r_persist_`) | below |
| `prelude-liveness` | the runtime prelude's functions that the program text does not name, directly or through the prelude's kept functions, are left out of the `.rr` | none needed for soundness: a function no text names cannot be called; every identifier of the generated text and of the prelude's items that always stay (the `extern "rust"` blocks, the types) is a root, also in string literals and in comments at the end of a line; only functions of the form `fn NAME` at column 0, outside a texture, with no attributes but `#[ffi(import)]` and `#[transform_anchor]`, can go; a name the scan missed would make rrc stop with an unknown function, not build another program | below |

### Values in unread fields are left out (`unread-fields`)

- **What:** Off by default (the owner's decision of 2026-10-08, an
  exception to the rule that every optional pass is on);
  `--enable-opt unread-fields` turns it on. After Stage 2, before Stage 3
  (`PassConfig.prunePasses`, called from `Main.pipeline`), a usefulness
  fixpoint from the entry point's callees, the startup steps that always
  run and the `IO.Error` builders: a field (constructor, index) is read
  when kept code projects it or matches the constructor and uses the
  field's binder; a variable is useful when kept code returns, matches or
  applies it, passes it to an extern, or projects it, when a useful `let`
  computes from it, or when a read field, a useful parameter of a
  declaration or a useful parameter of a join point receives it; a `let`
  stays when its variable is useful or its value may have an effect (a
  full application of a declaration, an extern or a function value). Then,
  in the declarations kept, each argument at an unread field (a function
  value or data, but not a field of a type that lean2rr's runtime
  represents itself, `builtinTypeNames`: strings, arrays, numbers, thunks,
  tasks) and each argument at an unused parameter of a declaration or a
  join point becomes `◾`; a `let` that is not useful and has no effect
  goes; a declaration that no kept `let` mentions goes. The lowering
  passes a placeholder for each `◾` (at a function type the nullary
  variant `z`). A step of the `Lean` package's `initialize` constants that
  the program uses stays only when kept code still reads the constant
  (`Main.pipeline` drops the others; see
  [startup/order.md](startup/order.md#the-librarys-initializers-run-at-their-modules-place-always)).
  Example: Batteries' `initialize` blocks call `addLinter` with a
  `Linter` whose `run` no kept code reads, and `registerTagAttribute`,
  whose `AttributeImpl.add` closure captures the caller's `validate`
  argument: the closure, then the unused parameter `validate`, then the
  caller's lambda and everything only they reach go. For a program that is
  still refused, `L2R_UNREAD_FIELDS_WHY=1` prints, for each extern of the
  `Lean` package that kept code reaches, the chain of declarations and
  reasons that keeps it.
- **Why:** lean2rr keeps every function that kept code mentions. Natively
  the initializers run at startup and store the callbacks, which only
  Lean's elaborator calls; through them a program that imports Batteries
  reached 29 C++ functions of the `Lean` package that lean2rr's runtime
  does not have, and was refused (a driver that runs cedar-spec
  8029f0eb's authorizer, `Cedar.Spec.isAuthorized`, on protobuf
  requests). With the pass, 8,335 of 25,363 declarations are kept
  (the fixpoint takes 49 rounds), no C++ function of the `Lean` package
  is left, and the program's output on three inputs of 500 requests
  equals native's byte for byte. Data too, since the owner's approval of
  2026-10-08: lean-regex 32af6f33 derives `Lean.ToExpr` for its types, and
  each instance, a program constant evaluated at startup, stores in its
  `toTypeExpr` an `Expr` that Lean's C++ builds (`Lean.Expr.mkData`,
  `Lean.Level.mkData`); no kept code reads it. With data replaced too, the
  unpatched program translates (979 of 1,443 declarations kept) and its
  driver's output on 1 MB of Dickens and 1 MB of Lean source equals
  native's.
- **Soundness:** a field counts as read wherever code lean2rr does not see
  may read it: every field of an inductive that an extern which kept code
  mentions takes, by all the extern's declared parameter types (also when
  the extern is a function value or partially applied: review of the
  pass, F1, test `RtUnreadFieldsExternFn`), also through other
  inductives, function types and type-level definitions (`IO.setStderr`
  takes an `IO.FS.Stream`), except a parameter declared at a type
  variable (the runtime only stores such a value and gives it back:
  `Array.push`); every field of `IO.FS.Stream` (the runtime writes panics
  and traces with the current stderr's `putStr`, `l2r_stderr_put`), of
  the IO results `EST.Out` and `ST.Out` (the entry point reads `main`'s,
  the startup chain stores an initializer's value and reports its error;
  F4), of tasks, thunks, references and promises; no field of a type that
  lean2rr's runtime represents itself (`builtinTypeNames`) is replaced.
  No code reads a field generically, data included: structural equality,
  hashing, `Repr`, `ToString`, `Ord` and the other derived instances are
  Lean code, which matches the value and uses each field it reads (test
  `RtUnreadFieldsDataRead`); the runtime prints only strings, and an
  uncaught error with `IO.Error.toString`, a root; the one structural
  equality lean2rr's runtime implements, `lean_name_eq`, is an extern, so
  `Lean.Name`'s fields count as read; `shareCommon` is the identity and
  `ShareCommon`'s equality and hash compare addresses; the persist walk
  only looks for tasks (the task check below). A declaration's parameter
  has its type (F2). A program that can read
  a value as another type (`programCasts`, computed on the declarations
  kept) is left as it is. In a program whose kept code creates tasks
  (`programCreatesTasks`, on the declarations kept), a value (a closure or
  data) is replaced only when it cannot hold a task, nor can the values a
  closure captures (`holdsNoTask`, or the same test on a constant's
  value): natively a constant's first evaluation waits for the tasks its
  value holds, captured values included. In a program whose kept code makes resources
  (`programMakesResources`: files, child processes, promises), a value that may
  hold one is not replaced, at a field or at an unused parameter (F3, test
  `RtUnreadFieldsHandle`): natively the closure keeps the handle alive,
  and a handle released earlier is flushed and closed earlier. Which
  values may hold one is a flow-insensitive over-approximation over the
  kept code (`taint`): the results of the externs that make resources
  (`resourceExterns`), and what is computed from such a value, stored in
  a field, passed to a parameter or a join point, or returned (an
  `initialize` constant's value is its initializer's result); a value
  given to an extern that may keep it (any parameter but a handle's or a
  child process's) or to a function value makes every extern's and
  function value's result, and the parameters of every declaration used
  as a function value, suspects too (`rEscape`); when a declaration used
  as a function value may return one, so may every function value's and
  extern's result (`rFnRet`: `IO.asTask`, `Thunk.get` call function
  values); only values whose type may hold one count (`mayHoldRes`:
  `mayHoldCode`, or Flatten's `holdsResource`). Both checks start as a
  new attempt when the kept code creates tasks or makes resources, and
  again while the kept code of the last attempt (which only grows) shows
  a new kind: at most three attempts (re-review N1, N2). Address and sharing tests read no field: the object stays the
  same object at the same address; a value that a closure left out
  captured has one reference less, which `dbgTraceIfShared` can show, and
  lean2rr's counts are not native's anyway
  ([representations/identity.md](representations/identity.md#sharing-is-not-observable)).
  Not covered: messages (accepted, plan §10). A full application whose
  arguments are not all constants stays, even when its result only fed a
  replaced field (it may panic or trace). But Stage 2 lifts every full
  application with constant arguments into a closed term, and the read of
  a closed term has no effect, so it goes with the field: a closed term
  read only to build a value the pass leaves out (a callback or data) is
  not evaluated, and the `panic!` and `dbg_trace` messages of its
  evaluation, which native Lean prints, do not show. This holds for the
  program's own constants, `{ s with … }` updates and `initialize`
  blocks too: with `def cfg : Cfg := { name := "c", extra := costly 5 }`
  and `extra` never read, `costly 5` and its trace do not run (review of
  the data widening, B1; `costly 21` in a function body, with a constant
  argument, behaves the same, while `boom (k + 5)` stays).
- **Where:** `Opt/UnreadFields.lean` (`fixpoint`, `go`, `useValue`,
  `replaceable`, `mayHoldCode`, `externReads`, `alwaysRead`,
  `noTaskValue`, `taint`, `taintValue`, `mayHoldRes`, `usesOnly`,
  `rewrite`, `run`); `PassConfig.lean`: `prunePasses`;
  `Main.lean`: `pipeline` (the roots, the steps of the `Lean` package's
  constants); `Opt/Registry.lean`. Tests `RtUnreadFieldsHook` (translated
  with the pass, equal to native; a callback reads `Lean.manualRoot`, whose
  initializer calls another C++ function and so must not run) and
  `RtUnreadFieldsHookOff` (the same program refused without it), `RtUnreadFieldsCalled` (callbacks read by
  projection, by a match and through a nested field are kept),
  `RtUnreadFieldsCast` (a callback read only through `unsafeCast`),
  `RtUnreadFieldsStream` (a stderr `putStr` that only the runtime calls),
  `RtUnreadFieldsStartup` (the initializers' output and their error, in
  native order), `RtUnreadFieldsExternFn` (an extern as a function value;
  data parameters), `RtUnreadFieldsHandle` (a closure that holds a file
  handle), `RtUnreadFieldsData` (`Expr`s in a field no code reads, left
  out) and `RtUnreadFieldsDataOff` (the same program refused without the
  pass), `RtUnreadFieldsDataRead` (data read by projection, by a match,
  through a nested field and by derived instances only, kept); each with
  `.enable-opts` (the two `Off` tests have `.opts`, which keeps the pass
  off in a run that turns it on for all).
- **Remove only if:** the runtime has the `Lean` package's C++ functions
  (then the callbacks translate as they are), or the pass is unwanted.

### Functions equal up to names are merged (`merge-fns`)

- **What:** After the other passes over the generated functions, each
  function gets a canonical text: its own name `SELF`, its local names
  (parameters, `let`s, match binders, lambda parameters, and those names in
  atoms) renamed `v0`, `v1`, ... in binding order. Of the functions with one
  text, the first stays; each other one keeps its name and signature and
  its body becomes a call of the first (`fn f(a, b) -> T { g(a, b) }`), and
  every call of it in a function body calls the first. Functions whose
  calls changed are looked at again, so callers merge in the next round
  (`List.reverse` at each type once `List.reverseAux` is), up to 8 rounds.
  A function that is a first already but changes later keeps the
  functions merged into it: its new body computes what the old one did.
  A copy calls the function its first ends at, never itself (two functions
  could otherwise call each other). A function that one place calls
  (besides its own recursive calls) takes no part: LLVM inlines such a
  function into its caller, and merged it would be one function that
  several places call, which LLVM does not inline (mergesort's six
  `splitHalf.go` instances, each inlined into its `mergeSort`, cost
  +2.3 % instructions merged); startup code merges anyway: a constant's
  computation (`_init`) and the persist walks (`l2r_persist_`).
- **Why:** With one layout per inductive, instances of a definition at
  different types are often the same code: `List.reverseAux` at `String`,
  `Nat` and a structure (since the heads pass their boxes on,
  [box-and-uniform.md](representations/box-and-uniform.md#a-value-that-only-goes-back-into-boxes-keeps-its-box)),
  `List.lengthTRAux`, the persist walks of function types that differ
  only in phantom domains. CslInitOnly: `.rr` 32.0 -> 30.7 MB (-4.1 %;
  -6.6 % when functions called from one place merge too), for about 1 %
  more translation time (the functions are bucketed by a hash of their
  canonical form, `canonHash`, which hashes types as rendered, `Ty.rt`;
  texts are built only within a bucket).
- **Where:** `Opt/MergeFns.lean`: `mergeFns` (`keep`), `countCalls`,
  `canonHash`, `canonText`, `renameCalls`; hook `PassConfig.rrPasses`
  (last). Test `RtMergeFns`.
- **Remove only if:** the pass is off (the copies stay whole).

### Only the prelude functions that a program uses are kept (`prelude-liveness`)

- **What:** `LoweredProgram.render` writes the generated part of the text
  first (types, functions, trampolines, the string table) and gives it with
  the prelude to `PreludePrune.prune`. `prune` cuts the prelude into its
  top-level items (`items`): a line at column 0, outside a texture, that
  is not blank, a comment or a closing bracket starts an item, and
  attribute lines (`#[`) belong to the item of the line they are attached
  to. An item can go only when it is a function of the form `fn NAME` with
  no attributes other than `#[ffi(import)]` and `#[transform_anchor]`. The
  roots are the prelude's function names that occur as identifiers in the
  generated part and in the items that always stay (the `extern "rust"`
  blocks, the types). From there, `prune` reads the bodies of the kept
  functions until it finds no new name (`namesIn`). It does not read lines
  of the prelude that are a comment as a whole; it reads every other line,
  string literals and comments at the end of a line included. A removed
  function's lines go from its first attribute line to its last line of
  code; the blank and comment lines after it stay. A comment line after the
  prelude gives the number of functions removed. The generated part is the
  same text with and without the pass.
- **Why:** rrc compiles every texture of its input with its own rustc run,
  one after the other, about 25 ms each, also a texture that no code calls
  (Reussir issue 35, a cost), and it lowers every function. The texture
  cache of patch 35-a hides this only while it is full: it is empty in a
  new checkout and after each change of leanrt, lean-runtime, Reussir's
  runtime or the toolchain. Measured on 2026-10-08 (rrc's wall time, quiet
  machine, single runs, empty cache / full cache): a one-line program,
  484 → 75 textures, 14.3 → 3.1 s / 1.8 → 1.1 s; lean-regex's benchmark
  driver, 679 → 327 textures, 27.3 → 17.3 s / 8.4 s both; lean-zip's
  benchmark driver, 622 → 286 textures, 74 → 64 s / 57 s both. The 18
  classic programs built one after the other in a new checkout: rrc 90 →
  69 s in total. For a big program the rest of rrc's time (its MLIR
  passes, LLVM's optimization and code generation) does not change. The
  executables are about 1 MB smaller: each texture is an exported symbol,
  which keeps its `leanrt` code in the link.
- **Where:** `PreludePrune.lean`: `prune`, `items`, `namesIn`;
  `Emit/Program.lean`: `LoweredProgram.render`; `Main.lean`: `pipeline`;
  the switch `PassConfig.prunePrelude`, which `Opt/PreludeLiveness.lean`
  sets. Check `tests/runtime/prelude-liveness-check.sh` (the generated part
  unchanged, at most half of the prelude's textures kept for `RtIO`);
  `tests/runtime/any-probe.sh` turns the pass off: its probe calls prelude
  functions that its host program does not use.
- **Remove only if:** rrc compiles only the textures of the functions that
  code reaches and lowers only those functions; or the pass is off (the
  whole prelude is in the text, as before).

### Constants are boxed once (`boxed-consts`)

- **What:** When a variable bound to a constant is boxed (`boxOf`, the
  box branch of `tryCoerce`), and boxing its type can allocate
  (`boxAllocates`: a `Float`, a `UInt64` or `i64` word, a `[value]`
  struct of one, a value in an `ElemBox`; not an immediate: `UInt8`…
  `UInt32`, `Char`, `Bool`, `Float32`, an enumeration, Lean's `Int8`…
  `Int32`, which Lean erases to `UInt8`…`UInt32`), the box is built
  once and kept in a once-cell, the accessor `l2r_boxed_N` (`boxedConst`;
  one per constant and type, `cafAccessor` without the walk for tasks). A
  constant is a declaration of the program without parameters (a
  constant or closed term cached in a once-cell, or one `cheap-consts`
  recomputes, which cannot trace or panic; not a closed term evaluated
  where it is used, `uncachedConsts`, which a second call would run
  again; not a constant whose value is a literal that boxes as an
  immediate, `constIsImmediate`: `def k : UInt64 := 77` is boxed in line,
  which LLVM folds, where a once-cell read is a load, a test and a copy)
  or a `UInt64`/`USize` literal from 2^63; `lowerCode` records the
  variables bound to one (`closedLetValue`, `LowerState.closedLets`). Not
  in the body of a declaration without parameters (`inConstBody`, set by
  `lowerDecl`): that body runs once, so a once-cell there saves no
  allocation and costs a slot and two functions per constant (a table
  constant of 600 distinct big `UInt64` literals went from 1159 to 2359
  functions).
- **Why:** Native Lean does the same (`ExplicitBoxing`,
  `isExpensiveConstantValueBoxing`: an auxiliary constant
  `_boxed_const_N`). The default of `a[i]!` is a constant
  (`instInhabitedFloat`, a structure's `Inhabited` instance); boxed at
  every read, an `Array Float` read allocated a 16-byte cell per read
  (adversarial review of the dependent-type branch, finding 2: 4 × 40000
  reads, 160046 allocations, natively 11079 with its startup's 11000; with
  the pass 47). A named constant or closed term, or a `UInt64` literal
  from 2^63, pushed or stored n times is one cell, as natively. A `Float`
  literal written in a loop (`a.push 0.25`) is no constant: it is
  computed there, natively too (Lean extracts no closed term for it), and
  boxed at each push on both sides. A constant is pure, so one box does
  as well as a new one; two boxings of one constant are one cell
  (`ptrEq`), as natively within one module (native Lean caches its boxed
  constants per module, `cacheAuxDecl`; lean2rr has one cell per constant
  for the whole program; plan §9, identity). Test `RtDepFloatArrayAlloc` (`.alloc`: `get!`,
  `getD`, `modify`, `set!`, a structure's default, constants and literals
  pushed, at two sizes). A closed term
  evaluated where it is used (`uncachedConsts`) is left out: the box's
  call ran it a second time, and a trace in it printed twice (test
  `RtDepBoxedClosedOnce`).
- **Where:** `Lower/Conv.lean`: `boxOf`, `boxedConst`; `Lower/Code.lean`:
  `closedLetValue`, `constIsImmediate`, the `let` loop of `lowerCode`,
  `lowerDecl`; `LowerBase.lean`: `boxAllocates`, `LowerState.closedLets`,
  `boxedConstFns`, `inConstBody`, `LowerCtx.boxedConsts`;
  `Opt/BoxedConsts.lean`.
- **Remove only if:** the pass is off (each box of a constant is built
  where it is used).

### Float literals are folded to their bits (`float-lits`)

- **What:** A call `Float.ofScientific m s e`, `Float.ofNat n` (or the
  `Float32` ones) on literal arguments is evaluated by lean2rr, with the
  same Lean functions, and replaced by `Float.ofBits` of the bit pattern, a
  total conversion of a literal. Calls with an exponent above 2000 or a
  mantissa (or `Float.ofNat` argument) of more than 4096 bits are left to
  run. An argument is a literal when its variable is one of these:
  - bound by a `let` to a literal (`10`, `Bool.true`);
  - the discriminant of a `cases` on `Bool`, inside an alternative that
    fixes its value: `Bool.true`, `Bool.false`, or a `.default`
    alternative when the other alternatives name exactly one constructor
    (`boolOfAlt?`; Lean's simp leaves no such `.default` today, because
    two equal alternatives remove the `cases`);
  - a parameter of a join point, when every jump to the join point passes
    the same literal at that parameter (`JumpLits`).

  Example. In `match b with | true => x * 2.5 | false => x * 3e2`, the
  literal `2.5` is `Float.ofScientific 25 true 1`. Inside the alternative
  `true` of `cases b`, Lean's simp replaces the constructor `Bool.true` by
  `b` (`Simp.simpCtorDiscr?`: a constructor equal to a discriminant there
  becomes the discriminant). So the mono code has
  `Float.ofScientific 25 b 1`. The pass knows that `b` is `true` in this
  alternative, and folds the call. In the alternative `false`, `3e2`
  (`Float.ofScientific 3 false 2`) becomes `Float.ofScientific 3 b 2` in
  the same way. If `Simp.simpJpCases?` then moves such an alternative into
  a join point of its own, `b` becomes that join point's parameter. In
  `if x && y then a + 0.5 else a * 2e3`, the `else` code is a join point.
  One jump passes `x` from the alternative `false` of `cases x`, the other
  passes `y` from the alternative `false` of `cases y`. Both are `false`,
  so the parameter is `false`, and `2e3` folds.
- **Why:** These are Lean functions, not C: the slow path goes through
  `Float.Model` with bignum arithmetic. lean2rr is compiled from the same
  `Init` code, so the bits are Lean's, subnormals and rounding included
  (adv3 CN3-01, d3e80aa; test `RtFloatLits`). After simp's replacement, a
  literal is no longer a closed term, so it is computed at each iteration
  of a loop (natively too), and a slow-path literal allocates there. The
  discriminant and join point rules fold these calls (test
  `RtFloatLitDiscr`; its `.alloc` file checks that lean2rr's allocations
  do not grow with N). They are sound: an alternative runs only when the discriminant
  has that value. A join point's body runs only after a jump to it, and
  every jump is in its continuation: a join point is not recursive, and a
  jump does not leave its function (LCNF's checker).
  Simp replaces only constructor applications. The `Nat` arguments of
  float literals are raw literals (`.lit`), not constructors, and mono code
  has no `cases` on `Nat`. So simp hides no `Nat` literal argument, except
  an explicit `Nat.zero` inside the alternative `Nat.zero` of a base-phase
  `cases` (the call then runs, with the same result).
  Not folded: a flag that is a parameter of a function, for example in a
  specialization of `List.map` for a closure that captured `b`
  (`if b then xs.map (· + 0.5) else …`). That call runs, as natively.
- **Where:** `Opt/FloatLits.lean`: `foldFloatLitsCore`, `boolOfAlt?`,
  `JumpLits`, `floatLitBits?`, `floatLitMaxExp`, `floatLitMaxBits`; hook
  `PassConfig.monoPasses`.
- **Remove only if:** the pass is off (the program computes the same bits
  at run time).

### Cheap constants are recomputed (`cheap-consts`)

- **What:** A constant whose code only builds unboxed values from small
  literals, constructors and total scalar conversions (`UInt32.ofNat 0`,
  `Float.ofBits`, or another such constant, up to 8 deep) is recomputed at
  every use instead of read from a once-cell. Every `Nat`/`Int` it builds
  must be small (one word): the pass tracks the known values of the
  `Nat`/`Int` variables it binds and accepts `Nat.succ` below 2^63 and
  `Int.ofNat`/`Int.negSucc` of `int32` values only.
- **Why:** It cannot panic, trace or allocate, so the change is
  unobservable, and a once-cell read costs more (a load, a test and the
  count's increment, startup/constants.md; the numbers that follow are
  from before a read became one load): deriv 1.20x → 1.11x
  native (a570011); `instInhabitedUInt32` read on every `get!` of an
  `Array UInt32`: qsort 1.03x → 0.89x (8c58721). A big `Nat`/`Int` is a
  heap number: `def K : Int := 3000000000` recomputed was allocated at
  every use, 7-8x native in a loop (RV8N-01; test `RtNatConst` with
  `nat-alloc-check.sh`).
- **Where:** `Opt/CheapConsts.lean`: `isCheapConst` (`smallCtor`), `isUnboxedTy`; hook
  `LowerHooks.recomputeConst`; `Lower/Code.lean`: `lowerDecl`.
- **Remove only if:** the pass is off (every constant outside closed-term
  chains is then cached).

### Structure arguments and results are spread into their fields (`flatten-structs`)

- **What:** A worker/wrapper transformation on the mono code after Stage 3
  (`Opt/Flatten.lean`). It splits:
  - a parameter of a join point, or of a declaration that calls itself (and
    is in no larger call cycle), whose type is a structure: one parameter
    per relevant field, at the field's precise type (`Nat`, not the
    `LAny` of the structure's layout), nested structures too (`MProd Nat
    (MProd Nat Nat)` gives three parameters). Join points also take
    two-constructor values (a `Bool` tag and the fields of both
    constructors). A parameter of a declaration that does not call itself
    is split only where it is only read and some caller passes it a value
    whose fields are known (`prunePassed`): lean-zip's Adler-32 fold passes
    its split state to `updateByte`, which Lean does not inline;
  - a result whose type is a structure or a type of two constructors
    (`EST.Out`, `Except`, `Option`, `ForInStep`), nested in each other:
    the declaration returns the variables as a `[value]` tuple
    (`L2RFlat.Tuple<k>`, a structure the pass adds to the environment, which
    `lowerType` lowers to `tupleType` of its fields' types). The fields of
    the constructor a value does not have are placeholders (`◾`); two
    constructors with the same field types (`ForInStep`) share them.

  A value's fields are known where it is a constructor application of the
  same declaration, a split parameter or a field of one, a value matched
  by an enclosing `cases` (its alternative's parameters), a constant that
  only builds one constructor (`pure 0`, extracted as a closed term), or
  the result of a call that returns a tuple (a value the callee built at
  every call, unless it may return an existing object there). A constructor application
  used only through such places is not built. A use of a split value
  "whole" (stored, passed to another function, returned unsplit) keeps
  that level of a join point's or a declaration's parameter whole, except
  at the exit (no self-call reachable) of a self-recursive declaration
  whose self-calls are all tail calls, when every self-call passes a value
  built in that step: the loop built one value per step, and now builds
  one there when it ends. Such a declaration keeps a copy of its body in
  the wrapper (`AState.peel`), which runs the first step on the value as
  it came, so a loop that ends at once returns it unchanged; every other
  declaration calls it through the wrapper. A whole use of a call's
  result rebuilds it there from the tuple (the callee no longer builds
  it). A join point's parameter is never rebuilt: rebuilding one gained
  nothing measurable on the benchmark programs (Sieve, MonadicInterp,
  Unionfind, Liasolver, Mergesort, HigherOrder, lean-zip: the same
  instructions without it), and every review round found a new copy in
  that logic.

  A level that receives an object the program shares (a matched value, a
  constant, a declaration's parameter, or such a level in turn:
  `AState.existing`; a parameter counts where some self-call passes it on
  unchanged) is never rebuilt either, nor copied when a level above it is
  rebuilt: Unionfind's `findEntryAux`
  returns an array element it matched, which a caller stores again;
  rebuilding it there allocated a copy at every step of the path
  compression instead of sharing the element. A value whose object is
  inspected (`ptrAddrUnsafe`, `dbgTraceIfShared`, `isExclusiveUnsafe`) is
  never rebuilt. The
  analysis is a greatest fixed point over the whole program (`analyze`,
  constraining again only the declarations a change concerns):
  shapes start from the largest (`maxShape`: 8 levels, 16 variables) and
  shrink where a value's fields are not known or a whole use is not
  allowed. A result level stays whole when some caller uses it whole and
  no other declaration reads it field by field, or when the declaration
  may return a shared object there, or when a level above it is used whole
  and a shared object arrives there (`pruneUnread`; a declaration that no
  code of the program mentions, such as Lean's original of a `_redArg`
  declaration, does not count as a user); a declaration reached
  through its wrapper (a function value, a caller the pass leaves alone, a
  peeled loop: `wrapperUsers`) counts as used whole at every level (the
  review of the pass found copies of a matched pair per call through a
  function value, a join point at a loop's exit rebuilding the caller's
  pair, a `dbgTraceIfShared` that a rebuilt copy silenced, and in a second
  round a shared object one level below a rebuilt one: test
  `RtFlattenShared`). A loop's parameter also counts as shared at a level
  where some other declaration passes it an object that exists there (a
  value whose fields are not known there, a matched value, a constant, a
  value built anyway: `AState.entryExisting`), and at every level where
  callers reach it through the wrapper (a function value, a caller the
  pass leaves alone: `analyze`; a peeled loop, whose wrapper runs the
  first step on the caller's value: `allowedWhole`). A run with no step
  returns that object, so a result level it reaches stays whole where a
  caller uses it whole. A constructor application that stays and a call's
  result used whole (`AState.builtCalls`) are objects that exist too: a
  join point or a result they reach does not build them again.

  Each value is built at most once per run of the code that binds it. The
  rewrite remembers every value it builds along the scope (`Env.mats`, by
  the value's constructors and leaves: a record and a projection of its
  inner record share the inner one). Two rebuilds of one value (or of a
  level inside it) of which a join point's body holds one may both run, so
  that level stays whole (`constrainDecl`'s sites, `AState.sites`): for a
  parameter, the slot is cut there; for a call's result, the declaration
  calls the wrapper and keeps the result whole (`AState.wholeCalls`), and
  the arguments of that call count as whole uses (the wrapper takes them
  whole; the callee's parameters then get existing objects). A
  two-constructor value built behind a join on its tag is matched as the
  built object, so the alternative's fields are the ones built there. A
  fresh value (a constructor application the pass leaves unbuilt, a call's
  result) that goes split both to another declaration's worker, which may
  return it as it came in a tuple a caller rebuilds, and to a second place
  (a self-call, a jump, a return, another call) counts as built: one
  object, which the callee gets as an existing one (`constrainDecl`'s flow
  sites, `AState.flowSites`). A rebuild copies no level below it that is
  not fresh. These rebuild
  checks run in the round after each fixed point (`AState.checkSites`),
  on shapes that no longer shrink. A loop peeled while its parameter was
  split keeps no first step when the parameter ends up whole.

  The review of the pass found, in its third round, a loop that ran no
  step returning the caller's record, which a caller that stored it built
  again from the tuple (one record per call), and a call's result stored
  and also given to a split join point parameter that was stored again
  (one more pair per step: test `RtFlattenCopies`); in its fourth round
  the same copy through a function value and in a peeled loop's first
  step (`RtFlattenFnValue`, `RtFlattenPeelFirst`, and the
  `dbgTraceIfShared` they silenced: `RtFlattenTrace`), a call's result
  used whole in a join point's body and at the jump to it
  (`RtFlattenOrder`), and values built twice: a record and its inner
  record, a loop's state in a join point's body and at its argument
  (`RtFlattenNested`); in its fifth round a matched payload built again
  after its value was built behind a tag join (`RtFlattenSumPayload`), and
  the arguments of a call through the wrapper constrained as passed field
  by field (`RtFlattenWrapArgs`, `RtFlattenSelfWrap`); in its sixth round a
  fresh value given to another loop's worker and also to a second place,
  built twice (`RtFlattenEscape`). Every
  saturated call in the program calls the worker (`f._l2r_flat`), with the
  arguments' fields (projected when they are not known); the wrapper keeps
  the declaration's name and signature for function values and entry
  points. `L2R_FLATTEN_DEBUG=NAME` prints the decisions about the
  declarations whose names contain NAME.
- **Why:** Rule 1 gives every datatype one layout with type parameters
  boxed, so a loop's state and a monad's result were boxed and unboxed at
  every step, and records allocated per call: the classic Sieve took 166
  instructions per step of its six-variable loop instead of dev's 77
  (+61 % against dev), MonadicInterp +57 %, Unionfind +42 % (performance
  review of the dependent-type work, item 1). Measured with cachegrind
  (instructions) against the same build with the pass off, on dev 393c739
  (one run): Sieve −53.9 %, MonadicInterp −51.0 %, Unionfind −51.3 %; on
  the dependent-type branch before (mean of two runs): HigherOrder
  −4.2 %, Liasolver −8.0 %, Mergesort −7.3 %; lean-zip compress −4.8 %,
  decompress −11.0 % (its Adler-32 state passed split to `updateByte`).
- **Where:** `Opt/Flatten.lean`: `Shape`, `maxShape`, `indInfo?`,
  `placeholderOk`, `collectDecl` (uses, aliases of matched values,
  `constCtor?`), `analyze`, `constrainDecl`, `flowInto`, `allowedWhole`,
  `freshFed`, `isExisting`, `wholeRoot`, `constrainDecl` (rebuild
  sites), `pruneUnread`, `resourceExcluded`; the rewrite `xform`,
  `explode`, `materialize` (`Env.mats`, `VVal.key`), `callWorker`, `run` (workers, wrappers,
  peeled wrappers). `LowerBase.lean`: `flatTupleName`, `lowerType` (the
  tuple types); `Lower/Values.lean`: `lowerLetValue` (tuple constructor and
  projections); `Opt/Flatten.lean`'s `holdsResource` follows
  `Lower/Borrow.lean`'s `mayHoldResource` (memoized); hook `PassConfig.monoPassesCore`
  (run by `Main.lean` after `monoPasses`; `--emit opt` prints the result).
  Tests `RtFlattenLoops`, `RtFlattenResults`, `RtFlattenSums`,
  `RtFlattenAlloc` (with `RtFlattenAlloc.alloc`), `RtFlattenShared` (with
  `RtFlattenShared.alloc`), `RtFlattenCopies`, `RtFlattenFnValue`,
  `RtFlattenPeelFirst`, `RtFlattenOrder`, `RtFlattenNested`,
  `RtFlattenSumPayload`, `RtFlattenWrapArgs`, `RtFlattenSelfWrap`,
  `RtFlattenEscape` (each with its `.alloc`), `RtFlattenTrace`.
- **Remove only if:** the pass is off (the structures are then built at
  every step, with boxed fields, as rule 1 lays them out).

## Required parts that look like optimizations

Listed in `Opt/Registry.lean` (`required`); `--disable-opt` rejects them.

| Part | Entry |
|---|---|
| `startup-chunks` | [startup/order.md](startup/order.md#the-startup-chain-is-cut-into-chunks-of-128-steps) |
| `loop-state-machines` | [control-flow/state-machines.md](control-flow/state-machines.md#a-loop-through-outlined-join-points-is-one-state-machine) |
| `closed-chains` | [startup/constants.md](startup/constants.md#a-closed-term-used-once-by-another-constant-is-not-cached) |
| `stage3-types` | [types/type-recovery.md](types/type-recovery.md) |
| `outline` | [control-flow/outline.md](control-flow/outline.md) |
| `wildcard-sinks` | [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#issue-22-cost-a-wildcard-arm-over-a-wide-enum-costs-n3-code) |
| `inline-anchors` | [reussir-workarounds/build-time.md](reussir-workarounds/build-time.md#issue-20-cost-the-inliner-multiplies-conversion-code) |

Stage 2's edits of Lean's pass lists (two passes replaced, `extractClosed`
moved to the end, `inferVisibility` and `toImpure` not run) are required
too: [types/lean-passes.md](types/lean-passes.md).

## Hooks

How a pass plugs in, and what installation order means for each kind of
hook, is in `Opt/Registry.lean`'s module comment and `PassConfig.lean`.
A pass that leaves declarations out runs before Stage 3
(`PassConfig.prunePasses`): it gets the instance keys, the roots and the
`Lean` package's `initialize` constants with their initializers, and a
startup step whose initializer it leaves out does not run
(`Main.pipeline`).
State scoped to the code being lowered (passed down into nested code, not
back up or across sibling branches) goes in `CodeCtx.ext`
(`CodeCtx.getExt?`/`setExt`; `Opt/LazyFields.lean`'s `LazyFieldsState`);
whole-program state in `LowerState.ext` (`Opt/FreshRebuild.lean`'s
`freshDeclsCached`).
