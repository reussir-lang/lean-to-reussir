# Externs of the program: Lean code, or a binding to an `@[export]`

lean2rr compiles Lean code, and Lean's runtime library is the only native
code it uses (the owner's decision of 2026-10-03: "let's just target lean
only code for now, with runtime library as the only exception"). The rule
is plan [§5.8](../../translation-plan.md#58-externs-and-runtime-calls),
"Lean-only target", "Externs of Lean's library" and "Externs of the
program". The code is ported from the parked branch `lean-externs`
(fb3bb77, reviewed in rv8/ext rounds 1-4, findings RV8E-01..11) and
changed to the rule: the precedence of a prelude function or of linked C
over the Lean body is gone, as is `--external-symbols`; and, by the
owner's decision of 2026-10-04, an extern of the program is never bound to
Lean's runtime (its binding to an extern of Lean's library, with its
lowering at the library extern's type arguments, was removed).

### Lean's library is decided by the declaration's module name

- **What:** An extern is Lean's library's when the module declaring it is
  named `Init.*`, `Std.*`, `Lean.*`, `Lake.*` or `L2RShim.*`
  (`isToolchainDecl`, `isToolchainModule`). Those externs are served by
  the runtime, as before this rule; every other extern is the program's
  (its own modules', or a package's it requires).
- **Why:** The name alone would be fooled by a program module named
  `Lean.Foo`; it is not, because `Env.loadEnvironment` rejects any module
  so named that is not the very file of the toolchain's library (or of
  the shim directory) (plan §10, "Module names"; RV6T-06, tests/env). So
  the name is the robust test, and needs no file system access per
  declaration.
- **Where:** `Mono.lean`: `isToolchainDecl`; `CompileRecord.lean`:
  `isToolchainModule`; `Env.lean`: `loadEnvironment`.
- **Remove only if:** the loader stops checking module files.

### An extern of the program takes the first route that applies

- **What:** `computeExternRoute` (cached by `externRoute`) gives each
  extern of the program one `ExternRoute`: `implementedBy g` (Stage 1
  redirects calls to `g`, `redirectTarget`); `export g` (its C symbol is
  `g`'s `@[export]`, the binding tests pass: the extern becomes a
  `noinline` declaration calling `g`, `exportForwardDecl`); `body` (its
  Lean definition, also when its C symbol is that of an extern of Lean's
  library); `refused why`. `baseDeclFor?` returns the compiled declaration
  (in `MonoState.extraBase`) for `body` and `export`, the extern
  declaration otherwise.
- **Why:** Natively the call is linked to the function named by the C
  symbol; when that is the program's own `@[export]` definition, lean2rr
  calls it too, otherwise it runs the extern's Lean definition, its
  specification. An extern of the program is never bound to Lean's
  runtime (the owner's decision of 2026-10-04): what runs is the program's
  own code. The rule is shared with another Lean translator built on the
  same runtime.
- **Where:** `Mono.lean`: `ExternRoute`, `computeExternRoute`,
  `externRoute`, `redirectTarget`, `baseDeclFor?`; `Main.lean`: the
  routes to the lowering.
- **Remove only if:** never (the rule).

### A binding needs an instance of the definition's type and one compiled signature

- **What:** `bindingFailure?` (an extern of the program and the
  `@[export]` definition of its C symbol), a rule shared with another Lean
  translator built on the same runtime: (1) the extern's type is an
  instance of the definition's (`typeInstance`, at transparency `all`):
  the definition's universe parameters become fresh level metavariables
  (`{α : Type}` binds to `{α : Type u}`, RV8E-09), and the types are
  compared (`typeMatches`): parameter types definitionally, the result
  type definitionally or after Lean's mono identifications applied to the
  *definition's* result, one after another (`resultInstance`,
  `monoHeadStep`, the step of `monoHead`): a trivial structure is its
  single relevant field, `Decidable p` is `Bool`. The definition's type
  parameters need no instantiating: they are erased parameters of its C
  function, which no extern's call passes, so test 2 fails for them.
  (2) One compiled signature, from Lean's impure-phase signatures
  (`getImpureSignature?`, `compiledSig?`): the extern's C call passes its
  parameters but the IO world and erased ones; the `@[export]` function
  takes its erased ones too; the types must be equal (an `obj` does not
  meet a `tobj`), the results equal, the borrow marks equal except owned
  on the extern where the definition borrows. The failure message names
  the test: "the type" (with the two types), "the compiled signature"
  (with the two signatures), "borrowed on the extern, owned on the
  target".
- **Why:** The second test is the condition under which the native linked
  call is defined; an `@&` on the extern where the definition takes the
  argument owned has the definition release a reference the caller holds
  (natively a double free), an owned argument at a borrowed parameter only
  leaks. The identifications are sound on the result (the definition's
  value meets the stronger invariant: `mk1 : Nat → Nat` of an `@[export]`
  returning `{m : Nat // m > 0}`) and unsound on a parameter (a `Nat`
  passed for a `{n : Nat // n > 0}` could be `0`; a `UInt32` for a `Char`,
  `0xD800`), so they apply to the result only. Tests `RtExternBind`
  (`triple`, `mk1` bind; `tripleB`, `pos1` run their bodies),
  `RtExternRefused` (`tripleS`, `myPos`), `RtCastExtern`, `RtExternStub`.
- **Where:** `Mono.lean`: `bindingFailure?`, `typeInstance`,
  `typeMatches`, `resultInstance`, `monoHeadStep`, `compiledSig?`,
  `renderCompiledSig`, `stripMData`.
- **Remove only if:** never.

### An `@[export]` binding calls the definition through a noinline declaration

- **What:** For `ExternRoute.export g`, the extern's declaration is
  `exportForwardDecl`: its parameters (from its LCNF type), a call of `g`
  on them, `noinline`, compiled with `recompilePasses`. Calls of the extern
  are not renamed.
- **Why:** Renamed to `g` in Stage 1 (as before), its calls on literals
  were inlined and folded by Stage 2's passes, which natively, a C call,
  never happens: `@[extern "s"] opaque myShl` bound to `@[export s] def
  shlImpl (a b : Nat) := a <<< b` stopped lean2rr with "Nat.shiftl exponent
  is too big" on a call in a branch that never runs (review REB-01, the
  export form of RV8E-11; test `RtExternFold`).
- **Where:** `Mono.lean`: `exportForwardDecl`, `compileExportForward`,
  `computeExternRoute`, `baseDeclFor?`, `redirectTarget`.
- **Remove only if:** Stage 2 stops folding calls on literals.

### A symbol of Lean's runtime library runs the extern's definition, or is refused naming Lean's declaration

- **What:** An extern of the program whose C symbol is that of an extern
  of Lean's library is not bound to it: its Lean definition runs; without
  one it is refused, the message naming the library's declaration(s) of
  that symbol ("call `Array.size` instead", from `toolchainExternSyms`),
  or, for a private declaration (module system), saying that a program
  can call it only from a `module` file that imports it with `import all
  M`, by its user-facing name (`privateToUserName?`; reviews REB-10,
  REB-12, test `RtExternPrivate`). An `@[export]` of Lean's library (Init's
  `String.Internal.dropImpl` exports `lean_string_drop`) counts as Lean's
  library too: no extern of the program is bound to it, and a refusal names
  it, a private one as above (`IO.eprintlnAux`'s `lean_io_eprintln`; reviews
  REB-14, REB-18; `isToolchainDecl` in `computeExternRoute`,
  `libraryDeclAdvice`). When no imported module declares the
  symbol but lean2rr's runtime implements it, the message names the
  module of Lean's library that declares it, to import if that
  declaration is public (`librarySourceExternSyms`, below). lean2rr's note
  marks an extern of the program running its definition where natively
  Lean's runtime function runs "(natively Lean's runtime function)", so a
  stub's difference shows at build time.
- **Why:** The owner's decision of 2026-10-04, shared with the other
  translator: the program's own code runs, and the runtime library serves
  Lean's own declarations only. Until then such an extern was bound to the
  runtime's function under a type-instance test (`sizeNat (a : @& Array
  Nat)` as `Array.size` at `Nat`), with a lowering at the library extern's
  type arguments; that code is gone. Tests `RtExternBind`, `RtExternNames`
  (definitions run), `RtExternRefused`, `RtExternOpaqueRedecl`,
  `RtExternOpaqueRepr` (refused).
- **Where:** `Mono.lean`: `computeExternRoute`, `libraryDeclAdvice`,
  `toolchainExternSyms`, `externBodiesOfRuntime`; `Main.lean`: `pipeline`
  (the note).
- **Remove only if:** the decision changes.

### The Lean definition is compiled as Lean compiles one, and noinline

- **What:** `externBodyDecl` repeats `ToDecl.toDecl`'s value path for the
  extern (which `toDecl` turns into an extern declaration): the
  `_unsafe_rec` copy when there is one (recursive, `partial`), each
  `X._unsafe_rec` renamed to `X` and `@[csimp]` replacements applied
  (`replaceLogicConstants`), `macro_inline`, matchers, then `toLCNF`, and
  marks it `noinline`; `compileExternBody` runs `recompilePasses` on it
  (Lean's base passes without inlining persisted bodies or specializing).
  An `opaque` (whose value only shows its type is inhabited), an axiom or
  any other kind has none.
- **Why:** "As if the attribute weren't there". `noinline`: RV8E-11 (the
  body folded on literals in Stage 2). The `@[csimp]` replacement follows
  Lean: without it a body calling a function a `@[csimp]` maps would call
  the slow one. Tests `RtExternBody`, `RtExternRec`, `RtExternCsimp`.
- **Where:** `Mono.lean`: `externBodyDecl`, `compileExternBody`,
  `recompilePasses`.
- **Remove only if:** never; `noinline` only with RV8E-11's fold gone.

### The Lean definition's closed terms are extracted as Lean would

- **What:** `extractLikeLean` extracts the closed terms of a declaration
  whose source is an extern (the Lean definition of an extern of the
  program), as it does for a declaration Lean compiled to no IR.
- **Why:** Lean's record of the module knows the extern as an IR extern
  declaration without a body, which would read as "Lean extracted
  nothing here": the definition's literals and constant data were then
  rebuilt at every call (`greet`'s `"hello, "` in `RtExternBody`). Lean
  compiling the definition without the attribute would extract them.
- **Where:** `Pipeline.lean`: `extractLikeLean`.
- **Remove only if:** never (cost only: without it, closed terms are
  recomputed per call).

### Refusals are reported at translation, with the reason

- **What:** A refused extern stays an extern declaration; each call of it
  that reaches the lowering (direct, partial application, function value:
  all get their target from `calleeOf`) is recorded
  (`noteRefusedExtern`), it gets no glue nor any of the lowering's
  shortcuts (`ptrAddrUnsafe`, references), only a call of
  `l2r_refused_<declaration>`, which nothing defines (`refusedExternCall`;
  under `L2R_ALLOW_MISSING_EXTERNS` the program is generated but does not
  build, rather than calling the runtime's function of the symbol: review
  REB-11), and
  `lowerProgram` rejects the program, listing each one with its module,
  its C symbol (or "inline C") and the reason, and saying that lean2rr
  supports Lean code plus Lean's runtime library only. Externs of Lean's
  library whose prelude function is missing are listed in the same
  message, as runtime gaps. `L2R_ALLOW_MISSING_EXTERNS=1` only warns.
  With the optimization `unread-fields` (off by default), an extern that
  only values in fields no kept code reads reach (Batteries' linters and
  attributes, the `Expr` of a derived `ToExpr` instance) is left out before
  Stage 3, with them, and so is not reported ([../optional-passes.md](../optional-passes.md#values-in-unread-fields-are-left-out-unread-fields)).
- **Why:** The owner wants refusal by lean2rr, not by rrc's "unknown
  function" (b2ced69 on `lean-externs` for the library's; RV8E-04 for the
  reason).
- **Where:** `Lower/Decls.lean`: `noteRefusedExtern`, `calleeOf`;
  `Lower/ExternCall.lean`: `refusedExternCall`, `lowerExternCall`;
  `Lower/Values.lean`: the extern call; `Emit/Program.lean`:
  `lowerProgram`. Tests `RtExternRefused`, `RtExternOpaqueRepr`,
  `RtExternOpaqueRedecl`, `RtExternPrivate`, `RtCastExtern` (`.refused`);
  `tests/runtime/allow-missing-check.sh` (REB-11's `l2r_refused_` calls
  under `L2R_ALLOW_MISSING_EXTERNS`, review REB-15).
- **Remove only if:** never.

### Stage 3 does not take a body instance for an extern

- **What:** `MonoRetype.externResultType?` skips a callee with code
  (`MRetypeState.codeDecls`).
- **Why:** It reads the extern's types from the persisted base
  declaration, which for an extern that runs its Lean definition is still
  the extern. Stage 3 used to redirect such calls to a new extern
  instance (until simplicity finding 2 of the rule 1 review, it built
  one): a body instance would have become a call of the C symbol. The
  optimization `uniform-updates` (deleted with the one array type) did it
  to `Array.restart` of test `RtExternUniform` (an `Array` extern of the
  program whose body uses no parameter, so Lean's `reduceArity` leaves
  calls on the instance): lean2rr then reported its C symbol as a missing
  extern of Lean's library. (rv8/ext round 1 found no program reaching
  the redirection.) `lowerProgram` labels an extern of the program that
  still reaches its missing-extern list an internal error.
- **Where:** `MonoRetype.lean`: `externResultType?`; `Emit/Program.lean`:
  `lowerProgram`.
- **Remove only if:** never.

### The prelude's functions are its declarations, not its words

- **What:** `preludeFnDecls` reads the names of the prelude's lines
  `fn NAME`/`pub fn NAME` outside its textures (`[{ … }]`, delimiters
  counted outside `//` comments; unbalanced textures are an error). Stage
  1 (whether a refused extern's symbol is a function of lean2rr's runtime)
  and the lowering (which symbols are missing) use this one set.
- **Why:** The textual set before took every word after `fn ` (a texture's
  `gettid`, comment words), RV8E-01, RV8E-07.
- **Where:** `Mono.lean`: `preludeFnDecls`, `preludeFnDeclsM`;
  `Emit/Program.lean`: `lowerProgram`.
- **Remove only if:** the prelude gets a machine-readable index.

### lean2rr notes which externs run their Lean definition

- **What:** After Stage 1 lean2rr prints on its own stderr (the build's
  output, not the program's) "note: N extern(s) of the program run their
  Lean definition, not their C code", one line per extern with its
  symbol, marked " (natively Lean's runtime function)" when its symbol is
  that of an extern of Lean's library (imported, or found by the source
  scan for a symbol the prelude defines) and " (natively Lean's library
  function)" when it is an `@[export]` of Lean's library
  (`nativeLibraryFunction?`, `MonoState.externBodiesOfRuntime`; reviews
  REB-13, REB-14), so a stub's difference from native shows at build
  time.
  Of those, an extern whose C symbol is another declaration's `@[export]`
  whose binding's tests fail also gets "warning: X runs its Lean
  definition, where native Lean calls the function its C symbol is linked
  to: …", naming the definition and each failed test (not for a symbol of
  Lean's runtime library, to which an extern of the program is never
  bound). For a refused extern, the hint naming the module of Lean's
  library to import is given only for a symbol that an extern of Lean's
  library declares: `librarySourceExternSyms` reads the `@[extern …]`
  attributes, with their modules, from the toolchain's library source
  (`src/lean/{Init,Std,Lean}` and `src/lean/lake/Lake`, imported or not),
  so a helper of lean2rr's prelude (`l2r_nat_repr`, `lean_array_uswap`),
  which no Lean module declares, gets none (review REB-07). The scan
  (about 2,600 files) runs once, and only for a refused extern whose
  symbol is a prelude function no imported declaration has: `do`
  evaluates every `(← …)` of a condition before it, with no `&&` short
  circuit, so it is nested in its own `if` (REB-08). It does not follow
  symbolic links to directories (REB-09). Without the toolchain's source
  there is no hint.
- **Why:** A stub body (natively the C does the work) otherwise shows only
  at run time (RV8E-03); and where the C symbol is the program's own
  `@[export]`, a failed binding is the reason the definition runs, which
  the build should say (review REB-02, REB-03). Tests' `.l2r-log` files
  check these lines (`RtExternStub`).
- **Where:** `Main.lean`: `pipeline`; `Mono.lean`: `externBodies`,
  `externBodiesOfRuntime`, `nativeLibraryFunction?`,
  `externBindingWarnings`, `computeExternRoute`, `externLabel`,
  `librarySourceExternSyms`, `externAttrStrings`.
- **Remove only if:** the note is unwanted.

### Tests give the native build the C code, and check routes and refusals

- **What:** `tests/runtime/run.sh`: `NAME.ffi.c` is linked into the
  native build only (the C side of the test's own externs, which lean2rr
  never sees); `NAME.refused` makes lean2rr's refusal the expected
  outcome (each line must be in its output, or with `! ` must not;
  natively only `lean -c` runs);
  `NAME.l2r-log` lists lines lean2rr's build output must contain, or with
  `! ` must not (the note above: which externs run their definition).
- **Why:** Natively a program extern needs its C; the routes are not
  visible in the program's output when the C and the body agree.
- **Where:** `tests/runtime/run.sh`; `RtExtern*`.
- **Remove only if:** n/a.
