import Lean
import LeanToReussir.PassConfig

/-!
# Unread constants without effects left out of the startup (optimization `unread-consts`)

Natively a module's initializer evaluates every constant of the module,
used or not (translation plan §5.12; docs/implementation/startup/order.md,
"Every constant of the program is a root"), and lean2rr's startup chain
does the same: one step per constant. Most of these constants are never
read and their evaluation shows nothing: the instances a `deriving` clause
makes, the expression trees that `bv_decide` stores as constants (a sixth
of the program text of a program that uses lean-zip; its LRAT
certificates, one string literal each, have no function at all with
`literal-consts`), the parser descriptors of a `syntax` command.

The pass runs on Stage 1's result, before Stage 2. It leaves out the startup
step of a constant when both hold:
- *unread*: no code that the program keeps names the constant: not the code
  that `main`, the error printer or another startup step (an `initialize`
  action, an init function, a constant that stays) reaches, through any
  reference (a call, a closure, a constant read);
- *without effects*: its evaluation cannot show (`blocker?`). Its code and
  the code of everything it calls (transitively) only binds literals,
  builds constructors and closures, projects fields, matches, jumps and
  returns, and calls declarations and the externs of `pureExterns`. A
  recursion among the instances it runs goes only through definitions of
  Lean's toolchain that Lean checked (structural or well-founded recursion)
  or through their `unsafe` implementations (`Array.foldlMUnsafe`), never a
  `partial` definition or the program's own recursion, so the evaluation
  ends (`recursionEnds`); no function value is applied, so a closure (which
  can do anything) is only built; no other extern is called (`panic`,
  `dbg_trace`, IO, tasks, references, thunks are all externs); none of the
  program's own `unsafe` code runs, except the computed-field
  implementations Lean makes (`_override`; the toolchain's `unsafe` code is
  trusted, as everywhere in lean2rr); no instance it runs comes from a
  declaration that rests on a claim Lean did not check: `sorry` or an
  axiom other than `propext`, `Quot.sound` and `Classical.choice`, also in
  a `@[csimp]` theorem or the `_unsafe_rec` code of a `partial` definition,
  or an `@[implemented_by]` of the program (`axiomTaints`: a false claim
  can reach an `unreach` or make a library recursion run for ever); no
  `initialize` constant is read; the value holds no task, thunk, reference
  or promise.
Then what only such constants reach is left out too: the code of each is
never translated. The `IO.Error` builder instances that Stage 1 made stay:
the lowering refers to them by name. A constant that is read stays a
startup step, at its place, as before.

Unobservable: natively the dropped constant is evaluated once, at startup,
and nothing reads the value. Its evaluation terminates and writes nothing,
so leaving it out changes no output, no exit code and no order of the other
steps. What can differ is resource exhaustion: an evaluation that natively
runs out of memory or exceeds a size limit of Lean's runtime (`Nat.pow` of
an exponent above 2^32) stops the native program at startup, and lean2rr's
program runs (plan §10, "Unread constants are not evaluated"). Memory use
and startup time drop.

With `L2R_DEBUG` set, lean2rr prints the decision for every
constant step on lean2rr's stderr. Without this pass every constant is a
startup step.
-/

namespace LeanToReussir.Opt.UnreadConsts
open Lean Compiler LCNF

/-- The operations of a fixed-width number type that are externs of Lean's
library and total: arithmetic wraps, a division or remainder by zero gives
0 or the dividend (`INT64_MIN / -1` too), a shift takes its amount modulo
the width, a conversion wraps or (from a float) saturates. -/
def fixedWidthOps : List String :=
  ["add", "sub", "mul", "div", "mod", "neg", "abs", "land", "lor", "xor", "complement",
   "shiftLeft", "shiftRight", "log2", "decEq", "decLt", "decLe", "ofNat", "ofNatLT", "ofInt",
   "ofBitVec", "toBitVec", "toNat", "toInt", "toUInt8", "toUInt16", "toUInt32", "toUInt64",
   "toUSize", "toInt8", "toInt16", "toInt32", "toInt64", "toISize", "toFloat", "toFloat32"]

/-- The float operations that are externs of Lean's library: IEEE 754
arithmetic and the C library's functions are total (a NaN or an infinity
for what has no number); a conversion to an integer saturates. -/
def floatOps : List String :=
  ["add", "sub", "mul", "div", "neg", "abs", "beq", "decLt", "decLe", "lt", "le", "isNaN",
   "isInf", "isFinite", "ofBits", "toBits", "ofModel", "toModel", "frExp", "scaleB", "toString",
   "sqrt", "cbrt", "exp", "exp2", "log", "log2", "log10", "pow", "sin", "cos", "tan", "asin",
   "acos", "atan", "atan2", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "ceil", "floor",
   "round", "toFloat", "toFloat32", "toUInt8", "toUInt16", "toUInt32", "toUInt64", "toUSize",
   "toInt8", "toInt16", "toInt32", "toInt64", "toISize"]

/-- Externs of Lean's library that only compute their result from their
arguments: total (every argument has a result; see `fixedWidthOps` and
`floatOps`; an index with a proof that it is in bounds), with no message,
no closure argument and no runtime object (task, thunk, reference,
promise). The only way one can fail is to run out of a resource: memory,
or the exponent limit of `Nat.pow` and `Nat.shiftLeft` (natively an
internal panic above 2^32: the result would need more than 2^32 bits). An
extern that can panic (`Array.get!Internal`, `Array.set!`,
`ByteArray.get!`, `String.get!`, `sorryAx`), trace, read the outside world
or look at the representation of objects (`ptrAddrUnsafe`) is not listed.
A constructor with an extern implementation (`Array.mk`, `String.mk`,
`ByteArray.mk`) is a constructor (`classifyCall`). -/
def pureExterns : Std.HashSet Name := Id.run do
  let mut s : Std.HashSet Name := Std.HashSet.ofList [
    -- Nat and Int (big numbers).
    ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.modCore, ``Nat.pow, ``Nat.gcd,
    ``Nat.beq, ``Nat.ble, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``Nat.pred, ``Nat.land,
    ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.log2,
    ``Int.neg, ``Int.add, ``Int.sub, ``Int.mul, ``Int.tdiv, ``Int.tmod, ``Int.ediv, ``Int.emod,
    ``Int.decEq, ``Int.decLt, ``Int.decLe, ``Int.decNonneg, ``Int.natAbs, ``Int.toNat,
    ``mixHash, ``Char.ofNatAux, ``Lean.Name.beq,
    -- Arrays: the operations whose index has a proof, never `!`.
    ``Array.mkEmpty, ``Array.emptyWithCapacity, ``Array.replicate, ``Array.push, ``Array.pop,
    ``Array.size, ``Array.usize, ``Array.getInternal, ``Array.uget, ``Array.set, ``Array.uset,
    ``Array.swap, ``Array.toList,
    ``ByteArray.emptyWithCapacity, ``ByteArray.push, ``ByteArray.size, ``ByteArray.usize,
    ``ByteArray.get, ``ByteArray.uget, ``ByteArray.set, ``ByteArray.uset, ``ByteArray.hash,
    ``ByteArray.beq, ``ByteArray.decEq, ``ByteArray.data,
    ``FloatArray.emptyWithCapacity, ``FloatArray.push, ``FloatArray.size, ``FloatArray.usize,
    ``FloatArray.get, ``FloatArray.uget, ``FloatArray.set, ``FloatArray.uset, ``FloatArray.data,
    -- Strings.
    ``String.push, ``String.append, ``String.length, ``String.utf8ByteSize, ``String.decEq,
    ``String.hash, ``String.data, ``String.toList, ``String.ofList, ``String.toUTF8,
    ``String.Internal.append, ``String.Internal.length]
  for t in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
            "ISize"] do
    for op in fixedWidthOps do s := s.insert (Name.mkStr (Name.mkSimple t) op)
  for t in ["Float", "Float32"] do
    for op in floatOps do s := s.insert (Name.mkStr (Name.mkSimple t) op)
  for t in ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
            "ISize"] do
    s := s.insert (Name.mkStr `Bool ("to" ++ t))
  return s

/-- Whether `n` is a computed-field implementation that Lean makes
(`Lean.Elab.ComputedFields`: `C._override` for a constructor `C`, `f._override`
for a computed field `f`, each the `implemented_by` of its declaration): an
`unsafe` definition only because it casts between a type and its
implementation type, which have one representation. -/
def isComputedFieldImpl (env : Environment) (n : Name) : Bool :=
  match n with
  | .str p "_override" => Compiler.getImplementedBy? env p == some n
  | _ => false

/-- What the pass looks at: the instances with code of Stage 1, by name,
the names of its extern instances, and its keys. -/
structure Ctx where
  env : Environment
  code : Std.HashMap Name (Decl .pure)
  externs : NameSet
  keys : NameMap InstKey
  monoExterns : NameSet

/-- The declaration an instance was made from (itself for a name Stage 1
kept: a monomorphic extern, a constructor). -/
def Ctx.orig (cx : Ctx) (n : Name) : Name := ((cx.keys.find? n).map (·.decl)).getD n

/-- What a call does: nothing that shows (a constructor, a closure, a pure
extern), a run of an instance's code, or something that may show. -/
inductive Call where
  | quiet
  | runs (inst : Name)
  | shows (why : String)

/-- What the application of `c` to `nargs` arguments does. Fewer arguments
than parameters build a closure, which runs nothing. -/
def classifyCall (cx : Ctx) (c : Name) (nargs : Nat) : Call := Id.run do
  if c == ``Decidable.decide then return .quiet
  if let some d := cx.code[c]? then
    if nargs < d.params.size then return .quiet
    if nargs > d.params.size then return .shows s!"applies the result of {cx.orig c}"
    return .runs c
  let o := cx.orig c
  if let some (.ctorInfo ci) := cx.env.find? o then
    return if opaqueTypes.contains ci.induct then .shows s!"builds a {ci.induct}" else .quiet
  if cx.externs.contains c || cx.monoExterns.contains c || isExtern cx.env o then
    return if pureExterns.contains o then .quiet else .shows s!"calls the extern {o}"
  if (getInitFnNameFor? cx.env o).isSome then return .shows s!"reads the initialize constant {o}"
  return .shows s!"calls {o}, which has no code"

/-- What code `c` shows by itself (the first reason, if any), and the
instances it runs (`classifyCall`). A local function's body runs only when
the function value is applied, which shows here; a join point's body runs
at its jumps. Lean puts `unreach` where the types prove that no value gets
(`False.elim`, an impossible match arm): it never runs, as long as no proof
rests on a claim Lean did not check (`axiomTaints`; natively
`False.elim sorry` reaches `lean_internal_panic_unreachable`). -/
partial def scanCode (cx : Ctx) : Code .pure → StateM (Option String × Array Name) Unit
  | .let d k => do
    match d.value with
    | .lit _ | .erased | .proj .. => pure ()
    | .fvar _ args => unless args.isEmpty do note "applies a function value"
    | .const c _ args =>
      match classifyCall cx c args.size with
      | .quiet => pure ()
      | .runs m => modify fun (w, ms) => (w, ms.push m)
      | .shows why => note why
    | _ => note "impure code"
    scanCode cx k
  | .fun _ k _ => scanCode cx k
  | .jp d k => do scanCode cx d.value; scanCode cx k
  | .cases c => c.alts.forM (scanCode cx ·.getCode)
  | .jmp .. | .return _ | .unreach _ => pure ()
where
  note (why : String) : StateM (Option String × Array Name) Unit :=
    modify fun (w, ms) => (w <|> some why, ms)

/-- The kernel declaration that instance `n` comes from: its declaration,
or for a declaration the compiler made (a specialization `f._at_.g.spec_2`,
a lifted lambda), the one it was made from. -/
def Ctx.source? (cx : Ctx) (n : Name) : Option Name :=
  compiledOwner cx.env.contains (cx.orig n)

/-- Whether `s` is in a module of Lean's toolchain (`Init`, `Std`, `Lean`,
lean2rr's shim). -/
def isToolchainDeclIn (env : Environment) (s : Name) : Bool :=
  match env.getModuleIdxFor? s with
  | some i => isToolchainModule env.header.moduleNames[i.toNat]!
  | none => false

/-- Whether a recursion through instance `n` ends, as Lean's library
guarantees: `n` comes from a declaration of the toolchain (which has no
`sorry`) that is a definition Lean checked (structural or well-founded
recursion), or an `unsafe` implementation of one (`implemented_by`: the
loop of `Array.foldlMUnsafe` runs over an index range), or a part of
one; not a `partial` definition. A recursion through the program's own
code does not count: its termination proof could use `sorry`. A recursion
of the toolchain can still depend on a proof the program passes in (the
`step_pos` of a `Std.Legacy.Range`, the measure of a well-founded loop),
and on the values that proof is about, which the compiled code computes:
the proof can rest on `sorry` or an axiom of the program, and the code
that computes the values can differ from the kernel's terms (a `@[csimp]`
theorem proved with `sorry`, an `@[implemented_by]` of the program, the
`_unsafe_rec` code of a `partial` definition). `axiomTaints` checks these
instead. `impls`: the `implemented_by` targets of safe declarations
(`implTargets`). -/
def Ctx.recursionEnds (cx : Ctx) (impls : NameSet) (n : Name) : Bool := Id.run do
  let some s := cx.source? n | return false
  unless isToolchainDeclIn cx.env s do return false
  let some info := cx.env.find? s | return false
  if info matches .opaqueInfo _ && cx.env.contains (Compiler.mkUnsafeRecName s) then return false
  if !info.isUnsafe then return true
  -- An `unsafe` declaration: an implementation, or a `let rec` of one
  -- (`Array.foldlMUnsafe.fold`, a private name in the module system).
  let mut p := userName s
  while !p.isAnonymous do
    if impls.contains p then return true
    p := p.getPrefix
  return false

/-- The `implemented_by` targets of safe declarations, without their
private prefixes. -/
def implTargets (env : Environment) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (n, ci) in env.constants.toList do
    if let some impl := Compiler.getImplementedBy? env n then
      unless ci.isUnsafe do out := out.insert (userName impl)
  return out

/-- Lean's three standard axioms. They are consistent: a proof that uses
only these cannot prove `False`. -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Whether the walk of `axiomTaints` stops at `n`: a declaration of Lean's
toolchain that is not an axiom, and not `Lean.reduceBool` or
`Lean.reduceNat`: the kernel reduces these by running compiled code, and
their values name the axiom `Lean.trustCompiler` (as `collectAxioms`
reports for a proof by `rfl` through them). -/
def isAxiomLeaf (env : Environment) (n : Name) : Bool :=
  isToolchainDeclIn env n && !(env.find? n matches some (.axiomInfo _)) &&
    n != ``Lean.reduceBool && n != ``Lean.reduceNat

/-- For the kernel declarations `starts`, each declaration that rests on a
claim Lean did not check, with what it rests on (`the axiom sorryAx`):
- an axiom other than the standard ones (`standardAxioms`): `sorryAx` for a
  `sorry`, an `axiom` of the program, the axiom that Lean 4.34 adds for each
  use of `native_decide` (`t._native.native_decide.ax_1_1`),
  `Lean.ofReduceBool` (conservative: these are sound when the compiler is);
- an `@[implemented_by]` of the program: the code that runs is the target,
  which can compute other values than the declaration (`stepI 0 = 1` with an
  implementation that gives 0: the `step_pos` proof of a range is about the
  declaration, the loop runs the target). Lean's computed-field
  implementations (`isComputedFieldImpl`) only cast, and do not count.
As Lean's `collectAxioms`, the walk goes through the type and the value of
each declaration it reaches, and an inductive type's constructors. It also
goes where the compiled code differs from the kernel's terms:
- into the `implemented_by` target (the code that runs, which Lean can
  inline into the constant's own code);
- into `f._unsafe_rec` for a `partial` definition `f` (its compiled code,
  `Compiler.mkUnsafeRecName`; the kernel's `f` is an opaque constant whose
  value is any inhabitant);
- for a reference to `f`, also a toolchain `f`, into each theorem of the
  program stated as `@f = @g` and into `g` (`programCsimps`: every
  `@[csimp]` theorem of the program, global, `scoped` or `local`; the
  compiler replaces `f` by `g`, and a theorem proved with `sorry` lets `g`
  compute other values).
It does not go into a declaration of Lean's toolchain that is not an axiom
(`isAxiomLeaf`): Lean's safe declarations use only the standard axioms (in
Lean 4.34.0's `Init` and `Std`, the only others named by a declaration are
`lcProof`, in `unsafe` implementations, and `Lean.trustCompiler`, in
`Lean.reduceBool` and `Lean.reduceNat`, which the walk enters), and their
`implemented_by`s and `csimp` theorems are trusted, as everywhere in
lean2rr; so the walk costs the program's declarations only. One walk for all of `starts`: each
declaration is visited once, then each claim found goes back along the
references to every declaration that reaches it (cycles, an inductive type
and its constructors, are fine). -/
def axiomTaints (env : Environment) (starts : Array Name) : NameMap String := Id.run do
  -- The theorems `@f = @g` of the program, by `f`, with `g`.
  let csimp : Std.HashMap Name (Array Name) := (programCsimps env).foldl (init := {}) fun m e =>
    m.alter e.fromDeclName fun xs => some ((xs.getD #[]).push e.thmName |>.push e.toDeclName)
  let mut seen : NameSet := {}
  let mut todo := starts.filter (!isAxiomLeaf env ·)
  -- `isAxiomLeaf` of each name met, once each: `Environment.find?` is most
  -- of the walk's cost otherwise (a reference to `Nat` from every
  -- declaration; Z06g: 68 000 references, 4 500 declarations).
  let mut leaves : Std.HashMap Name Bool := {}
  -- For each declaration reached, the declarations of the program that use it.
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut taint : NameMap String := {}
  let mut found : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if ci matches .axiomInfo _ then
      unless standardAxioms.contains n do
        taint := taint.insert n s!"the axiom {n}"
        found := found.push n
      continue
    let impl := Compiler.getImplementedBy? env n
    if let some t := impl then
      unless isComputedFieldImpl env t do
        taint := taint.insert n s!"the implemented_by of {n}"
        found := found.push n
    let unsafeRec := Compiler.mkUnsafeRecName n
    let refs := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++
      (match ci with | .inductInfo v => v.ctors.toArray | _ => #[]) ++
      impl.toArray ++ (if env.contains unsafeRec then #[unsafeRec] else #[])
    for m in refs do
      -- The `csimp` theorems that may replace `m` in compiled code, and
      -- the replacements.
      for u in #[m] ++ csimp.getD m #[] do
        let leaf ← match leaves[u]? with
          | some b => pure b
          | none => do
            let b := isAxiomLeaf env u
            leaves := leaves.insert u b
            pure b
        if leaf then continue
        users := users.alter u fun us => some ((us.getD #[]).push n)
        unless seen.contains u do todo := todo.push u
  let mut work := found
  while h : work.size > 0 do
    let m := work.back
    work := work.pop
    let some a := taint.find? m | continue
    for n in users.getD m #[] do
      unless taint.contains n do
        taint := taint.insert n a
        work := work.push n
  return taint

/-- For each instance in `starts`, why evaluating it (its code, with all its
parameters given) may show, or nothing: the instances it runs, transitively
(`scanCode`), show nothing, and every recursion among them ends
(`recursionEnds`). The program's own `unsafe` code shows (a cast can make
any value of any type), except the computed-field implementations Lean
makes (`isComputedFieldImpl`). So does an instance whose declaration rests
on a claim Lean did not check (`axiomTaints`): a false claim can reach an
`unreach` (`False.elim`) or make a recursion of Lean's library run for
ever (a `Std.Legacy.Range` of step 0; hunt r7 B and its review). -/
def blockers (cx : Ctx) (starts : Array Name) : Std.HashMap Name String := Id.run do
  -- Each instance's own blocker and the instances it runs.
  let mut nodes : Std.HashMap Name (Option String × Array Name) := {}
  let mut todo := starts
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if nodes.contains n then continue
    let some d := cx.code[n]? | nodes := nodes.insert n (some s!"{cx.orig n} has no code", #[]); continue
    let o := cx.orig n
    -- Unsafe: the declaration the instance comes from (a specialization of
    -- an `unsafe` function is its code).
    let src := cx.source? n
    let own : Option String :=
      if (src.bind cx.env.find?).any (·.isUnsafe) && !(src.any (isComputedFieldImpl cx.env)) &&
          !(src.any (isToolchainDeclIn cx.env)) then
        some s!"{o} is unsafe"
      else none
    let (w, ms) := match d.value with
      | .code c => ((scanCode cx c).run (own, #[])).2
      | .extern _ => (some s!"{o} is an extern", #[])
    nodes := nodes.insert n (w, ms)
    for m in ms do unless nodes.contains m do todo := todo.push m
  -- The declarations that rest on a claim Lean did not check (`sorry`,
  -- an axiom of the program, an `implemented_by`): one walk for all.
  let srcs := nodes.toArray.filterMap fun (n, _) => cx.source? n
  let taint := axiomTaints cx.env srcs
  unless taint.isEmpty do
    for (n, (w, ms)) in nodes.toArray do
      if w.isSome then continue
      let some s := cx.source? n | continue
      if let some a := taint.find? s then
        nodes := nodes.insert n (some s!"{s} depends on {a}", ms)
  -- The strongly connected components, callees first.
  let succs (n : Name) : List Name := ((nodes[n]?.map (·.2)).getD #[]).toList
  let comps := Lean.SCC.scc (nodes.toList.map (·.1)) succs
  let mut impls? : Option NameSet := none
  let mut out : Std.HashMap Name String := {}
  for comp in comps do
    let inComp (m : Name) : Bool := comp.contains m
    let cyclic := comp.length > 1 || comp.any fun n => (succs n).contains n
    let mut why : Option String := none
    for n in comp do
      if let some w := (nodes[n]?.bind (·.1)) then why := why <|> some w
      for m in succs n do
        unless inComp m do
          if let some w := out[m]? then why := why <|> some w
    if why.isNone && cyclic then
      let impls := impls?.getD (implTargets cx.env)
      impls? := some impls
      if let some n := comp.find? (!cx.recursionEnds impls ·) then
        why := some s!"recursion through {cx.orig n}"
    if let some w := why then
      for n in comp do out := out.insert n w
  return out

/-- Whether type `t` mentions a task, thunk, reference or promise. -/
def holdsRuntimeObject (t : Expr) : Bool :=
  (t.find? fun e => match e with
    | .const n _ => opaqueTypes.contains n
    | _ => false).isSome

/-- The instances that the code of `roots` names, transitively (`roots`
included). -/
def reachable (code : Std.HashMap Name (Decl .pure)) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some { value := .code c, .. } := code[n]? then
      for m in codeConsts c #[] do
        unless seen.contains m do todo := todo.push m
  return seen

/-- The pass (see the module doc): the startup steps without the unread
constants that have no effect, and Stage 1's state without the
declarations only those reach. `mainInst` and `errStr` are the instances
of `main` and of the error printer. -/
def prune (st : MonoState) (mainInst errStr : Name) (startup : Array StartupStep) :
    CoreM (Array StartupStep × MonoState) := do
  let env ← getEnv
  let code : Std.HashMap Name (Decl .pure) := st.decls.foldl (fun m d => m.insert d.name d) {}
  let cx : Ctx := { env, code, keys := st.keys, monoExterns := st.monoExterns,
                    externs := st.externs.foldl (fun m d => m.insert d.name) {} }
  -- The constant steps whose evaluation cannot show.
  let cafs := startup.filterMap fun | .caf i => some i | _ => none
  let bl := blockers cx cafs
  let mut why : NameMap String := {}
  for i in cafs do
    if (code[i]?.map (holdsRuntimeObject ·.type)).getD true then
      why := why.insert i "its value may hold a task, thunk, reference or promise"
    else if let some w := bl[i]? then why := why.insert i w
  let quiet := startup.filterMap fun | .caf i => if why.contains i then none else some i | _ => none
  let quietSet : NameSet := quiet.foldl (·.insert ·) {}
  -- Everything else is a root. So are the `IO.Error` builders Stage 1
  -- made: the lowering calls them by name for every fallible IO extern and
  -- child-process extern (`ensureIOErrorBuilders`, `LowerCtx.ioErrorBuilders`),
  -- also when only a left-out constant names one in its code
  -- (`IO.Error.mkAlreadyExistsFile`; test `RtUnreadConstsIoErr`) and when
  -- nothing names one. And so, as a net, is every other instance that
  -- nothing reaches (`implicit`). Stage 1 makes an instance without a
  -- reference in code only for these builders and for init functions, and
  -- an init function is a root through its `.init` step.
  let byDecl : NameMap Name := st.keys.foldl (init := {}) fun m inst k =>
    if k.typeArgs.isEmpty && k.dicts.isEmpty then m.insert k.decl inst else m
  let exports ← match st.exports with
    | some m => pure m
    | none => (exportMap.run' { config := {} } : CoreM _)
  let builders := ioErrorBuilderSyms.filterMap fun sym => (exports.get? sym).bind byDecl.find?
  let roots := #[mainInst, errStr] ++ builders ++ startup.filterMap fun
    | .caf i => if quietSet.contains i then none else some i
    | .ioUnit i | .init _ i => some i
  let all := reachable code (roots ++ quiet)
  let implicit := (st.decls.map (·.name) ++ st.externs.map (·.name)).filter (!all.contains ·)
  let kept := reachable code (roots ++ implicit)
  let dropped := quietSet.filter (!kept.contains ·)
  if (← IO.getEnv "L2R_DEBUG").isSome then
    for step in startup do
      let .caf i := step | continue
      let o := cx.orig i
      if dropped.contains i then IO.eprintln s!"lean2rr: unread-consts: {o}: left out"
      else if let some w := why.find? i then IO.eprintln s!"lean2rr: unread-consts: {o}: kept, {w}"
      else IO.eprintln s!"lean2rr: unread-consts: {o}: kept, read"
  if dropped.isEmpty then return (startup, st)
  let decls := st.decls.filter (kept.contains ·.name)
  let externs := st.externs.filter (kept.contains ·.name)
  -- The keys of the instances left out go too: later passes find
  -- instances by declaration through them (`ResourceFlow`, the
  -- `IO.Error` builders).
  let keys := (st.decls ++ st.externs).foldl (init := st.keys) fun ks d =>
    if kept.contains d.name then ks else ks.erase d.name
  -- lean2rr's notes name only the externs of the program still compiled.
  let used : NameSet := (decls ++ externs).foldl (fun s d => s.insert (cx.orig d.name)) {}
  let startup := startup.filter fun | .caf i => !dropped.contains i | _ => true
  let externBodies := st.externBodies.filter fun (_, d) => used.contains d
  let externBindingWarnings := st.externBindingWarnings.filter fun (d, _) => used.contains d
  return (startup, { st with decls, externs, keys, externBodies, externBindingWarnings })

end LeanToReussir.Opt.UnreadConsts

namespace LeanToReussir

/-- Registry entry point: the startup steps of unread constants without
effects left out, with what only they reach. -/
def Opt.UnreadConsts.install (c : PassConfig) : PassConfig :=
  { c with startupPrune := some Opt.UnreadConsts.prune }

end LeanToReussir
