import Lean
import LeanToReussir.PassConfig

/-!
# Declarations that nothing reaches left out before Stage 3 (optimization `unreached-decls`)

Stage 2 gives more declarations than the program can run. Lean's passes
inline a callee into its callers, specialize a function at its arguments
and extract closed terms, and the callee, the general function or the code
that a closed term came from stays as a declaration that no code names.
Without this pass Stage 3, the passes over mono code and the lowering
translate every one of them, and only `conv-liveness`, at the end of the
lowering, drops the functions that nothing reaches. A program that
imports `Cslib.Init` and prints one line has 69,730 declarations with code
after Stage 2; 13,829 of them are not reachable from the roots below.

The pass runs on Stage 2's declarations, before Stage 3 (a
`PassConfig.prunePasses` pass, after `unread-fields` when that is on). It
keeps each declaration with code that the roots reach through references
in code, and drops the others. Extern declarations (no code) all stay:
they cost no translation, and the whole-program checks that read them
(`typed-cells` reads the instances of the reference primitives) give the
same answers.

Roots: the declarations the entry point calls (`main`, the error printer
`IO.Error.toString`) and every startup step's declaration: the program's
constants and `initialize` actions, the initializers of `Init` and `Std`,
and the initializer of each `Lean` package `initialize` constant that the
program uses (Stage 1 adds a startup step for each one that the code it
reached reads). Each such initializer stays a root, also when kept code no
longer reads its constant, so the startup runs the same steps as without
this pass (only `unread-fields` leaves out such a step, when kept code
does not read the constant). The `IO.Error` builders that Stage 1 made are
roots too: the lowering calls them by name for the errors of fallible IO
externs (`LowerCtx.ioErrorBuilders`), also where no code names them.

Edges: every constant that a `let` names in the code of a kept
declaration, in local functions and join points too: a full call, a
partial application or a declaration used as a function value (a closure
can run later, from anywhere it flows), the read of a constant, a
type-class instance (after Stage 1 every instance is a named constant).
Stage 1 already followed `implemented_by`, the Lean bodies of externs and
the reads of `initialize` constants (each a startup step above), so each
appears as such a reference or as a root.

Why nothing that can run is left out: in mono LCNF a declaration refers
to another one only through a `let` value `.const` (types, projections,
cases and arguments name types and constructors, never a declaration with
code; `Code .pure` and `LetValue .pure` cannot hold the impure phase's
constructors, whose proofs need `.impure`). The lowering emits a call of a declaration only where its code is
such a reference, at the entry point and in the startup chain (the
roots), and for the `IO.Error` builders (roots); the function of a
function value runs from an application function whose arms come from the
partial applications in lowered code. The passes after Stage 3
(`flatten-structs`, the typed `map` loops, `prelude-int-ops`, `mod-pow2`,
`utf8-size-add`) make new declarations and new references from the
declarations they get, or to prelude functions and extern instances. A
reference to a declaration the pass left out would stop the lowering with
an internal error (`calleeOf`: "unknown callee"), never give another
program. (Stage 2 records every declaration it compiles in Lean's mono
extension, the dropped ones too; `calleeOf` takes a name it finds only
there for an extern of its own name only when that declaration is an
extern. Before that check, such a name was lowered as a call of a missing
extern `l2r_extern_…`: the program was refused for an extern that it
does not have, or with `L2R_ALLOW_MISSING_EXTERNS` rrc stopped at an
unknown function.)

Guard: two declarations with code of one name turn the pass off (the walk
by name would follow only one of them): every declaration stays.

The output is the same program: the pass changes no kept declaration, and
the functions dropped are never called. It is not byte-identical: lean2rr's
one name counter, the payload numbers of `Box` and the once-cell slots
shift; types, payload types of `Box` and variants of function-value enums
that only dropped code registered go; and choices made from the whole
program no longer count the dropped code (stream cells, `flatten-structs`'
splits of results, a closed term then read once evaluated in its reader,
`closed-chains`, `merge-fns`' first copy; also `programCasts`,
`programCreatesTasks`, compact and typed arrays, typed cells)
(docs/implementation/optional-passes.md).
-/

namespace LeanToReussir.Opt.UnreachedDecls
open Lean Compiler LCNF

/-- The pass (`PassConfig.prunePasses`): of Stage 2's declarations
`decls`, those with code that the roots reach, and every extern
declaration. `keep`: the declarations the entry point always needs;
`inits`: every startup step of an `initialize` constant as (constant,
initializer, whether only kept code's reads make it run). -/
def run (keys : NameMap InstKey) (keep : Array Name) (inits : Array (Name × Name × Bool))
    (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let debug := (← IO.getEnv "L2R_DEBUG").isSome
  let mut code : Std.HashMap Name (Code .pure) := {}
  for d in decls do
    if let .code c := d.value then
      -- Two declarations of one name: the walk by name would follow one.
      if code.contains d.name then
        if debug then IO.eprintln s!"lean2rr: unreached-decls: off, two declarations named {d.name}"
        return decls
      code := code.insert d.name c
  -- The `IO.Error` builders' instances, found as the lowering finds them
  -- (`lowerProgram`: monomorphic instances by declaration).
  let byDecl : NameMap Name := keys.foldl (init := {}) fun m inst k =>
    if k.typeArgs.isEmpty && k.dicts.isEmpty then m.insert k.decl inst else m
  let exports ← (exportMap.run' { config := {} } : CoreM _)
  let builders := ioErrorBuilderSyms.filterMap fun sym => (exports.get? sym).bind byDecl.find?
  let roots := keep ++ inits.map (·.2.1) ++ builders
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some c := code[n]? then
      for m in codeConsts c #[] do
        unless seen.contains m do todo := todo.push m
  let out := decls.filter fun d => !(d.value matches .code _) || seen.contains d.name
  if debug then
    IO.eprintln s!"lean2rr: unreached-decls: {out.size} of {decls.size} declarations kept \
      ({code.size - (decls.size - out.size)} of {code.size} with code), {decls.size - out.size} dropped"
  return out

/-- Registry entry point. -/
def install (c : PassConfig) : PassConfig :=
  { c with prunePasses := c.prunePasses.push run }

end LeanToReussir.Opt.UnreachedDecls
