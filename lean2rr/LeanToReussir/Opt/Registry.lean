import Lean
import LeanToReussir.PassConfig
import LeanToReussir.TypedToMono
import LeanToReussir.TypedStructProjCases
import LeanToReussir.Opt.FloatLits
import LeanToReussir.Opt.SinkProj
import LeanToReussir.Opt.CheapConsts
import LeanToReussir.Opt.PreludeRepr
import LeanToReussir.Opt.JpSink
import LeanToReussir.Opt.JpSmall
import LeanToReussir.Opt.LazyFields
import LeanToReussir.Opt.NullaryScrutinee
import LeanToReussir.Opt.StateMachines
import LeanToReussir.Opt.ValueStructs
import LeanToReussir.Opt.FieldOrder
import LeanToReussir.Opt.NatArrays
import LeanToReussir.Opt.PlaceholderCache
import LeanToReussir.Opt.SplitMapLoops
import LeanToReussir.Opt.OriginFreeReads
import LeanToReussir.Opt.FreshRebuild

/-!
# The pass registry

Every pass lean2rr adds to or changes in the pipeline, in one place:

* `stage2`: the edits of Lean's own Stage 2 pass lists (required);
* `optimizations`: the optional passes, one line each (name, enabled by
  default, description, the module's `install`). The core translation needs
  none of them: removing a line removes the optimization, and
  `lean2rr --disable-opt NAME` turns one off for a run;
* `required`: parts of the translation that look like optimizations but are
  not optional, with the reason.

Stage 1 recompiles some declarations with Lean's base passes before
`saveBase`, edited for type-unsafe code (`Mono.recompilePasses`); those
edits depend on Stage 1's analysis and stay there.

Adding a pass: write `Opt/Name.lean` with the transformation and an
`install : PassConfig → PassConfig` that plugs it into a hook of
`PassConfig` (passes over mono LCNF or over the generated Reussir functions,
or a lowering hook of `LowerHooks`), import it here and add its line to
`optimizations`.

Order. The lines are installed in order, and every `install` keeps what
was installed before: list hooks (`monoPasses`, `rrPasses`) append, so
their passes run in line order; `prepareBody` and `fieldOrder` apply the
new pass after the earlier ones; the predicates (`duplicateJp`,
`recomputeConst`) are true if any pass says so; the binding hooks
(`structFields`, `enumFields`, `lowerAlt`, `stateMachine`) are consulted
newest first and hand what they do not handle to the earlier ones;
`armPrelude` places the earlier passes' `let`s first;
`preludeReplacements` is a map, where a later line wins for the same
definition; `preludePasses` run in line order; `valueStructs` is a switch. The core's own steps (`Outline`
before the passes over the generated functions) are not listed here.
-/

namespace LeanToReussir.Opt
open Lean Compiler LCNF

/-- lean2rr's edits of Lean's Stage 2 pass lists (translation plan §3). -/
def stage2 : Stage2Config := #[
  .replace `toMono toMonoK
    "Lean's toMono erases type-former arguments (HashMap values become lcAny); lean2rr's copy keeps constant type families, so Stage 3 and the lowering see exact types",
  .replace `structProjCases structProjCasesK
    "the other pass that converts types: its result types must agree with toMonoK's",
  .skip `inferVisibility
    "module-visibility bookkeeping; it transforms no code",
  .skip `extractClosed
    "run last, over all declarations, as Lean ran it (Pipeline.extractLikeLean, ExtractClosedK): module by module in Lean's order, following what the .olean records of each declaration's closed terms",
  .skip `toImpure
    "boxing, reference counting and reset/reuse belong to Reussir (Stage 2 ends at mono, plus extractClosed)"]

/-- The optional passes, in installation order. -/
def optimizations : Array OptPass := #[
  ⟨"field-order", true, "record fields in decreasing alignment, so records have no padding (declaration order otherwise)", FieldOrder.install⟩,
  ⟨"value-structs", true, "a structure with one relevant field (ST.Out of every BaseIO call) is a [value] struct, not a heap record", ValueStructs.install⟩,
  ⟨"nat-arrays", true, "Array Nat/Int as the runtime's one-word-per-element LNatArr/LIntArr", NatArrays.install⟩,
  ⟨"split-map-loops", true, "an Array.map loop whose element representation changes split into source and result arrays, instead of running on Boxes (Stage 3)", SplitMapLoops.install⟩,
  ⟨"placeholder-cache", true, "placeholders (box(0) at a type) that would allocate built once, in a once-cell", PlaceholderCache.install⟩,
  ⟨"float-lits", true, "Float literals (Float.ofScientific/ofNat on literals) folded to their bits at compile time", FloatLits.install⟩,
  ⟨"cheap-consts", true, "constants built from small literals and scalar conversions recomputed at each use, not cached", CheapConsts.install⟩,
  ⟨"prelude-repr", true, "Nat.repr/Int.repr calls replaced by the runtime's GMP versions (same strings; the runtime keeps them, unused, without the pass)", PreludeRepr.install⟩,
  ⟨"jp-sink", true, "join points moved down to the smallest code containing their jumps, before the J1-J4 choice", JpSink.install⟩,
  ⟨"jp-small", true, "small join points (own body at most 40 nodes, a copy expanding to at most 480 with the join points inlined into it, the copies beyond the first adding at most 2000, 4000 for a loop's continuation) duplicated at their jumps (J1') instead of outlined", JpSmall.install⟩,
  ⟨"state-machines", true, "a loop's state machine (J4) entered without allocation: parameters passed beside a nullary entry variant (placeholders at jumps)", StateMachines.install⟩,
  ⟨"lazy-fields", true, "fields of a matched value kept live (stored, returned or passed to a call whole) bound where used (Reussir bug 7 workaround)", LazyFields.install⟩,
  ⟨"nullary-scrutinee", true, "in the arm of a constructor without fields, the matched value rebuilt instead of kept", NullaryScrutinee.install⟩,
  ⟨"sink-proj", true, "field projections sunk into the branches that use them (Reussir token-reuse workaround)", SinkProj.install⟩,
  ⟨"fresh-rebuild", true, "in a program that never asks for an object's identity, an alternative that only returns a freshly built matched value returns it rebuilt from its fields (Reussir then reuses the cell in every alternative)", FreshRebuild.install⟩,
  ⟨"origin-free-reads", true, "in a program whose conversions never produce an array, array reads release without checking the origin table (LLVM then cancels a read's increment and release)", OriginFreeReads.install⟩]

/-- Parts of the translation that look like optimizations but are not
optional. -/
def required : Array RequiredPass := #[
  ⟨"startup-chunks", "the startup chain cut into functions of at most 128 steps (Emit/Startup, startupChunk)",
    "not an optimization: one chain of nested matches would be as deep as the program has initializers, and rrc's recursive lowering overflows its stack on a few thousand (translation plan §5.12)"⟩,
  ⟨"loop-state-machines", "a declaration whose outlined join point calls it back in tail position is one state machine, its entry variant carrying the parameters (J4; Lower/StateMachine)",
    "otherwise a loop through an outlined join point is mutually recursive and uses stack per iteration where native Lean uses none: without it, and with the join-point passes off, the classic Sieve and Strings overflowed Lean's 1 GiB stack at their medium size"⟩,
  ⟨"closed-chains", "a closed term used once, by another constant, is evaluated there instead of cached, and spliced into it when both are straight-line (Emit/Program, chainConsts, spliceChainConsts; Array Nat runs as tables: ArrayLits)",
    "an array literal is a chain of closed terms, and caching every step keeps every intermediate array: memory quadratic in the literal's length (10000 elements: 1036 MB instead of 7 MB); as one function per step, a 100000-element literal took ten minutes to build"⟩,
  ⟨"stage3-types", "Stage 3 recovers parameter types from call sites and result types from callers' bindings (MonoRetype: paramsFromCallers, refineSignature)",
    "type recovery, not a choice of representation: a value left at lcAny is a Box, and an array whose representation differs is converted, a copy, each time it crosses such a position (a call in a loop, each read of a constant), and the copy is another object than native Lean's"⟩,
  ⟨"outline", "deep and long tail paths and let values of a function cut into functions, recursive functions included (their loops through step values) (Outline)",
    "rrc's analyses are superlinear in nesting depth and straight-line length (Reussir bugs 16, 17), and so is the .rr text, whose indentation follows the nesting: without it a 3000-arm literal match in tail position gives 126 MB of .rr instead of 1 MB"⟩,
  ⟨"wildcard-sinks", "a wildcard arm covering several constructors releases the wide-enum values it holds and does not use through one out-of-line call (`l2r_sink`; Lower/Code, sinkWildcardHeld)",
    "rrc copies a wildcard arm into every constructor it covers and expands each release there in line, a match over the variants: a derived BEq/DecidableEq/Ord on an inductive with N constructors became N^3 code, and a 40-constructor one took 9 minutes to build (round-6 PRG6-02; docs/reussir-bugs.md bug 22)"⟩,
  ⟨"inline-anchors", "conversions, unboxings, and the applications of wrapped function values and of those of uniform types, kept out of rrc's MLIR inliner (#[transform_anchor]; Lower/Finish, anchoredFns)",
    "rrc's inliner grows the conversion code of polymorphic recursion through monad transformers exponentially (Reussir bug 20): an 8-line StateT tower used at IO did not build within 30 minutes or 15 GB"⟩]

/-- The configuration with the enabled optimizations, after turning off
those named in `disabled` and on those named in `enabled`. An unknown name,
the name of a required part, or a name both turned off and on is an
error. -/
def config (disabled enabled : Array String := #[]) : Except String PassConfig := do
  for n in disabled ++ enabled do
    if let some r := required.find? (·.name == n) then
      throw s!"'{n}' is required, not an optimization: {r.reason}"
    unless optimizations.any (·.name == n) do
      throw s!"unknown optimization '{n}' (see --list-opts)"
    if disabled.contains n && enabled.contains n then
      throw s!"'{n}' is both disabled and enabled"
  let on (o : OptPass) : Bool := (o.enabled || enabled.contains o.name) && !disabled.contains o.name
  return optimizations.foldl (init := { stage2 }) fun c o => if on o then o.install c else c

/-- The registry as text (`lean2rr --list-opts`). -/
def listing : String := Id.run do
  let mut out := "Optimizations (in order; --disable-opt NAME turns one off):\n"
  for o in optimizations do
    out := out ++ s!"  {o.name}{if o.enabled then "" else " (off by default)"}: {o.description}\n"
  out := out ++ "\nRequired (not optional):\n"
  for r in required do
    out := out ++ s!"  {r.name}: {r.description}\n    why: {r.reason}\n"
  out := out ++ "\nStage 2 edits of Lean's passes (required):\n"
  for e in stage2 do
    match e with
    | .replace n _ why => out := out ++ s!"  {n} replaced by lean2rr's copy: {why}\n"
    | .skip n why => out := out ++ s!"  {n} not run: {why}\n"
  return out

end LeanToReussir.Opt
