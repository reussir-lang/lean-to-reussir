import Lean
import LeanToReussir.PassConfig
import LeanToReussir.TypedToMono
import LeanToReussir.TypedStructProjCases
import LeanToReussir.Opt.FloatLits
import LeanToReussir.Opt.SinkProj
import LeanToReussir.Opt.Outline
import LeanToReussir.Opt.CheapConsts
import LeanToReussir.Opt.ClosedChains
import LeanToReussir.Opt.PreludeRepr
import LeanToReussir.Opt.JpSink
import LeanToReussir.Opt.JpSmall
import LeanToReussir.Opt.LazyFields
import LeanToReussir.Opt.NullaryScrutinee
import LeanToReussir.Opt.StateMachines
import LeanToReussir.Opt.ValueStructs
import LeanToReussir.Opt.FieldOrder

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
`optimizations`. The order of the lines is the order of installation, so
passes of the same kind run in this order.
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
  .skip `toImpure
    "boxing, reference counting and reset/reuse belong to Reussir (Stage 2 ends at mono, plus extractClosed)"]

/-- The optional passes, in installation order. -/
def optimizations : Array OptPass := #[
  ⟨"field-order", true, "record fields in decreasing alignment, so records have no padding (declaration order otherwise)", FieldOrder.install⟩,
  ⟨"value-structs", true, "a structure with one relevant field (ST.Out of every BaseIO call) is a [value] struct, not a heap record", ValueStructs.install⟩,
  ⟨"float-lits", true, "Float literals (Float.ofScientific/ofNat on literals) folded to their bits at compile time", FloatLits.install⟩,
  ⟨"cheap-consts", true, "constants built from small literals and scalar conversions recomputed at each use, not cached", CheapConsts.install⟩,
  ⟨"closed-chains", true, "closed terms used once, by another constant, evaluated there instead of cached", ClosedChains.install⟩,
  ⟨"prelude-repr", true, "Nat.repr/Int.repr calls replaced by the runtime's GMP versions (same strings)", PreludeRepr.install⟩,
  ⟨"jp-sink", true, "join points moved down to the smallest code containing their jumps, before the J1-J4 choice", JpSink.install⟩,
  ⟨"jp-small", true, "small join points (at most 40 nodes) duplicated at their jumps (J1') instead of outlined", JpSmall.install⟩,
  ⟨"state-machines", true, "a loop through outlined join points lowered as one function over an entry-point enum (J4)", StateMachines.install⟩,
  ⟨"lazy-fields", true, "fields of a matched value kept live (stored or returned whole) bound where used (Reussir bug 7 workaround)", LazyFields.install⟩,
  ⟨"nullary-scrutinee", true, "in the arm of a constructor without fields, the matched value rebuilt instead of kept", NullaryScrutinee.install⟩,
  ⟨"sink-proj", true, "field projections sunk into the branches that use them (Reussir token-reuse workaround)", SinkProj.install⟩,
  ⟨"outline", true, "deep and long tail paths cut into chains of functions: not faster, but needed to build very deep or long functions (Reussir bugs 16, 17)", Outline.install⟩]

/-- Parts of the translation that look like optimizations but are not
optional. -/
def required : Array RequiredPass := #[
  ⟨"startup-chunks", "the startup chain cut into functions of at most 128 steps (Emit/Startup, startupChunk)",
    "not an optimization: one chain of nested matches would be as deep as the program has initializers, and rrc's recursive lowering overflows its stack on a few thousand (translation plan §5.12)"⟩]

/-- The configuration with the enabled optimizations, after turning off
those named in `disabled` and on those named in `enabled`. An unknown name,
or the name of a required part, is an error. -/
def config (disabled enabled : Array String := #[]) : Except String PassConfig := do
  for n in disabled ++ enabled do
    if let some r := required.find? (·.name == n) then
      throw s!"'{n}' is required, not an optimization: {r.reason}"
    unless optimizations.any (·.name == n) do
      throw s!"unknown optimization '{n}' (see --list-opts)"
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
