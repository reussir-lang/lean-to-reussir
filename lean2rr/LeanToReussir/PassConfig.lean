import Lean
import LeanToReussir.Pipeline
import LeanToReussir.Lower
import LeanToReussir.MonoRetype

/-!
# The configurable parts of the pipeline

`PassConfig` is everything Opt/Registry.lean configures: lean2rr's edits of
Lean's Stage 2 pass lists (required), and the hook points where optional
passes plug in. Every hook's default is the plain translation, so a
configuration with only the Stage 2 edits translates every program; an
optimization module (`Opt/*.lean`) changes hooks in its `install` function,
and the registry installs the enabled ones, in its order.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- What a pass over the generated Reussir functions can look at besides the
functions: the runtime prelude, the names of its functions, and the
program's type items (generated types, function-value enums, `Box`). -/
structure RRProgram where
  prelude : String
  preludeFns : Std.HashSet String
  types : Array RR.Item

structure PassConfig where
  /-- Edits of Lean's pass lists for Stage 2. -/
  stage2 : Stage2Config := #[]
  /-- Passes over Stage 2's declarations before Stage 3, in order, that may
  leave declarations out. They get the instance keys, the declarations the
  entry point always needs (`main`, the error printer, the startup steps
  that always run and their `initialize` constants), every startup step of
  an `initialize` constant as (constant, initializer, whether it is needed
  only while kept code reads the constant: the `Lean` package's constants
  that the program uses; the step of one whose initializer is left out does
  not run), and the declarations; they return the declarations to
  translate. Plain: none, every declaration Stage 1 reached is translated. -/
  prunePasses : Array (NameMap InstKey → Array Name → Array (Name × Name × Bool) → Array (Decl .pure) →
    CoreM (Array (Decl .pure))) := #[]
  /-- The optional parts of Stage 3 (the typed `map` loops). -/
  stage3 : Stage3Config := {}
  /-- Whether an `Array S` of a scalar `S` is stored compactly, `RVec<k>` of
  its storage kind `k`, for the kinds the whole-program check allows
  (`compactArrayKinds`, Opt/SplitMapLoops). Plain: every `Array α` is an
  array of `Box`es. -/
  compactArrays : Bool := false
  /-- Passes over the checked mono declarations (after Stage 3, before
  lowering), in order; they get the instance keys. -/
  monoPasses : Array (NameMap InstKey → Array (Decl .pure) → Array (Decl .pure)) := #[]
  /-- Passes over the checked mono declarations that need the environment
  (field types at type arguments, new declarations), run after
  `monoPasses`, in order. -/
  monoPassesCore : Array (NameMap InstKey → Array (Decl .pure) → CoreM (Array (Decl .pure))) := #[]
  /-- Unary Lean definitions returning a `String` replaced by a prelude
  function with the same results (definition ↦ prelude function and its
  parameter type). -/
  preludeReplacements : NameMap (String × RR.Ty) := {}
  /-- Whether a structure with a single relevant field is a `[value]`
  struct (no heap cell per value) rather than a shared record. -/
  valueStructs : Bool := false
  /-- Whether a placeholder (Lean's `box(0)` at a type) that would allocate
  is built once and kept in a once-cell. Plain: built where it is used. -/
  cachePlaceholders : Bool := false
  /-- Whether a constant whose boxing allocates (a `Float`, a `UInt64` from
  2^63) is boxed once and kept in a once-cell, as native Lean's
  `_boxed_const`. Plain: boxed where it is used. -/
  boxedConsts : Bool := false
  /-- The order of a constructor's relevant fields in its record, given
  their alignments: the fields' indices in record order. Plain: declaration
  order. -/
  fieldOrder : Array Nat → Array Nat := fun aligns => (List.range aligns.size).toArray
  /-- Whether the helpers generated at the end of Stage 4 (unboxing,
  application and conversion functions of function values) follow liveness: generated only once live code reaches them,
  with arms only for the variants live code builds, and the functions
  nothing reaches dropped (Lower/Live). Plain: every helper requested,
  with an arm for every variant. -/
  convLiveness : Bool := false
  /-- Whether the program text leaves out the runtime prelude's functions
  that the generated code does not reach by name (PreludePrune). Plain: the
  whole prelude. -/
  prunePrelude : Bool := false
  /-- The hooks of code lowering. -/
  lower : LowerHooks := {}
  /-- Passes over the generated Reussir functions (before the program text is
  assembled), in order. -/
  rrPasses : Array (RRProgram → Array RR.Item → Array RR.Item) := #[]

/-- An optional pass, registered by one line of Opt/Registry.lean: removing
the line removes the pass. `install` adds it to a configuration. -/
structure OptPass where
  name : String
  /-- Whether lean2rr runs it unless `--disable-opt NAME` is given. -/
  enabled : Bool
  description : String
  install : PassConfig → PassConfig

/-- A part of the translation that may look optional but is not, listed in
the registry with the reason. -/
structure RequiredPass where
  name : String
  description : String
  reason : String

end LeanToReussir
