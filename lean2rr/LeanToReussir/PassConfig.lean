import Lean
import LeanToReussir.Pipeline
import LeanToReussir.Lower

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
  /-- Passes over the checked mono declarations (after Stage 3, before
  lowering), in order; they get the instance keys. -/
  monoPasses : Array (NameMap InstKey → Array (Decl .pure) → Array (Decl .pure)) := #[]
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
