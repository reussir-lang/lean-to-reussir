import Lean
import LeanToReussir.PassConfig
import LeanToReussir.Outline

/-!
# Array reads without the origin check (optimization `origin-free-reads`)

A structural conversion records the object it builds in the runtime's
origin table (`leanrt::origin`, translation plan §5.1), which holds a
reference to it. So the runtime's release of an array handle
(`leanrt::array::release`, used by every read of an array: `get`, `size`,
`uget`, …) checks whether a count of 2 means the program's last reference
plus the table's. That check sits on the shared-handle path, where LLVM
otherwise cancels a read's release against the caller's increment: the
classic Qsort runs 1.5 times slower with it.

A program none of whose functions calls `l2r_origin_note` records no
origins, so its arrays are never in the table. This pass then points the
prelude's array reads at `leanrt::array::release_unrecorded`, the plain
decrement. Without the pass (or when the program records origins) every
read checks; the results are the same.

Example: `qsortAux` reads `as[i]` and `as[j]` and swaps. Each read is
`l2r_array_get(v, i)`, an increment of `v` by the caller and a release in
the inlined runtime function; with this pass the pair disappears.
-/

namespace LeanToReussir
open RR

/-- The prelude function that records a conversion origin. -/
def Opt.OriginFreeReads.noteFn : String := "l2r_origin_note"

/-- Whether a generated function records a conversion origin. -/
def Opt.OriginFreeReads.recordsOrigins (fns : Array Item) : Bool :=
  fns.any fun
    | .fn _ _ _ body => (Outline.blockCalls body #[]).contains noteFn
    | .raw text => (text.splitOn noteFn).length > 1
    | _ => false

/-- The prelude with its array reads releasing without the origin check,
when `fns` record no origins. -/
def Opt.OriginFreeReads.edit (fns : Array Item) (prelude : String) : String :=
  if recordsOrigins fns then prelude
  else prelude.replace "leanrt::array::release(" "leanrt::array::release_unrecorded("

/-- Registry entry point. -/
def Opt.OriginFreeReads.install (c : PassConfig) : PassConfig :=
  { c with preludePasses := c.preludePasses.push edit }

end LeanToReussir
