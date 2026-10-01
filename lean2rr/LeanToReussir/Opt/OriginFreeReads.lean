import Lean
import LeanToReussir.PassConfig

/-!
# Array reads without the origin check (optimization `origin-free-reads`)

A structural conversion records the object it builds in the runtime's
origin table (`leanrt::origin`, translation plan §5.1), which holds a
reference to it. So the runtime's release of an array handle
(`leanrt::array::release`, used by every read of an array: `get`, `size`,
…) checks whether a count of 2 means the program's last reference plus the
table's. That check sits on the shared-handle path, where LLVM otherwise
cancels a read's release against the caller's increment: the classic Qsort
runs 1.5 times slower with it.

Only conversions whose result is an array (`l2r_origin_note<S, RVec<…>>`)
put arrays in the table. In a program with none (most programs: those that
convert only lists and other records, or nothing), no array is ever in the
table, and this pass points the prelude's array reads at
`leanrt::array::release_unrecorded`, the plain decrement. Without the pass,
or when the program converts to an array, every read checks; the results
are the same.

Example: `qsortAux` reads `as[i]` and `as[j]` and swaps. Each read is
`l2r_array_get(v, i)`, an increment of `v` by the caller and a release in
the inlined runtime function; with this pass the pair disappears.
-/

namespace LeanToReussir
open RR

/-- The prelude function that records a conversion origin. -/
def Opt.OriginFreeReads.noteFn : String := "l2r_origin_note"

mutual
  /-- Whether an expression records the origin of an array (a call of
  `l2r_origin_note` whose destination type is an `RVec`). -/
  partial def Opt.OriginFreeReads.exprNotesArray (e : Expr) : Bool :=
    match e with
    | .var _ | .atom _ => false
    | .call f tys args =>
      (f == noteFn && match (tys[1]? : Option Ty) with | some (Ty.app "RVec" _) => true | _ => false)
        || args.any exprNotesArray
    | .apply f x => exprNotesArray f || exprNotesArray x
    | .ctor _ _ args => args.any exprNotesArray
    | .field x _ | .cast x _ => exprNotesArray x
    | .lam _ _ b | .block b => blockNotesArray b
    | .ite c t f => exprNotesArray c || blockNotesArray t || blockNotesArray f
    | .mtch s arms => exprNotesArray s || arms.any (blockNotesArray ·.body)
  partial def Opt.OriginFreeReads.blockNotesArray (b : Block) : Bool :=
    b.lets.any (exprNotesArray ·.2.2) || exprNotesArray b.result
end

/-- Whether a generated function records the origin of an array. -/
def Opt.OriginFreeReads.recordsArrayOrigins (fns : Array Item) : Bool :=
  fns.any fun
    | .fn _ _ _ body => blockNotesArray body
    | .raw text => (text.splitOn noteFn).length > 1
    | _ => false

/-- The prelude with its array reads releasing without the origin check,
when `fns` record no array origins. -/
def Opt.OriginFreeReads.edit (fns : Array Item) (prelude : String) : String :=
  if recordsArrayOrigins fns then prelude
  else prelude.replace "leanrt::array::release(" "leanrt::array::release_unrecorded("

/-- Registry entry point. -/
def Opt.OriginFreeReads.install (c : PassConfig) : PassConfig :=
  { c with preludePasses := c.preludePasses.push edit }

end LeanToReussir
