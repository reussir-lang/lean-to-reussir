import LeanToReussir.Lower.FnValues

/-!
# Live helpers (optimization `conv-liveness`)

The helpers generated at the end of Stage 4 match variants: an unboxing
function (`l2r_unbox_…`) has an arm per `Box` variant that can hold a value
of its type, an application function (`l2r_ap<j>_…`) an arm per variant of
its function type, a conversion of function values (`l2r_fconv_S_T`) an arm
per wrapped representation of its source, a reference dispatch
(`l2r_refbox_…`) an arm per boxed reference type. Without this pass every
helper requested anywhere is generated, with an arm for every variant
registered anywhere, and each arm converts (`tryCoerce`), which requests
more helpers and registers more variants. In a program that can cast
(`programCasts`), every unboxing function also gets a cast arm for every
variant of a compatible layout, so the helpers grow quadratically: on a
program importing a large library, 95 % of the functions were helpers that
can never run.

With the pass, the helpers follow a type-based reachability (rapid type
analysis), computed here while they are generated (`Finish.finishLive`):
- the roots are the identifiers of raw text (the entry point, the startup
  chain, the trampolines the runtime calls: `l2r_init_body`,
  `l2r_main_body`, `l2r_stderr_put`, `l2r_task_run_one`, `l2r_task_walk`,
  `l2r_promise_drop`) and of the prelude;
- a function reached is looked at (`liveFollow`): the functions it calls and
  the identifiers of its atoms are reached, and the variants of `Box` and of
  function-value enums it builds are *made*;
- a helper is generated only once reached, with arms only for the variants
  made (an unbuilt variant reaches no helper: no value of it exists), and
  generated again when a variant it matches is made;
- until nothing changes; then the functions not reached are dropped
  (`liveDrop`).

The `Box` enum and the function-value enums keep every variant registered:
only arms and functions go. Every other match (persist walks, typed code's
own unboxing in line) keeps all its arms, and every arm of a function
reached counts. A variant that only text names (raw items, atoms) counts as
made. A removed arm matches a variant no running code builds, so the program
computes the same results; an extern that only a removed arm would call is
not reported as missing. Without the pass, every helper requested is
generated with every arm.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- What liveness follows in a function body or a text: names (functions
called; the identifiers of atoms and raw text) and the variants of `Box`
and of function-value enums built (`made`: enum name, variant name). -/
structure LiveRefs where
  names : Array String := #[]
  made : Array (String × String) := #[]

/-- The enums whose variants liveness tracks: `Box` and the enums of
function values. -/
def liveTracked (ty : String) : Bool := ty == boxName || ty.startsWith "L2RFn_"

/-- The identifiers of text `t` (raw items, atoms) as names, and every
`T::v` of a tracked enum (built or matched: both count as built). A
number's letters (`0x1f`, `1u64`) are not names. -/
def textRefs (t : String) (r : LiveRefs) : LiveRefs := Id.run do
  let b := t.toUTF8
  let isStart (c : UInt8) : Bool := (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95
  let isCont (c : UInt8) : Bool := isStart c || (c ≥ 48 && c ≤ 57)
  let mut r := r
  let mut i := 0
  let mut prev : Option String := none
  while i < b.size do
    let c := b[i]!
    if isStart c then
      let mut id := ""
      while i < b.size && isCont b[i]! do
        id := id.push (Char.ofNat b[i]!.toNat)
        i := i + 1
      if let some ty := prev then
        if liveTracked ty then r := { r with made := r.made.push (ty, id) }
      r := { r with names := r.names.push id }
      if i + 1 < b.size && b[i]! == 58 && b[i + 1]! == 58 then
        prev := some id
        i := i + 2
      else
        prev := none
    else if c ≥ 48 && c ≤ 57 then
      while i < b.size && isCont b[i]! do i := i + 1
      prev := none
    else
      i := i + 1
      prev := none
  return r

mutual
  /-- `textRefs` of a function body: the functions called, the identifiers
  of its atoms, and the tracked variants it builds. -/
  partial def exprRefs (e : RR.Expr) (r : LiveRefs) : LiveRefs :=
    match e with
    | .var _ => r
    | .atom t => if t.any (fun c => c.isAlpha || c == '_') then textRefs t r else r
    | .call f _ args => args.foldl (fun r a => exprRefs a r) { r with names := r.names.push f }
    | .apply f a => exprRefs a (exprRefs f r)
    | .ctor ty v args =>
      let r := match v with
        | some v => if liveTracked ty then { r with made := r.made.push (ty, v) } else r
        | none => r
      args.foldl (fun r a => exprRefs a r) r
    | .field e _ => exprRefs e r
    | .cast e _ => exprRefs e r
    | .lam _ _ b => blockRefs b r
    | .block b => blockRefs b r
    | .ite c t e => blockRefs e (blockRefs t (exprRefs c r))
    | .mtch s arms => arms.foldl (fun r a => blockRefs a.body r) (exprRefs s r)
  partial def blockRefs (b : RR.Block) (r : LiveRefs) : LiveRefs :=
    exprRefs b.result (b.lets.foldl (fun r (_, _, e) => exprRefs e r) r)
end

/-- `refs` reached: their names (not the prelude's functions, `pre`) and
made variants recorded in `lv`. -/
def LiveState.add (lv : LiveState) (pre : Std.HashSet String) (refs : LiveRefs) : LiveState := Id.run do
  let mut lv := lv
  for n in refs.names do
    if pre.contains n || lv.names.contains n then continue
    lv := { lv with names := lv.names.insert n, work := lv.work.push n }
    if let some h := lv.helperOf[n]? then lv := { lv with helpers := lv.helpers.push (n, h) }
  for (ty, v) in refs.made do
    if ty == boxName then
      lv := { lv with madeBox := lv.madeBox.insert v }
    else if !lv.madeFn.contains (ty, v) then
      lv := { lv with madeFn := lv.madeFn.insert (ty, v),
                      madeFnCount := lv.madeFnCount.insert ty (lv.madeFnCount.getD ty 0 + 1) }
  return lv

/-- A helper requested (`name`): indexed, and live if it was reached. -/
def LiveState.request (lv : LiveState) (name : String) (h : LiveHelper) : LiveState :=
  if lv.helperOf.contains name then lv else
  let lv := { lv with helperOf := lv.helperOf.insert name h }
  if lv.names.contains name then { lv with helpers := lv.helpers.push (name, h) } else lv

/-- Text `t` (the prelude) taken as roots. -/
def liveRootText (t : String) : LowerM Unit := do
  let pre := (← read).preludeFns
  let lv ← modifyGet fun s => (s.live, { s with live := {} })
  let lv := lv.add pre (textRefs t {})
  modify fun s => { s with live := lv }

/-- Bring liveness up to date with the functions emitted so far: index the
helpers requested since the last call; look at the items emitted since
(a function's new version if it is live, every raw item); then follow the
names reached until none is left (a name without a function yet is looked
at when its function is emitted). -/
def liveFollow : LowerM Unit := do
  syncFnIndex
  let pre := (← read).preludeFns
  let unboxTs ← getPart (·.unboxTargets)
  let arrTs ← getPart (·.unboxArrTargets)
  let fnTs ← getPart (·.fnUnboxTargets)
  let applies ← getPart (·.fnApplies)
  let convs ← getPart (·.fnConvs)
  let refOps ← getPart (·.refBoxOps)
  let fns ← getPart (·.fns)
  let pos ← getPart (·.fnPos)
  let mut lv ← modifyGet fun s => (s.live, { s with live := {} })
  -- The helpers requested since the last call.
  let ix := lv.indexed
  for t in unboxTs[ix[0]!:] do lv := lv.request s!"l2r_unbox_{t}" (.unbox (.named t))
  for (t, f) in arrTs[ix[1]!:] do lv := lv.request f (.unbox t)
  for t in fnTs[ix[2]!:] do lv := lv.request s!"l2r_unbox_fn_{t.enc}" (.unbox t)
  for (t, j) in applies[ix[3]!:] do lv := lv.request (applyFnName t j) (.apply t j)
  for (src, dst) in convs[ix[4]!:] do lv := lv.request s!"l2r_fconv_{src.enc}_{dst.enc}" (.fconv src dst)
  for (op, a) in refOps[ix[5]!:] do
    lv := lv.request (if op == "addr" then "l2r_refbox_addr" else s!"l2r_refbox_{op}_{a.enc}") (.refbox op a)
  lv := { lv with indexed := #[unboxTs.size, arrTs.size, fnTs.size, applies.size, convs.size, refOps.size] }
  -- The items emitted since the last call.
  for h : i in [lv.seen:fns.size] do
    match fns[i]'h.upper with
    | .fn n .. => if lv.names.contains n then lv := { lv with work := lv.work.push n }
    | .raw t => unless t.isEmpty do lv := lv.add pre (textRefs t {})
    | _ => pure ()
  lv := { lv with seen := fns.size }
  -- The names reached, each looked up once per call.
  let mut done : Std.HashSet String := {}
  while h : lv.work.size > 0 do
    let n := lv.work[lv.work.size - 1]
    lv := { lv with work := lv.work.pop }
    if done.contains n then continue
    done := done.insert n
    let some i := pos[n]? | continue
    let some (.fn _ _ _ body) := fns[i]? | continue
    lv := lv.add pre (blockRefs body {})
  modify fun s => { s with live := lv }

/-- Whether `conv-liveness` leaves out the arm of `Box` variant `v`: no live
code builds it. -/
def liveSkipBox (v : String) : LowerM Bool := do
  unless (← read).convLiveness do return false
  return !(← getPart (·.live.madeBox.contains v))

/-- Whether `conv-liveness` leaves out the arm of variant `v` of function
type `t`: no live code builds it. -/
def liveSkipFn (t : RR.Ty) (v : FnVariant) : LowerM Bool := do
  unless (← read).convLiveness do return false
  return !(← getPart (·.live.madeFn.contains (RR.fnTypeName t, fnVariantName v)))

/-- The version a live helper's body is generated for: the number of
variants it can match that live code builds. -/
def liveVersion (h : LiveHelper) : LowerM Nat := do
  match h with
  | .unbox _ | .refbox .. => getPart (·.live.madeBox.size)
  | .apply t _ | .fconv t _ =>
    let tn := RR.fnTypeName t
    getPart (·.live.madeFnCount.getD tn 0)

/-- `fns` without the functions liveness did not reach (raw items stay). -/
def liveDrop (st : LowerState) : Array RR.Item :=
  st.fns.filter fun | .fn n .. => st.live.names.contains n | _ => true

end LeanToReussir
