import Lean
import LeanToReussir.ArrayKinds
import LeanToReussir.ErasedDomains

/-!
# Cell kinds of typed references (optimization `typed-cells`, clean step B2)

A reference (`ST.Ref σ X`) is a generated shared record around a Reussir
cell. Without the optimization the cell holds a `Box` whatever `X` is
(rule 1). With it, the cell holds `X`'s own Reussir type `T` when the
whole-program check (`TypedCells.lean`) allows `X`'s *cell kind*: the
record is then `L2RRef…(Cell<T>)`, one record type per `T`.

The cell kind of `X` names the Reussir type the lowering gives `X`, so that
two element types of one kind that can be one type (`List Nat` and
`List lcAny`) have one representation:

* `bool`, `u8`, `u16`, `u32`, `f32`: `Bool`, `UInt8`, `UInt16`, `UInt32`
  (and `Char`, whose mono type is `UInt32`), `Float32`, the scalars that a
  box holds as an immediate;
* `Nat`, `Int`, `LStr`: `Nat`, `Int`, `String` (a typed cell of `Nat`
  holds Reussir's owned handle, local patch R2);
* `I:<name>`: an inductive the lowering makes a shared record or enum
  (`sharedInductive?`, as for typed arrays);
* `A(<s>)`: an `Array Y`, where `s` is the storage of `Y` in the array as
  the program's array decisions make it (`compact-arrays`, `typed-arrays`):
  `Y`'s storage kind when it is compact, `Y`'s cell kind when its pointer
  kind is typed, `box` otherwise. So `Array Nat` and `Array lcAny` have one
  cell kind when the program's arrays of `Nat` hold boxes.

`UInt64`, `USize` and `Float` have no cell kind: their box allocates (a
`Float` always, a `UInt64` from 2^63), and a reference's `get` gives its
value in the `Box` field of the IO result (`ST.Out`), so a typed cell would
allocate at each read where the cell of boxes allocates at each store, as
natively. Enumerations, function types, thunks, tasks, references,
handles, `lcAny` and the types that are no inductive have none either.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The cell kind of mono type `t` (see the module comment), given the
storage kinds whose arrays are compact (`compactOn`) and the pointer kinds
whose arrays are typed (`typedOn`). `cache` is `ptrKind?`'s. -/
partial def cellKind? (cache : IO.Ref (Std.HashMap Name (Option String))) (compactOn : Array String)
    (typedOn : Std.HashSet String) (t : Expr) : CoreM (Option String) := do
  let t := t.consumeMData.headBeta
  if t.isForall then return none
  let .const n _ := t.getAppFn | return none
  match n with
  | ``Bool => return some "bool"
  | ``UInt8 => return some "u8"
  | ``UInt16 => return some "u16"
  | ``UInt32 => return some "u32"
  | ``Float32 => return some "f32"
  | ``UInt64 | ``USize | ``Float => return none
  | ``Nat => return some "Nat"
  | ``Int => return some "Int"
  | ``String => return some "LStr"
  | ``Array =>
    unless t.getAppNumArgs == 1 do return none
    -- The element's storage, as `arrayStorage` decides it.
    let e := t.appArg!
    let s ← match ← scalarKind? cache e with
      | some k => pure (if compactOn.contains k then k else "box")
      | none =>
        match ← ptrKind? cache e with
        | some k =>
          if typedOn.contains k then
            match ← cellKind? cache compactOn typedOn e with
            | some c => pure c
            | none => pure "box"
          else pure "box"
        | none => pure "box"
    return some s!"A({s})"
  | _ =>
    let ck := ptrKindCacheKey n
    if let some r := (← cache.get)[ck]? then return r
    let r := (← sharedInductive? n).map fun k => s!"I:{k}"
    cache.modify (·.insert ck r)
    return r

/-- Whether a reference of element type `a` and one of element type `b`
(mono types) can be one reference, as far as the types tell: they can be
one type up to `lcAny`. A type that `Box` represents (`lcAny`, a type whose
head is no inductive: a definition that unfolds to anything) can be any
type; two inductives of different names never are one type (`T` and its
implementation `T._impl` are one); a function type and an inductive are
not one type; arguments are compared in turn. Says `true` when unsure. -/
partial def cellTypesMeet (env : Environment) (a b : Expr) (fuel : Nat := 32) : Bool :=
  let a := keyTy a
  let b := keyTy b
  if a == b then true else
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    let wild (t : Expr) : Bool := t.isErased || (!t.isForall && mayBeBox env t)
    if wild a || wild b then true else
    match a, b with
    | .forallE .., .forallE .. => true
    | .forallE .., _ | _, .forallE .. => false
    | _, _ =>
      match a.getAppFn, b.getAppFn with
      | .const m _, .const n _ =>
        if !sameInductive m n then false
        else if a.getAppNumArgs != b.getAppNumArgs then true
        else (a.getAppArgs.zip b.getAppArgs).all fun (x, y) => cellTypesMeet env x y fuel'
      | _, _ => true

end LeanToReussir
