import LeanToReussir.Lower.StateMachine

/-!
# Binders whose values only go into boxes

A field of a parameter's type is a `Box` in the record (one type per
inductive). An alternative binds it at its own type (`bindField`), so it
is unboxed once. When every use of the binder puts the value back into a
box (a field of a parameter's type, a `Box` parameter, a `Box` result, a
`Box` join-point parameter), the unboxing and each boxing again are wasted:
`List.reverseAux` at `String` unboxed each head to rebox it into the new
cell. Such a binder keeps the field's box (`CodeCtx.boxedOnly`): the box
is passed on unchanged, as natively, where the head is the same
`lean_object*` all along. A `let` whose value only goes into boxes and is
a box to start with (`letValueBoxed`: a projection of a box field, a call
whose callee returns a `Box`) is bound as a `Box` too (`lowerCode`).

The analysis is syntactic and conservative: a use that it does not know
to be boxed (a projection, a `cases`, an extern's argument, a closure's
argument, a capture by a local function) makes the binder keep its own
type, and lowering is then unchanged. A wrong guess only costs speed: a
binder bound as a `Box` is unboxed at a use that wants its own type.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- What the walk of `boxedOnlyVars` collects: the variables used in a boxed
position at least once, and those used anywhere else. -/
structure BoxedUses where
  boxed : Std.HashSet FVarId := {}
  other : Std.HashSet FVarId := {}
  /-- The join points in scope: which parameters they take (rule 4) and
  the Reussir types of those. -/
  jps : Std.HashMap FVarId (Array Bool × Array RR.Ty) := {}

namespace BoxedUses

def use (u : BoxedUses) (a : Arg .pure) (boxed : Bool) : BoxedUses :=
  match a with
  | .fvar x => if boxed then { u with boxed := u.boxed.insert x } else { u with other := u.other.insert x }
  | _ => u

def useAll (u : BoxedUses) (as : Array (Arg .pure)) : BoxedUses :=
  as.foldl (fun u a => u.use a false) u

def useVars (u : BoxedUses) (xs : Std.HashSet FVarId) : BoxedUses :=
  xs.fold (fun u x => { u with other := u.other.insert x }) u

end BoxedUses

/-- Which arguments of a call of declaration or extern `f` are boxed
positions, by position (`none`: a constructor, or another callee). For a
declaration: its `Box` parameters, except those it does not take (rule
4a), which no use reaches; for an extern: its `Box` parameters and those
declared at a type variable it stores in a `Box` (`Array.push`'s element:
`lowerExternCall` boxes it, and `tryCoerce` folds the unboxing and the
boxing), not `ptrAddrUnsafe`'s, which reads the variable's own
representation (`addrOf`), nor a refused extern's. Cached by callee. -/
def boxedArgMask (f : Name) : LowerM (Option (Array (Option Bool))) := do
  if let some m := (← get).boxedArgMasks.find? f then return some m
  match ← calleeOf f with
  | .code _ params _ keep =>
    -- `none` at a parameter the function does not take (not a use).
    let m := params.mapIdx fun i t => if keep[i]?.getD true then some (t == RR.Ty.box) else none
    modify fun s => { s with boxedArgMasks := s.boxedArgMasks.insert f m }
    return some m
  | .extern orig typeArgs params _ =>
    if (← read).externRefusals.contains orig || (← externSymbol orig) == "lean_ptr_addr" then
      let m := params.map fun _ => some false
      modify fun s => { s with boxedArgMasks := s.boxedArgMasks.insert f m }
      return some m
    let (uses, _) ← typeVarUses orig
    let inArrays ← typeVarsInArrays orig
    let mut acc := #[]
    for h : i in [:params.size] do
      -- (An array element is a box unless the array is compact,
      -- `arrayStorage`.)
      let atVar ← match uses[i]?.join with
        | some k =>
          match typeArgs[k]? with
          | some ta =>
            let mt ← toMonoTypeKeep ta
            if inArrays[k]?.getD false then pure ((← arrayStorage mt) == RR.Ty.box)
            else pure ((← lowerType mt) == RR.Ty.box)
          | none => pure (inArrays[k]?.getD false)
        | none => pure false
      acc := acc.push (atVar || (← lowerType params[i]) == RR.Ty.box)
    let m := acc.map some
    modify fun s => { s with boxedArgMasks := s.boxedArgMasks.insert f m }
    return some m
  | _ => return none

/-- The uses in `let _ : ty := v` (an application of a constant: the
arguments at `Box` parameters or fields are boxed uses). -/
def boxedUsesValue (u : BoxedUses) (v : LetValue .pure) (ty : Expr) : LowerM BoxedUses := do
  match v with
  | .const f _ args _ =>
    if args.size == 1 then
      if let some _ := (← read).preludeReplacements.find? (((← read).keys.find? f).map (·.decl) |>.getD f) then
        return u.useAll args
    if let some m ← boxedArgMask f then
      let mut u := u
      for h : i in [:args.size] do
        match m[i]? with
        | some (some b) => u := u.use args[i] b
        | some none => pure ()
        | none => u := u.use args[i] false
      return u
    match ← calleeOf f with
    | .ctor c =>
      let arity := c.numParams + c.numFields
      if args.size < arity then return u.useAll args
      let .named tn ← lowerType ty | return u.useAll args
      let some info := (← get).typeInfos[tn]? | return u.useAll args
      let some layout := info.ctors.find? c.name | return u.useAll args
      let mut u := u
      for h : i in [:args.size] do
        let a := args[i]
        if i < layout.numParams then u := u.use a false
        else match layout.fields[i - layout.numParams]? with
          | some (some (_, t)) => u := u.use a (t == RR.Ty.box)
          | _ => u := u.use a false
      return u
    | _ => return u.useAll args
  | .fvar g args => return (u.use (.fvar g) false).useAll args
  | .proj _ _ y _ => return u.use (.fvar y) false
  | _ => return u

/-- The walk of `boxedOnlyVars` over `c`, in a declaration whose result has
Reussir type `ret`. -/
partial def boxedUsesCode (ret : RR.Ty) (u : BoxedUses) (c : Code .pure) : LowerM BoxedUses := do
  match c with
  | .let d k => boxedUsesCode ret (← boxedUsesValue u d.value d.type) k
  | .fun d k _ =>
    -- A local function: what it captures is used in its body, whose
    -- results are not the declaration's.
    boxedUsesCode ret (u.useVars (codeUses d.value {})) k
  | .jp d k =>
    let keep := d.params.map fun p => !erasedDom p.type
    let tys ← ((d.params.zip keep).filter (·.2)).mapM fun (p, _) => lowerType p.type
    let u := { u with jps := u.jps.insert d.fvarId (keep, tys) }
    boxedUsesCode ret (← boxedUsesCode ret u d.value) k
  | .jmp j args =>
    let some (keep, tys) := u.jps[j]? | return u.useAll args
    let mut u := u
    let mut k := 0
    for h : i in [:args.size] do
      if keep[i]?.getD true then
        u := u.use args[i] (tys[k]? == some RR.Ty.box)
        k := k + 1
    return u
  | .cases cs =>
    let mut u := u.use (.fvar cs.discr) false
    for alt in cs.alts do u ← boxedUsesCode ret u alt.getCode
    return u
  | .return y => return u.use (.fvar y) (ret == RR.Ty.box)
  | .unreach _ => return u

/-- Whether the value `v` of a `let` is a `Box` before it is converted to
the binder's type (`lowerLetValue`): a projection of a `Box` field, a call
whose callee returns a `Box`, an extern whose result is a type variable it
stores in a `Box` (`Array.get!`'s element). A `let` that only goes into
boxes is bound as a `Box` only then (`lowerCode`): a value of its own type
(a constructor) would be boxed at its `let` instead of at its use, which
saves nothing and changes the order Reussir sees. -/
def letValueBoxed (ctx : CodeCtx) (v : LetValue .pure) : LowerM Bool := do
  match v with
  | .proj _ i x _ =>
    let some (_, .named tn) := ctx.vars[x]? | return false
    let some info := (← get).typeInfos[tn]? | return false
    let some layout := info.ctorOrder[0]?.bind info.ctors.find? | return false
    match layout.fields[i]? with
    | some (some (_, ft)) => return ft == RR.Ty.box
    | _ => return false
  | .const f _ args _ =>
    match ← calleeOf f with
    | .code _ params ret _ => return args.size == params.size && ret == RR.Ty.box
    | .extern orig typeArgs params ret =>
      if args.size != params.size then return false
      if (← lowerType ret) == RR.Ty.box then return true
      let (_, retUse) ← typeVarUses orig
      let some k := retUse | return false
      let inArrays := (← typeVarsInArrays orig)[k]?.getD false
      let some ta := typeArgs[k]? | return inArrays
      let mt ← toMonoTypeKeep ta
      if inArrays then return (← arrayStorage mt) == RR.Ty.box
      return (← lowerType mt) == RR.Ty.box
    | _ => return false
  | _ => return false

/-- The variables of declaration body `body` (result type `ret`) whose every
use is a boxed position (`CodeCtx.boxedOnly`). -/
def boxedOnlyVars (body : Code .pure) (ret : RR.Ty) : LowerM (Std.HashSet FVarId) := do
  let u ← boxedUsesCode ret {} body
  return u.boxed.fold (fun s x => if u.other.contains x then s else s.insert x) {}

end LeanToReussir
