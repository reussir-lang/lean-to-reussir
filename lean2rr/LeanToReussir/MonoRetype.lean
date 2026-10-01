import Lean
import LeanToReussir.MonoTypesKeep
import LeanToReussir.Relevance
import LeanToReussir.Mono
import LeanToReussir.Pipeline

/-!
# Stage 3: exact recovery of types lost in mono

Lean's mono code can type a binder `lcAny` although the value has one
precise type (translation plan §4):

* types inferred during the passes go through erased signatures — a
  constructor's mono type is `List.cons : lcAny → List lcAny → List lcAny`,
  so `structProjCases` may produce `cases p | Prod.mk (fst : lcAny) …` for
  an exactly typed `p`, and lambda lifting may give the lifted function the
  result type `lcAny`;
* library code that relies on the uniform representation (§2.7) casts with
  `unsafeCast`, which LCNF erases: the result of `Array.map` is bound at
  `Array NonScalar`, i.e. `Array lcAny`, and so is every loop parameter it is
  passed to.

A binder typed `lcAny` is represented by `Box`, and every use at a precise
type converts it; an array converts element by element, so a loop reading a
loop-invariant `Array lcAny` would convert the whole array per access. This
pass recomputes binder types where the program determines them, iterating
over the whole program to a fixpoint (translation plan §4). A type is taken
from what flows into a binder, never from how it is used: with a type that
depends on a value (`data : Array t.denote`), a use as `Array Nat` speaks
only for the branch where `t = .nat`.

* **from definitions**: a `cases` field gets its constructor's field type at
  the discriminant's type arguments; a constructor application, a projection,
  a call (full or partial) gets the type its callee's signature gives; a
  join-point parameter gets the type of its jump arguments, if all are known
  and agree;
* **result types**: a declaration whose result is `lcAny` gets the type all
  its `return`s have, or the type all its callers bind the result at (if it
  is used nowhere else); a `map` loop of `Array.mapMUnsafe` or
  `Array.mapFinIdxMUnsafe` returns `Array β` when every value it stores has
  type `β`;
* **parameters from callers**: a parameter holding an erased array that
  every caller passes at the same precise type `T` gets `T` when the body,
  retyped under that assumption, passes `T` back in its self calls (this
  makes the `map` loop precise when the source and target element types
  agree, e.g. `xs.map (· * 2)`);
* **externs**: a call of a polymorphic extern instantiated at `lcAny`
  (`Array.uget`/`Array.uset` at `NonScalar`) whose arguments determine the
  type arguments is redirected to the extern's instance at those types;
* **placeholders**: `let z := ◾` gets the type its uses expect.

Whatever stays unknown keeps `lcAny` and is represented by the uniform `Box`
in Stage 4.
-/

namespace LeanToReussir
open Lean Compiler LCNF

abbrev Types := Std.HashMap FVarId Expr

def isUnknown (table : RelevanceTable) (t : Expr) : Bool := hasRelevantAny table t

/-- Do `a` and `b` have the same head constant (universe levels ignored)? -/
def sameHead (a b : Expr) : Bool :=
  match a, b with
  | .const m _, .const n _ => m == n
  | _, _ => a == b

/-- First-order matching of `pat` against `target`, where the placeholder
free variables `holes` stand for unknown inductive parameters; records
their assignments. -/
partial def matchTy (holes : Array FVarId) (pat target : Expr) (assign : Array (Option Expr))
    (strict : Bool := false) : Array (Option Expr) :=
  let pat := pat.consumeMData
  let target := target.consumeMData
  match pat with
  | .fvar id =>
    match holes.idxOf? id with
    | some i =>
      match assign[i]! with
      -- `strict`: an argument whose type leaves the parameter unknown
      -- (`lcAny`) may hold values of any representation (uniform code,
      -- `unsafeCast`), so the parameter is not determined either.
      | none =>
        if target.isErased then assign
        else if target == anyExpr then (if strict then assign.set! i (some anyExpr) else assign)
        else assign.set! i (some target)
      -- Two arguments disagree about the parameter (`List.cons` of an
      -- `α × Nat` onto a list of `α × String`, as `unsafeCast` can make
      -- them): it is not determined (`lcAny` marks the conflict).
      | some a =>
        if target.isErased || a == target then assign
        else if target == anyExpr && !strict then assign
        else assign.set! i (some anyExpr)
    | none => assign
  | .app .. =>
    if target.isApp && sameHead pat.getAppFn target.getAppFn && pat.getAppNumArgs == target.getAppNumArgs then
      (pat.getAppArgs.zip target.getAppArgs).foldl (fun a (p, t) => matchTy holes p t a strict) assign
    else assign
  | .forallE _ d b _ =>
    match target with
    | .forallE _ d' b' _ => matchTy holes b b' (matchTy holes d d' assign strict) strict
    | _ => assign
  | _ => assign

/-- A type for comparisons: no metadata, no universe levels, and `◾` at the
arguments of irrelevant (phantom) parameters, which do not change the
representation. -/
partial def normTy (table : RelevanceTable) (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE n d b bi => .forallE n (normTy table d) (normTy table b) bi
  | e@(.app ..) =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let args := match f with
      | .const n _ =>
        match table.find? n with
        | some rel => args.mapIdx fun i a => if rel.getD i true then normTy table a else erasedExpr
        | none => args.map (normTy table)
      | _ => args.map (normTy table)
    mkAppN (normTy table f) args
  | .const n _ => .const n []
  | e => e

/-- Is `new` a refinement of `old`: equal, except that `lcAny` in `old` may
stand for anything? (Both normalized with `normTy`.) -/
partial def refines (old new : Expr) : Bool :=
  if old == anyExpr then true
  else match old, new with
    | .forallE _ d b _, .forallE _ d' b' _ => refines d d' && refines b b'
    | .app .., .app .. =>
      sameHead old.getAppFn new.getAppFn && old.getAppNumArgs == new.getAppNumArgs &&
        (old.getAppArgs.zip new.getAppArgs).all fun (a, b) => refines a b
    | _, _ => old == new

/-- Field types (mono) of constructor `ctor` at inductive arguments `args`. -/
def ctorFieldTypes (ctor : Name) (args : Array Expr) : CoreM (Array Expr) := do
  let some (.ctorInfo c) := (← getEnv).find? ctor | return #[]
  let mut ty ← instantiateForall (← getOtherDeclBaseType ctor []) args[:c.numParams].toArray
  let mut out := #[]
  repeat
    match ty.headBeta with
    | .forallE _ d b _ =>
      out := out.push (← toMonoTypeKeep d)
      ty := b.instantiate1 anyExpr
    | _ => break
  return out

/-- The mono type of a constructor application with argument types `argTys`
(parameters first, then fields), when matching determines it. A parameter
that no field determines (the error type of `EST.Out.ok`) is taken from
`known`, the type the binder already has, if it is an application of the
same inductive. -/
def ctorAppType (ctor : Name) (argTys : Array Expr) (known : Option Expr := none) : CoreM (Option Expr) := do
  let some (.ctorInfo c) := (← getEnv).find? ctor | return none
  let holes ← (List.range c.numParams).toArray.mapM fun _ => mkFreshFVarId
  let mut ty ← instantiateForall (← getOtherDeclBaseType ctor []) (holes.map .fvar)
  let mut assign : Array (Option Expr) := Array.replicate c.numParams none
  let mut i := c.numParams
  repeat
    match ty.headBeta with
    | .forallE _ d b _ =>
      if let some argTy := argTys[i]? then
        assign := matchTy holes d argTy assign (strict := true)
      ty := b.instantiate1 anyExpr
      i := i + 1
    | _ => break
  if let some k := known then
    let k := k.consumeMData.headBeta
    if sameHead k.getAppFn (.const c.induct []) && k.getAppNumArgs == c.numParams then
      assign := assign.zipIdx.map fun (a, i) => a <|> some k.getAppArgs[i]!
  if assign.any (fun a => a.isNone || a == some anyExpr) then return none
  let indTy := mkAppN (.const c.induct []) (assign.map Option.get!)
  return some (← toMonoTypeKeep indTy)

/-! ## Signatures and state -/

/-- Parameter and result types of a declaration. -/
structure Sig where
  params : Array Expr
  ret : Expr

/-- The first `n` parameter types of a function type and the rest. -/
def splitArrows (ty : Expr) (n : Nat) : Array Expr × Expr := Id.run do
  let mut ty := ty
  let mut ps := #[]
  for _ in [:n] do
    match ty.consumeMData with
    | .forallE _ d b _ => ps := ps.push d; ty := b.instantiate1 anyExpr
    | _ => break
  return (ps, ty)

def declSig (d : Decl .pure) : Sig :=
  { params := d.params.map (·.type), ret := (splitArrows d.type d.params.size).2 }

/-- Rebuild a declaration's type from its parameters and result type. -/
def withSig (d : Decl .pure) (params : Array (Param .pure)) (ret : Expr) : Decl .pure :=
  { d with params, type := params.foldr (fun p acc => .forallE p.binderName p.type acc .default) ret }

structure MRetypeCtx where
  table : RelevanceTable
  /-- Stage 2's pass lists (extern instances are built as Stage 2 builds them). -/
  stage2 : Stage2Config

structure MRetypeState where
  /-- Current signatures of the program's declarations and extern instances. -/
  sigs : Std.HashMap Name Sig := {}
  /-- Declarations with code. -/
  codeDecls : NameSet := {}
  /-- Declarations with code reachable from the program's roots (only their
  call sites say what a parameter receives). -/
  live : NameSet := {}
  keys : NameMap InstKey := {}
  /-- Extern instances by (extern, type arguments). -/
  instances : Std.HashMap (Name × Array Expr) Name := {}
  /-- Extern instances created by this pass. -/
  newExterns : Array (Decl .pure) := #[]
  nextInst : Nat := 0
  /-- Split `map` loops (see `splitMapLoops`): (loop, source and target
  element types, normalized) ↦ the split instance, `none` if the loop
  cannot be split. -/
  splits : Std.HashMap (Name × Expr × Expr) (Option Name) := {}
  /-- Split instances being built. -/
  splitBusy : NameSet := {}
  /-- Split instances built. -/
  splitDecls : Array (Decl .pure) := #[]

abbrev MRetypeM := ReaderT MRetypeCtx (StateRefT MRetypeState CoreM)

def unknown (t : Expr) : MRetypeM Bool := return isUnknown (← read).table t
def norm (t : Expr) : MRetypeM Expr := return normTy (← read).table t

/-- What the traversal knows about the binders in scope. -/
structure Scope where
  types : Types := {}
  /-- Variables bound to `◾`: placeholders, which fit any type. -/
  erased : FVarIdSet := {}

def Scope.argTy (sc : Scope) : Arg .pure → Expr
  | .fvar x => sc.types.getD x anyExpr
  | _ => erasedExpr

def Scope.isPlaceholder (sc : Scope) : Arg .pure → Bool
  | .fvar x => sc.erased.contains x
  | _ => true

/-! ## Extern re-instantiation -/

/-- The instance of extern `orig` (base declaration `base`) at `typeArgs`:
an existing one, or a new one built like Stage 1 and Stage 2 build extern
instances. -/
def externInstance (orig : Name) (base : Decl .pure) (typeArgs : Array Expr) : MRetypeM Name := do
  if let some n := (← get).instances[(orig, typeArgs)]? then return n
  let k := (← get).nextInst
  let name := Name.num (orig ++ `_l2r_re) k
  let passes ← stage2Passes (← read).stage2
  let decl ← CompilerM.run (phase := .base) do
    let d ← instantiateExtern base name typeArgs
    let out ← runPasses passes.toMono #[uniformDecl d] false
    return out[0]!
  modify fun s => { s with
    nextInst := k + 1
    instances := s.instances.insert (orig, typeArgs) name
    sigs := s.sigs.insert name (declSig decl)
    keys := s.keys.insert name { decl := orig, typeArgs }
    newExterns := s.newExterns.push decl }
  return name

/-- A saturated call of `f`, an extern instance whose type arguments Lean did
not know (`lcAny`, e.g. `Array.uget` at `NonScalar` inside `Array.map`): the
instance of the same extern at the type arguments that the argument types
determine, provided every argument then has exactly the expected type (or is
a placeholder). An extern does not depend on its type arguments; only the
representation changes. -/
def reinstantiate? (sc : Scope) (f : Name) (args : Array (Arg .pure)) (resTy : Expr) :
    MRetypeM (Option Name) := do
  let some key := (← get).keys.find? f | return none
  unless key.dicts.isEmpty && key.typeArgs.any (· == anyExpr) do return none
  let some base ← getBaseDecl? key.decl | return none
  let positions := typeParamPositions base
  -- Saturated, or over-applied (the element read of an `Array.map` over
  -- functions is applied to the function's argument).
  let n := base.params.size
  unless positions.size == key.typeArgs.size && n ≤ args.size do return none
  let holes ← positions.mapM fun _ => mkFreshFVarId
  let mut assign : Array (Option Expr) := Array.replicate holes.size none
  let mut ty := eraseLevels base.type
  for h : i in [:n] do
    match ty.headBeta with
    | .forallE _ d b _ =>
      match positions.idxOf? i with
      | some j => ty := b.instantiate1 (.fvar holes[j]!)
      | none =>
        unless sc.isPlaceholder args[i]! do
          assign := matchTy holes d (sc.argTy args[i]!) assign
        ty := b.instantiate1 anyExpr
    | _ => return none
  let some typeArgs := assign.mapM id | return none
  for t in typeArgs do
    if (← unknown t) || t.hasFVar then return none
  let inst ← externInstance key.decl base (typeArgs.map eraseLevels)
  if inst == f then return none
  let some sig := (← get).sigs[inst]? | return none
  for h : i in [:n] do
    let p := sig.params[i]!.consumeMData
    if p.isErased || p.isSort || p == mkConst ``lcVoid then continue
    if sc.isPlaceholder args[i]! then continue
    if (← norm (sc.argTy args[i]!)) != (← norm p) then return none
  -- The result after the extra arguments, if any.
  let mut ret := sig.ret
  for _ in [n:args.size] do
    match ret.consumeMData with
    | .forallE _ _ b _ => ret := b.instantiate1 anyExpr
    | _ => return none
  -- A binder that already has a precise type keeps it; the instance must
  -- produce exactly that.
  unless (← unknown resTy) || (← norm resTy) == (← norm ret) do return none
  return some inst

/-! ## Retyping from definitions -/

/-- Refine `old` to `new` if `new` is precise and refines it. -/
def refineTo? (old : Expr) (new : Option Expr) : MRetypeM (Option Expr) := do
  let some new := new | return none
  if !(← unknown old) || (← unknown new) then return none
  if refines (← norm old) (← norm new) then return some new else return none

/-- The type of `f` applied to `n` arguments, from its signature. -/
def appType? (sig : Sig) (n : Nat) : Option Expr :=
  if n == sig.params.size then some sig.ret
  else if n < sig.params.size then
    some (sig.params[n:].toArray.foldr (fun d acc => .forallE `_ d acc .default) sig.ret)
  else none

/-- The type of a function value of type `t` applied to `n` arguments. -/
def applyType? (t : Expr) : Nat → Option Expr
  | 0 => some t
  | n + 1 => match t.consumeMData with
    | .forallE _ _ b _ => applyType? (b.instantiate1 anyExpr) n
    | _ => none

/-- Is `t` an array type? -/
def isArrayTy (t : Expr) : Bool := t.consumeMData.headBeta.isAppOf ``Array

partial def fwdCode (sc : Scope) : Code .pure → StateT Bool MRetypeM (Code .pure × Scope)
  | .let d k => do
    let mut d := d
    if let .const f us args h := d.value then
      if let some inst ← reinstantiate? sc f args d.type then
        d := { d with value := .const inst us args h }
        set true
    if ← unknown d.type then
      let candidate ← match d.value with
        | .const f _ args _ =>
          if (← getEnv).isConstructor f then ctorAppType f (args.map sc.argTy) d.type
          else pure (((← getThe MRetypeState).sigs[f]?).bind (appType? · args.size))
        | .proj s i x _ =>
          match sc.types[x]? with
          | some st =>
            let st := st.consumeMData.headBeta
            let some (.inductInfo iv) := (← getEnv).find? s | pure none
            let fs ← ctorFieldTypes iv.ctors[0]! st.getAppArgs
            pure fs[i]?
          | none => pure none
        | .fvar g args => pure ((sc.types[g]?).bind (applyType? · args.size))
        | _ => pure none
      if let some t ← refineTo? d.type candidate then
        d := { d with type := t }
        set true
    let erased := if d.value matches .erased then sc.erased.insert d.fvarId else sc.erased
    let (k, sc) ← fwdCode { types := sc.types.insert d.fvarId d.type, erased } k
    return (.let d k, sc)
  | .jp d k => do
    -- Scope first, to learn the jump argument types.
    let (k, sc) ← fwdCode sc k
    let mut params := d.params
    for i in [:params.size] do
      let p := params[i]!
      if ← unknown p.type then
        let cands := jumpArgTypes d.fvarId k i sc.types #[]
        let mut known := #[]
        for t in cands do
          unless ← unknown t do known := known.push (← norm t, t)
        -- Every argument must be known: with a type that depends on a value
        -- (`Array t.denote`), jumps from different branches pass different
        -- types, and an argument typed `lcAny` may have any of them.
        if let some (n, t) := known[0]? then
          if known.size == cands.size && known.all (·.1 == n) then
            if let some t ← refineTo? p.type (some t) then
              params := params.set! i { p with type := t }
              set true
    let sc := { sc with types := params.foldl (fun m p => m.insert p.fvarId p.type) sc.types }
    let (value, sc) ← fwdCode sc d.value
    return (.jp (FunDecl.mk d.fvarId d.binderName params d.type value) k, sc)
  | .fun d k _ => do
    let sc := { sc with types := d.params.foldl (fun m p => m.insert p.fvarId p.type) sc.types }
    let (value, sc) ← fwdCode sc d.value
    let sc := { sc with types := sc.types.insert d.fvarId d.type }
    let (k, sc) ← fwdCode sc k
    return (.fun (FunDecl.mk d.fvarId d.binderName d.params d.type value) k, sc)
  | .cases cs => do
    let discrTy := (sc.types.getD cs.discr anyExpr).consumeMData.headBeta
    let mut sc := sc
    let mut alts := #[]
    for alt in cs.alts do
      match alt with
      | .alt ctor ps code _ =>
        let mut ps := ps
        let mut anyUnknown := false
        for p in ps do
          if ← unknown p.type then anyUnknown := true
        if anyUnknown && discrTy.getAppFn.isConst then
          let fs ← ctorFieldTypes ctor discrTy.getAppArgs
          for i in [:ps.size] do
            let p := ps[i]!
            if let some t ← refineTo? p.type fs[i]? then
              ps := ps.set! i { p with type := t }
              set true
        sc := { sc with types := ps.foldl (fun m p => m.insert p.fvarId p.type) sc.types }
        let (code, sc') ← fwdCode sc code
        sc := sc'
        alts := alts.push (.alt ctor ps code)
      | .default code =>
        let (code, sc') ← fwdCode sc code
        sc := sc'
        alts := alts.push (.default code)
      | other => alts := alts.push other
    return (.cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩, sc)
  | c => return (c, sc)
where
  jumpArgTypes (j : FVarId) (c : Code .pure) (i : Nat) (types : Types) (acc : Array Expr) : Array Expr :=
    match c with
    | .jmp j' args =>
      if j' == j then
        match args[i]? with
        | some (.fvar x) => acc.push (types.getD x anyExpr)
        | _ => acc
      else acc
    | .let _ k => jumpArgTypes j k i types acc
    | .fun d k _ | .jp d k => jumpArgTypes j k i types (jumpArgTypes j d.value i types acc)
    | .cases cs => cs.alts.foldl (fun acc alt => jumpArgTypes j alt.getCode i types acc) acc
    | _ => acc

/-! ## Placeholders from uses

A binder of a value is only retyped from its definition: a use at a precise
type in one branch says nothing about the other paths. With a type that
depends on a value (`data : Array t.denote`, used as `Array Nat` only in the
branch where `t = .nat`), a conversion moved from the use to the definition
would run, and fail, on the other paths. The exception is a placeholder
`let z := ◾`, which has no value to convert and fits any type. -/

abbrev Uses := Std.HashMap FVarId (Array Expr)

/-- The precise types that the uses of each variable expect: arguments of
calls (from the callee's signature) and of constructors (from the field
types), jump arguments (the join point's parameter types), and closure
arguments. Arguments of self calls (of `self`) at positions `skip` are not
counted: those parameter types are assumptions being checked
(`paramsFromCallers`). -/
partial def collectUses (types : Types) (jps : Std.HashMap FVarId (Array Expr))
    (c : Code .pure) (acc : Uses) (self : Name := .anonymous) (skip : Array Nat := #[]) :
    MRetypeM Uses := do
  let add (acc : Uses) (a : Arg .pure) (t : Expr) : MRetypeM Uses := do
    let .fvar x := a | return acc
    if ← unknown t then return acc
    return acc.insert x ((acc.getD x #[]).push t)
  match c with
  | .let d k =>
    let mut acc := acc
    match d.value with
    | .const f _ args _ =>
      if let some (.ctorInfo ci) := (← getEnv).find? f then
        let ty := d.type.consumeMData.headBeta
        if sameHead ty.getAppFn (.const ci.induct []) then
          let fs ← ctorFieldTypes f ty.getAppArgs
          for h : i in [:args.size] do
            if i ≥ ci.numParams then
              if let some t := fs[i - ci.numParams]? then acc ← add acc args[i] t
      else if let some sig := (← get).sigs[f]? then
        for i in [:min args.size sig.params.size] do
          unless f == self && skip.contains i do
            acc ← add acc args[i]! sig.params[i]!
    | .fvar g args =>
      let mut t := types.getD g anyExpr
      for a in args do
        match t.consumeMData with
        | .forallE _ dom b _ => acc ← add acc a dom; t := b.instantiate1 anyExpr
        | _ => break
    | _ => pure ()
    collectUses types jps k acc self skip
  | .jp d k =>
    let jps := jps.insert d.fvarId (d.params.map (·.type))
    collectUses types jps k (← collectUses types jps d.value acc self skip) self skip
  | .fun _ k _ => collectUses types jps k acc self skip
  | .cases cs => cs.alts.foldlM (fun acc alt => collectUses types jps alt.getCode acc self skip) acc
  | .jmp j args =>
    let some ps := jps[j]? | return acc
    let mut acc := acc
    for i in [:min args.size ps.size] do acc ← add acc args[i]! ps[i]!
    return acc
  | _ => return acc

/-- The type all precise uses of `x` agree on, if it refines `old`. -/
def fromUses (uses : Uses) (x : FVarId) (old : Expr) : MRetypeM (Option Expr) := do
  let cands := uses.getD x #[]
  let some t := cands[0]? | return none
  let n ← norm t
  for c in cands do
    if (← norm c) != n then return none
  refineTo? old (some t)

partial def bwdCode (uses : Uses) : Code .pure → StateT Bool MRetypeM (Code .pure)
  | .let d k => do
    let mut d := d
    if d.value matches .erased then
      if let some t ← fromUses uses d.fvarId d.type then
        d := { d with type := t }
        set true
    return .let d (← bwdCode uses k)
  | .jp d k => do
    let value ← bwdCode uses d.value
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type value) (← bwdCode uses k)
  | .fun d k _ => do
    let value ← bwdCode uses d.value
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type value) (← bwdCode uses k)
  | .cases cs => do
    let alts ← cs.alts.mapM fun
      | .alt ctor ps code _ => return .alt ctor ps (← bwdCode uses code)
      | .default code => return .default (← bwdCode uses code)
      | other => return other
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c

/-! ## Declarations -/

def paramScope (d : Decl .pure) : Scope :=
  { types := d.params.foldl (fun m p => m.insert p.fvarId p.type) {} }

/-- Retype the body of a declaration to a local fixpoint; returns the new
declaration, whether it changed, and the types of all its binders. The
parameters at positions `skip` carry assumptions (see `collectUses`). -/
def localRetype (d : Decl .pure) (skip : Array Nat := #[]) : MRetypeM (Decl .pure × Bool × Types) := do
  let .code c := d.value | return (d, false, {})
  let mut c := c
  let mut any := false
  let mut types : Types := {}
  for _ in [:8] do
    let ((c1, sc), ch1) ← (fwdCode (paramScope d) c).run false
    types := sc.types
    let uses ← collectUses types {} c1 {} d.name skip
    let (c2, ch2) ← (bwdCode uses c1).run false
    c := c2
    if !(ch1 || ch2) then break
    any := true
  return ({ d with value := .code c }, any, types)

/-- The applications of constants in `c`, with the type of the binder. -/
partial def constApps (c : Code .pure) (acc : Array (Name × Array (Arg .pure) × Expr)) :
    Array (Name × Array (Arg .pure) × Expr) :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .const f _ args _ => acc.push (f, args, d.type)
      | _ => acc
    constApps k acc
  | .jp d k | .fun d k _ => constApps k (constApps d.value acc)
  | .cases cs => cs.alts.foldl (fun acc alt => constApps alt.getCode acc) acc
  | _ => acc

/-- Variables of `c` bound to `◾`. -/
partial def erasedVars (c : Code .pure) (acc : FVarIdSet) : FVarIdSet :=
  match c with
  | .let d k => erasedVars k (if d.value matches .erased then acc.insert d.fvarId else acc)
  | .jp d k | .fun d k _ => erasedVars k (erasedVars d.value acc)
  | .cases cs => cs.alts.foldl (fun acc alt => erasedVars alt.getCode acc) acc
  | _ => acc

/-- What a declaration returns: the types of the returned values, except the
results of its own saturated self calls (by induction on the recursion they
have the declaration's result type, whatever it is) and constructors without
fields (`none`, `[]`), whose inductives are listed separately: such a value
exists at every instantiation of its inductive. -/
partial def returnTypes (env : Environment) (self : Name) (arity : Nat) (types : Types) :
    Code .pure → Std.HashMap FVarId (Option Name) → Array Expr × Array Name → Array Expr × Array Name
  | .let d k, special, acc =>
    let special := match d.value with
      | .const f _ args _ =>
        match env.find? f with
        | some (.ctorInfo c) => if c.numFields == 0 then special.insert d.fvarId (some c.induct) else special
        | _ => if f == self && args.size == arity then special.insert d.fvarId none else special
      | _ => special
    returnTypes env self arity types k special acc
  | .jp d k, special, acc | .fun d k _, special, acc =>
    returnTypes env self arity types k special (returnTypes env self arity types d.value special acc)
  | .cases cs, special, acc => cs.alts.foldl (fun acc alt => returnTypes env self arity types alt.getCode special acc) acc
  | .return x, special, (tys, inds) =>
    match special[x]? with
    | some none => (tys, inds)
    | some (some ind) => (tys, inds.push ind)
    | none => (tys.push (types.getD x anyExpr), inds)
  | _, _, acc => acc

/-- Is `n` the `map` loop of `Array.mapMUnsafe` or `Array.mapFinIdxMUnsafe`
(an instance of one of Lean's specializations of it, or its `_redArg`
part)? These are the loops of §2.7 that reinterpret an array. -/
def isMapLoop (keys : NameMap InstKey) (n : Name) : Bool :=
  let n := match n with
    | .str p "_redArg" => p
    | n => n
  match keys.find? n with
  | some k =>
    let u := userName ((specOrigin? k.decl).getD k.decl)
    u == `Array.mapMUnsafe.map || u == `Array.mapFinIdxMUnsafe.map
  | none => false

def isArrayAny (e : Expr) : Bool := e.isAppOfArity ``Array 1 && e.appArg!.consumeMData == anyExpr

/-- Occurrences of `Array lcAny` in `e`. -/
partial def countArrayAny (e : Expr) : Nat :=
  if isArrayAny e then 1
  else match e with
    | .app f a => countArrayAny f + countArrayAny a
    | .forallE _ d b _ => countArrayAny d + countArrayAny b
    | .mdata _ b => countArrayAny b
    | _ => 0

/-- The element type of the array that a `map` loop returns (see
`isMapLoop`). The loop replaces the elements of its array parameter one by
one with `Array.uset` and returns the array when every element has been
replaced; if every value it stores (other than the `box(0)` placeholder) has
the same precise type `β`, it returns an `Array β`. The array parameter and
the arrays derived from it must only be read, written, passed back to the
loop, returned (possibly inside a constructor, e.g. `some bs`) or jumped
with; any other use (the array escaping into a closure, say) gives up. -/
partial def mapLoopElem? (d : Decl .pure) (types : Types) : MRetypeM (Option Expr) := do
  let .code c := d.value | return none
  let arrs ← d.params.filterM fun p => return isArrayTy p.type && (← unknown p.type)
  let some bs := arrs[0]? | return none
  unless arrs.size == 1 do return none
  let keys := (← get).keys
  let env ← getEnv
  let erased := erasedVars c {}
  -- The arrays derived from `bs`, to a fixpoint (join-point parameters
  -- receive them through jumps).
  let mut chain : FVarIdSet := ({} : FVarIdSet).insert bs.fvarId
  let mut result : Bool × Array (Option Expr) := (true, #[])
  for _ in [:4] do
    let before := chain.size
    let (chain', ok, stored) := visit env keys erased types d.name c (chain, true, #[])
    chain := chain'
    result := (ok, stored)
    if chain.size == before then break
  let (ok, stored) := result
  unless ok do return none
  let tys := stored.filterMap id
  let some t := tys[0]? | return none
  if tys.size != stored.size then return none
  let n ← norm t
  for t' in tys do
    if (← unknown t') || (← norm t') != n then return none
  return some t
where
  /-- One pass over the loop body: extends the chain of derived arrays,
  checks their uses, and collects the types of the stored values (`none` for
  a value of unknown type; placeholders are skipped). -/
  visit (env : Environment) (keys : NameMap InstKey) (erased : FVarIdSet) (types : Types) (self : Name)
      (c : Code .pure) : FVarIdSet × Bool × Array (Option Expr) → FVarIdSet × Bool × Array (Option Expr)
    | (chain, ok, stored) =>
    let inChain (a : Arg .pure) : Bool := match a with
      | .fvar x => chain.contains x
      | _ => false
    match c with
    | .let d k =>
      let st := match d.value with
        | .const f _ args _ =>
          match (keys.find? f).map (·.decl) with
          | some ``Array.uset =>
            -- `Array.uset α a i v h`: only the array argument may be derived.
            if args.size != 5 || args.zipIdx.any (fun (a, i) => i != 1 && inChain a) then (chain, false, stored)
            else if inChain args[1]! then
              let stored := match args[3]! with
                | .fvar x => if erased.contains x then stored else stored.push (types[x]?.filter (!·.isErased))
                | _ => stored
              (chain.insert d.fvarId, ok, stored)
            else (chain, ok, stored)
          | some ``Array.uget | some ``Array.usize | some ``Array.size => (chain, ok, stored)
          | _ =>
            if f == self || env.isConstructor f || !args.any inChain then (chain, ok, stored)
            else (chain, false, stored)
        | .fvar _ args => (chain, ok && !args.any inChain, stored)
        | .proj _ _ x => (chain, ok && !chain.contains x, stored)
        | _ => (chain, ok, stored)
      visit env keys erased types self k st
    | .jp d k =>
      -- Parameters that receive a derived array join the chain.
      let chain := d.params.zipIdx.foldl (fun ch (p, i) =>
        if jumpsWith d.fvarId i k chain then ch.insert p.fvarId else ch) chain
      visit env keys erased types self k (visit env keys erased types self d.value (chain, ok, stored))
    | .fun d k _ =>
      visit env keys erased types self k (visit env keys erased types self d.value (chain, ok, stored))
    | .cases cs =>
      cs.alts.foldl (fun st alt => visit env keys erased types self alt.getCode st)
        (chain, ok && !chain.contains cs.discr, stored)
    | _ => (chain, ok, stored)
  jumpsWith (j : FVarId) (i : Nat) (c : Code .pure) (chain : FVarIdSet) : Bool :=
    match c with
    | .jmp j' args => j' == j && (match args[i]? with | some (.fvar x) => chain.contains x | _ => false)
    | .let _ k => jumpsWith j i k chain
    | .fun d k _ | .jp d k => jumpsWith j i d.value chain || jumpsWith j i k chain
    | .cases cs => cs.alts.any fun alt => jumpsWith j i alt.getCode chain
    | _ => false

/-- Refine a declaration's result type, if unknown: for a `map` loop, from
the values it stores (`mapLoopElem?`); otherwise from the values it returns,
when they agree (constructors without fields must belong to the inductive of
that type). -/
def refineSignature (d : Decl .pure) (types : Types) : MRetypeM (Decl .pure × Bool) := do
  let .code c := d.value | return (d, false)
  let sig := ((← get).sigs[d.name]?).getD (declSig d)
  unless ← unknown sig.ret do return (d, false)
  let mut cand : Option Expr := none
  if isMapLoop (← get).keys d.name then
    if let some β ← mapLoopElem? d types then
      -- The loop's result type holds its array once, e.g. `Option (Array lcAny)`.
      let occ := countArrayAny sig.ret
      if occ == 1 then
        cand := some (sig.ret.replace fun e => if isArrayAny e then some (mkApp (mkConst ``Array) β) else none)
  if cand.isNone then
    let (rets, inds) := returnTypes (← getEnv) d.name d.params.size types c {} (#[], #[])
    if let some t := rets[0]? then
      let n ← norm t
      let mut agree := true
      for r in rets do
        if (← norm r) != n then agree := false
      for ind in inds do
        unless sameHead t.consumeMData.getAppFn (.const ind []) do agree := false
      if agree then cand := some t
  let some t ← refineTo? sig.ret cand | return (d, false)
  let d := withSig d d.params t
  modify fun s => { s with sigs := s.sigs.insert d.name (declSig d) }
  return (d, true)

/-! ## Parameters from call sites -/

/-- What the call sites in the program's live declarations tell (self calls
not included): the argument types per (callee, parameter), `none` for a
placeholder argument; the parameters that some partial application leaves
open (`blocked`: they receive whatever the closure is applied to); the types
of the binders of saturated calls, per callee; and which callees are
referenced otherwise. -/
structure CallSites where
  args : Std.HashMap (Name × Nat) (Array (Option Expr)) := {}
  blocked : Std.HashSet (Name × Nat) := {}
  results : Std.HashMap Name (Array Expr) := {}
  /-- Declarations also referenced otherwise than by a saturated call (a
  closure, an over-application), including by themselves. -/
  escapes : NameSet := {}

def callSites (decls : Array (Decl .pure)) (types : Array Types) : MRetypeM CallSites := do
  let mut cs : CallSites := {}
  let st ← get
  for h : i in [:decls.size] do
    let d := decls[i]
    let .code c := d.value | continue
    unless st.live.contains d.name do continue
    let sc : Scope := { types := types[i]!, erased := erasedVars c {} }
    for (f, args, resTy) in constApps c #[] do
      if !st.codeDecls.contains f then continue
      let some sig := st.sigs[f]? | continue
      if args.size != sig.params.size then cs := { cs with escapes := cs.escapes.insert f }
      if f == d.name then continue
      for j in [:sig.params.size] do
        match args[j]? with
        | some a =>
          let t := if sc.isPlaceholder a then none else some (sc.argTy a)
          cs := { cs with args := cs.args.insert (f, j) ((cs.args.getD (f, j) #[]).push t) }
        | none => cs := { cs with blocked := cs.blocked.insert (f, j) }
      if args.size == sig.params.size then
        cs := { cs with results := cs.results.insert f ((cs.results.getD f #[]).push resTy) }
  return cs

/-- Do all self calls of `d` pass arguments of the types `hyp` assigns to
parameter positions? -/
def selfCallsAgree (d : Decl .pure) (types : Types) (hyp : Array (Nat × Expr)) : MRetypeM Bool := do
  let .code c := d.value | return true
  let sc : Scope := { types, erased := erasedVars c {} }
  for (f, args, _) in constApps c #[] do
    if f != d.name then continue
    for (j, t) in hyp do
      let some a := args[j]? | return false
      if sc.isPlaceholder a then continue
      if (← norm (sc.argTy a)) != (← norm t) then return false
  return true

/-- Parameters that every caller passes at the same precise type: assume
that type, retype the body, and keep the assumption if the self calls agree
(then every value reaching the parameter has the type). -/
def paramsFromCallers (decls : Array (Decl .pure)) (types : Array Types) :
    MRetypeM (Array (Decl .pure) × Array Types × Bool) := do
  let sites ← callSites decls types
  let mut decls := decls
  let mut types := types
  let mut changed := false
  for i in [:decls.size] do
    let d := decls[i]!
    unless d.value matches .code _ do continue
    let mut hyp : Array (Nat × Expr) := #[]
    for h : j in [:d.params.size] do
      let p := d.params[j]
      -- (A borrow annotation, `mdata`, does not change the type.)
      let pt := p.type.consumeMData
      unless ← unknown pt do continue
      if sites.blocked.contains (d.name, j) then continue
      let ts := ((sites.args.getD (d.name, j) #[]).filterMap id)
      let some t := ts[0]? | continue
      -- Only types holding an erased array (`Array lcAny`, `Option (Array
      -- lcAny)`, …) or receiving a typed reference: code over a dynamically
      -- typed value (`Dynamic.get?`) casts it to other types in branches
      -- that a runtime check rules out, and at a precise parameter type
      -- those casts could not be translated.
      unless countArrayAny pt > 0 || hasTypedRef t do continue
      let n ← norm t
      let mut agree := true
      for t' in ts do
        if (← unknown t') || (← norm t') != n then agree := false
      if !agree then continue
      if let some t ← refineTo? pt (some t) then hyp := hyp.push (j, t)
    if hyp.isEmpty then continue
    let oldSig := (← get).sigs[d.name]?
    let params := hyp.foldl (fun ps (j, t) => ps.set! j { ps[j]! with type := t }) d.params
    let d' := withSig d params (oldSig.map (·.ret) |>.getD (declSig d).ret)
    modify fun s => { s with sigs := s.sigs.insert d.name (declSig d') }
    let (d'', _, types'') ← localRetype d' (hyp.map (·.1))
    if ← selfCallsAgree d'' types'' hyp then
      decls := decls.set! i d''
      types := types.set! i types''
      changed := true
    else
      modify fun s => { s with sigs := match oldSig with
        | some sig => s.sigs.insert d.name sig
        | none => s.sigs.erase d.name }
  -- Result types: when every saturated call binds the result at the same
  -- precise type, the value returned has it (callers would convert right
  -- away; the conversion moves to the callee's returns, typically once
  -- into a constant instead of at every read of it).
  for i in [:decls.size] do
    let d := decls[i]!
    unless d.value matches .code _ do continue
    let some sig := (← get).sigs[d.name]? | continue
    unless ← unknown sig.ret do continue
    -- A closure of it may be applied where the result has another type.
    if sites.escapes.contains d.name then continue
    let rs := sites.results.getD d.name #[]
    let some t := rs[0]? | continue
    let n ← norm t
    let mut agree := true
    for r in rs do
      if (← unknown r) || (← norm r) != n then agree := false
    if !agree then continue
    if let some t ← refineTo? sig.ret (some t) then
      let d := withSig d d.params t
      modify fun s => { s with sigs := s.sigs.insert d.name (declSig d) }
      decls := decls.set! i d
      changed := true
  return (decls, types, changed)

/-! ## Map loops that change the element representation

A `map` loop of `Array.mapMUnsafe`/`mapFinIdxMUnsafe` (§2.7) replaces the
elements of its array one by one, so the array holds `α` values at the
indices not visited yet and `β` values at the others. When `α` and `β` have
the same representation, the loop runs on the precise array
(`paramsFromCallers`). When they differ, the array parameter stays
`Array lcAny`, and the loop would run on an array of `Box`es, converted from
the input on entry and to the result on exit. Instead, such a loop gets a
*split* instance over two arrays: the source `src : Array α`, read at `α`'s
own representation (each slot still replaced by the placeholder after it is
read, as Lean does, so that the element stays unshared), and the result
`dst : Array β`, which the caller creates empty with the source's size as
capacity, and to which each mapped value is pushed.

The loop must have the shape Lean gives it: the arrays derived from the
parameter (by `uset`, and through join points) are only read with `uget` at
the loop index (before any value is written), written with `uset` at the
loop index (the placeholder, then the mapped value, once), measured
(`usize`, `size`), passed to the loop again with the index plus one after
the value was written, or with the index to the loop a `_redArg` wrapper
calls, returned, put in a constructor or passed to a join point; and the
entry call passes the index `0`. Then `dst` holds exactly the values mapped
so far whenever the loop runs at index `i` (it has `i` elements), so the
value written at index `i` is the next one pushed. Any other shape keeps the
uniform loop. -/

/-- The shape of a `map` loop: its array parameter (the only one of type
`Array lcAny`), its index parameter, and the type of the values it stores. -/
structure LoopShape where
  arrPos : Nat
  idxPos : Nat
  elem : Expr

/-- The extern instance of `Array` operation `op` at element type `t`. -/
def arrayExternAt (op : Name) (t : Expr) : MRetypeM Name := do
  let some base ← getBaseDecl? op | throwError "lean2rr: no base declaration of {op}"
  externInstance op base #[eraseLevels t]

def isPlaceholderArg (erased : FVarIdSet) : Arg .pure → Bool
  | .fvar x => erased.contains x
  | _ => true

/-- The shape of map loop `d` (see `LoopShape`), given the shapes of the
other map loops. -/
def loopShape? (d : Decl .pure) (types : Types) (shapes : NameMap LoopShape) : MRetypeM (Option LoopShape) := do
  let .code c := d.value | return none
  let keys := (← get).keys
  let arrs := d.params.zipIdx.filter fun (p, _) => isArrayAny p.type.consumeMData
  let #[(arr, arrPos)] := arrs | return none
  let erased := erasedVars c {}
  let paramIdx (a : Arg .pure) : Option Nat := match a with
    | .fvar x => d.params.findIdx? (·.fvarId == x)
    | _ => none
  let apps := constApps c #[]
  let mut idx : Option Nat := none
  let mut elems : Array Expr := #[]
  for (f, args, _) in apps do
    match (keys.find? f).map (·.decl) with
    | some ``Array.uget | some ``Array.uset =>
      if args[1]? == some (.fvar arr.fvarId) && idx.isNone then idx := args[2]? >>= paramIdx
      if (keys.find? f).map (·.decl) == some ``Array.uset && args.size == 5 then
        if !isPlaceholderArg erased args[3]! then
          match args[3]! with
          | .fvar x => elems := elems.push (types.getD x anyExpr)
          | _ => pure ()
    | _ =>
      -- A wrapper (`_redArg`): the loop it passes the array to.
      if let some s := shapes.find? f then
        if args[s.arrPos]? == some (.fvar arr.fvarId) then
          if idx.isNone then idx := args[s.idxPos]? >>= paramIdx
          elems := elems.push s.elem
  let some idxPos := idx | return none
  unless d.params[idxPos]!.type.consumeMData.isConstOf ``USize do return none
  let some β := elems[0]? | return none
  if ← unknown β then return none
  for t in elems do
    if (← norm t) != (← norm β) then return none
  return some { arrPos, idxPos, elem := β }

/-- `c` without the placeholders (`let x := ◾`) it does not use (the
split loop's source gets a placeholder of its own type). -/
partial def dropDeadPlaceholders (c : Code .pure) : Code .pure :=
  match c with
  | .let d k =>
    let k := dropDeadPlaceholders k
    if d.value matches .erased && !usesFVar d.fvarId k then k else .let d k
  | .jp d k => .jp (FunDecl.mk d.fvarId d.binderName d.params d.type (dropDeadPlaceholders d.value)) (dropDeadPlaceholders k)
  | .fun d k _ => .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (dropDeadPlaceholders d.value)) (dropDeadPlaceholders k)
  | .cases cs => .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (dropDeadPlaceholders code)
      | .default code => .default (dropDeadPlaceholders code)
      | a => a⟩
  | c => c
where
  argUses (x : FVarId) (args : Array (Arg .pure)) : Bool := args.any fun a => match a with | .fvar y => y == x | _ => false
  usesFVar (x : FVarId) (c : Code .pure) : Bool :=
    match c with
    | .let d k =>
      (match d.value with
        | .const _ _ args _ => argUses x args
        | .fvar g args => g == x || argUses x args
        | .proj _ _ y => y == x
        | _ => false) || usesFVar x k
    | .jp d k | .fun d k _ => usesFVar x d.value || usesFVar x k
    | .cases cs => cs.discr == x || cs.alts.any fun alt => usesFVar x alt.getCode
    | .jmp j args => j == x || argUses x args
    | .return y => y == x
    | _ => false

structure SplitCtx where
  self : Name
  selfNew : Name
  shape : LoopShape
  α : Expr
  β : Expr
  types : Types
  shapes : NameMap LoopShape

/-- What the rewrite of a loop body knows: each derived array's source and
result arrays and how many values were written into it since the loop was
entered (0 or 1); the `USize` variables that are the loop index plus a
constant; the `USize` literals 1; the placeholders; the derived arrays
passed to each join point parameter (their write counts; `none` for
another argument). -/
structure SplitSt where
  pairs : Std.HashMap FVarId (FVarId × FVarId) := {}
  count : Std.HashMap FVarId Nat := {}
  off : Std.HashMap FVarId Nat := {}
  one : FVarIdSet := {}
  erased : FVarIdSet := {}
  seen : Std.HashMap (FVarId × Nat) (Array (Option Nat)) := {}

abbrev SplitM := StateT SplitSt MRetypeM

def splitFail {α : Type} : SplitM α := throwError "lean2rr: map loop not split"

def replaceArrayAny (t β : Expr) : SplitM Expr := do
  match countArrayAny t with
  | 0 => return t
  | 1 => return t.replace fun e => if isArrayAny e then some (mkApp (mkConst ``Array) β) else none
  | _ => splitFail

mutual
  /-- Ensure the split instance of map loop `f` (whose shape is in `shapes`)
  from `α` to `β`: its name, or `none` if the loop cannot be split. -/
  partial def ensureSplit (f : Name) (α β : Expr) (shapes : NameMap LoopShape)
      (src : NameMap (Decl .pure × Types)) : MRetypeM (Option Name) := do
    let key := (f, ← norm α, ← norm β)
    if let some r := (← get).splits[key]? then
      -- An instance being built is only referenced by itself.
      if let some n := r then
        if (← get).splitBusy.contains n then return none
      return r
    let some (d, types) := src.find? f | return none
    let some shape := shapes.find? f | return none
    let name := Name.num (f ++ `_l2r_split) (← get).splits.size
    modify fun s => { s with splits := s.splits.insert key (some name), splitBusy := s.splitBusy.insert name }
    let r ← try some <$> buildSplit d shape types name α β shapes src catch _ => pure none
    modify fun s => { s with splitBusy := s.splitBusy.erase name }
    match r with
    | some d' =>
      modify fun s => { s with sigs := s.sigs.insert name (declSig d') }
      let (d', _, _) ← localRetype d'
      modify fun s => { s with splitDecls := s.splitDecls.push d', sigs := s.sigs.insert name (declSig d') }
      return some name
    | none =>
      modify fun s => { s with splits := s.splits.insert key none }
      return none

  /-- The split instance `name` of map loop `d`. -/
  partial def buildSplit (d : Decl .pure) (shape : LoopShape) (types : Types) (name : Name) (α β : Expr)
      (shapes : NameMap LoopShape) (src : NameMap (Decl .pure × Types)) : MRetypeM (Decl .pure) := do
    let .code c := d.value | throwError "lean2rr: no code"
    let ret := (splitArrows d.type d.params.size).2
    if ← unknown ret then throwError "lean2rr: map loop result unknown"
    let p := d.params[shape.arrPos]!
    let s ← mkFreshFVarId
    let t ← mkFreshFVarId
    let params := d.params[:shape.arrPos].toArray ++
      #[{ p with fvarId := s, binderName := `src, type := mkApp (mkConst ``Array) α },
        { p with fvarId := t, binderName := `dst, type := mkApp (mkConst ``Array) β }] ++
      d.params[shape.arrPos + 1:].toArray
    let st : SplitSt := {
      pairs := ({} : Std.HashMap _ _).insert p.fvarId (s, t)
      count := ({} : Std.HashMap _ _).insert p.fvarId 0
      off := ({} : Std.HashMap _ _).insert d.params[shape.idxPos]!.fvarId 0
      erased := erasedVars c {} }
    let cx : SplitCtx := { self := d.name, selfNew := name, shape, α, β, types, shapes }
    let (c', _) ← (splitCode cx src c).run st
    return { withSig d params ret with name, value := .code (dropDeadPlaceholders c') }

  /-- Rewrite a loop body for its split instance (see `SplitSt`); fails on
  any other use of a derived array. -/
  partial def splitCode (cx : SplitCtx) (src : NameMap (Decl .pure × Types)) (c : Code .pure) :
      SplitM (Code .pure) := do
    let chain? (a : Arg .pure) : SplitM (Option FVarId) := do
      match a with
      | .fvar x => return if (← getThe SplitSt).pairs.contains x then some x else none
      | _ => return none
    let noChain (args : Array (Arg .pure)) : SplitM Unit := do
      for a in args do
        if (← chain? a).isSome then splitFail
    let offOf (a : Arg .pure) : SplitM (Option Nat) := do
      match a with
      | .fvar x => return (← getThe SplitSt).off[x]?
      | _ => return none
    match c with
    | .let d k =>
      match d.value with
      | .lit (.usize 1) =>
        modifyThe SplitSt fun st => { st with one := st.one.insert d.fvarId }
        return .let d (← splitCode cx src k)
      | .const f us args _ =>
        let keys := (← getThe MRetypeState).keys
        let op := (keys.find? f).map (·.decl)
        let arrArg ← match args[1]? with
          | some a => chain? a
          | none => pure none
        if let some x := arrArg then
          let some (xs, xd) := (← getThe SplitSt).pairs[x]? | splitFail
          let cnt := ((← getThe SplitSt).count[x]?).getD 0
          match op with
          | some ``Array.uget =>
            -- Possibly over-applied: the element of an array of functions
            -- applied to the function's arguments.
            unless args.size ≥ 4 && cnt == 0 && (← offOf args[2]!) == some 0 do splitFail
            noChain (args.eraseIdx! 1)
            let inst ← arrayExternAt ``Array.uget cx.α
            let d' := { d with type := if args.size == 4 then cx.α else d.type,
                               value := .const inst [] (#[.erased, .fvar xs, args[2]!, .erased] ++ args[4:].toArray) }
            return .let d' (← splitCode cx src k)
          | some ``Array.uset =>
            unless args.size == 5 && cnt == 0 && (← offOf args[2]!) == some 0 do splitFail
            noChain (args.eraseIdx! 1)
            if isPlaceholderArg (← getThe SplitSt).erased args[3]! then
              -- The placeholder, at `α`, into the source.
              let z ← mkFreshFVarId
              let zd : LetDecl .pure := { fvarId := z, binderName := `_x, type := cx.α, value := .erased }
              let inst ← arrayExternAt ``Array.uset cx.α
              let d' := { d with type := mkApp (mkConst ``Array) cx.α,
                                 value := .const inst [] #[.erased, .fvar xs, args[2]!, .fvar z, .erased] }
              modifyThe SplitSt fun st => { st with pairs := st.pairs.insert d.fvarId (d.fvarId, xd), count := st.count.insert d.fvarId 0, erased := st.erased.insert z }
              return .let zd (.let d' (← splitCode cx src k))
            -- The mapped value, pushed onto the result.
            let .fvar v := args[3]! | splitFail
            if (← norm (cx.types.getD v anyExpr)) != (← norm cx.β) then splitFail
            let inst ← arrayExternAt ``Array.push cx.β
            let d' := { d with type := mkApp (mkConst ``Array) cx.β, value := .const inst [] #[.erased, .fvar xd, .fvar v] }
            modifyThe SplitSt fun st => { st with pairs := st.pairs.insert d.fvarId (xs, d.fvarId), count := st.count.insert d.fvarId 1 }
            return .let d' (← splitCode cx src k)
          | some ``Array.usize | some ``Array.size =>
            unless args.size == 2 do splitFail
            let inst ← arrayExternAt op.get! cx.α
            return .let { d with value := .const inst [] #[.erased, .fvar xs] } (← splitCode cx src k)
          | _ => pure ()
        -- A call of this loop, or of the loop a wrapper calls.
        let callee? : Option (Option LoopShape) :=
          if f == cx.self then some (some cx.shape) else (cx.shapes.find? f).map some
        if let some (some sh) := callee? then
          if args.size == ((← getThe MRetypeState).sigs[f]?.map (·.params.size)).getD 0 then
            if let some y ← chain? args[sh.arrPos]! then
              let some (ys, yd) := (← getThe SplitSt).pairs[y]? | splitFail
              let cnt := ((← getThe SplitSt).count[y]?).getD 0
              unless (← offOf args[sh.idxPos]!) == some cnt do splitFail
              noChain (args.eraseIdx! sh.arrPos)
              let target ← if f == cx.self then pure cx.selfNew else do
                match ← ensureSplit f cx.α cx.β cx.shapes src with
                | some n => pure n
                | none => splitFail
              let args' := args[:sh.arrPos].toArray ++ #[.fvar ys, .fvar yd] ++ args[sh.arrPos + 1:].toArray
              return .let { d with value := .const target us args' } (← splitCode cx src k)
        if (← getEnv).isConstructor f then
          -- A result (`some bs`, `EST.Out.ok bs w`): the result array.
          let mut args' := #[]
          let mut any := false
          for a in args do
            match ← chain? a with
            | some y =>
              let some (_, yd) := (← getThe SplitSt).pairs[y]? | splitFail
              args' := args'.push (.fvar yd)
              any := true
            | none => args' := args'.push a
          if any then
            let ty ← replaceArrayAny d.type cx.β
            return .let { d with type := ty, value := .const f us args' } (← splitCode cx src k)
          return .let d (← splitCode cx src k)
        noChain args
        -- The loop index plus one.
        if f == ``USize.add && args.size == 2 then
          match args[0]!, args[1]! with
          | .fvar a, .fvar b =>
            if let some o := (← getThe SplitSt).off[a]? then
              if (← getThe SplitSt).one.contains b then modifyThe SplitSt fun st => { st with off := st.off.insert d.fvarId (o + 1) }
          | _, _ => pure ()
        return .let d (← splitCode cx src k)
      | .fvar _ args =>
        noChain args
        return .let d (← splitCode cx src k)
      | .proj _ _ x =>
        if (← getThe SplitSt).pairs.contains x then splitFail
        return .let d (← splitCode cx src k)
      | .erased =>
        modifyThe SplitSt fun st => { st with erased := st.erased.insert d.fvarId }
        return .let d (← splitCode cx src k)
      | _ => return .let d (← splitCode cx src k)
    | .jp d k =>
      -- The continuation first: its jumps say which parameters receive
      -- derived arrays (with their write counts).
      let k' ← splitCode cx src k
      let mut params := #[]
      for h : i in [:d.params.size] do
        let p := d.params[i]
        let seen := ((← getThe SplitSt).seen[(d.fvarId, i)]?).getD #[]
        let counts := seen.filterMap id
        if counts.isEmpty then
          params := params.push p
        else
          unless counts.size == seen.size && counts.all (· == counts[0]!) do splitFail
          let s ← mkFreshFVarId
          let t ← mkFreshFVarId
          params := params ++ #[{ p with fvarId := s, binderName := `src, type := mkApp (mkConst ``Array) cx.α },
            { p with fvarId := t, binderName := `dst, type := mkApp (mkConst ``Array) cx.β }]
          modifyThe SplitSt fun st => { st with pairs := st.pairs.insert p.fvarId (s, t), count := st.count.insert p.fvarId counts[0]! }
      let value ← splitCode cx src d.value
      let res := (splitArrows d.type d.params.size).2
      let ty := params.foldr (fun p acc => .forallE p.binderName p.type acc .default) res
      return .jp (FunDecl.mk d.fvarId d.binderName params ty value) k'
    | .fun d k _ =>
      -- A closure must not capture a derived array.
      for x in (← getThe SplitSt).pairs.keys do
        if hasFVarIn x d.value then splitFail
      return .fun d (← splitCode cx src k)
    | .cases cs =>
      if (← getThe SplitSt).pairs.contains cs.discr then splitFail
      let alts ← cs.alts.mapM fun
        | .alt ctor ps code _ => return .alt ctor ps (← splitCode cx src code)
        | .default code => return .default (← splitCode cx src code)
        | a => return a
      let resTy ← try replaceArrayAny cs.resultType cx.β catch _ => pure cs.resultType
      return .cases ⟨cs.typeName, resTy, cs.discr, alts⟩
    | .jmp j args =>
      let mut args' := #[]
      for h : i in [:args.size] do
        let a := args[i]
        let entry ← match ← chain? a with
          | some y =>
            let some (ys, yd) := (← getThe SplitSt).pairs[y]? | splitFail
            args' := args' ++ #[.fvar ys, .fvar yd]
            pure (some (((← getThe SplitSt).count[y]?).getD 0))
          | none =>
            args' := args'.push a
            pure none
        modifyThe SplitSt fun st => { st with seen := st.seen.insert (j, i) (((st.seen[(j, i)]?).getD #[]).push entry) }
      return .jmp j args'
    | .return x =>
      match (← getThe SplitSt).pairs[x]? with
      | some (_, xd) => return .return xd
      | none => return .return x
    | c => return c
where
  hasFVarIn (x : FVarId) (c : Code .pure) : Bool :=
    (codeFVars c {}).contains x
  codeFVars (c : Code .pure) (acc : FVarIdSet) : FVarIdSet :=
    match c with
    | .let d k =>
      let acc := match d.value with
        | .const _ _ args _ | .fvar _ args => args.foldl (fun s a => match a with | .fvar y => s.insert y | _ => s) acc
        | .proj _ _ y => acc.insert y
        | _ => acc
      let acc := match d.value with | .fvar g _ => acc.insert g | _ => acc
      codeFVars k acc
    | .jp d k | .fun d k _ => codeFVars k (codeFVars d.value acc)
    | .cases cs => cs.alts.foldl (fun s alt => codeFVars alt.getCode s) (acc.insert cs.discr)
    | .jmp _ args => args.foldl (fun s a => match a with | .fvar y => s.insert y | _ => s) acc
    | .return y => acc.insert y
    | _ => acc
end

/-- The entry calls of split `map` loops in `c` (an index argument bound to
the literal `0` and a source array of a precise type `Array α`): rewritten to
call the split instance with a new empty result array whose capacity is the
source's size. -/
partial def splitEntries (types : Types) (zeros : FVarIdSet) (shapes : NameMap LoopShape)
    (src : NameMap (Decl .pure × Types)) (c : Code .pure) : MRetypeM (Code .pure) := do
  match c with
  | .let d k =>
    let k' ← splitEntries types zeros shapes src k
    let .const f us args _ := d.value | return .let d k'
    let some sh := shapes.find? f | return .let d k'
    unless args.size == ((← get).sigs[f]?.map (·.params.size)).getD 0 do return .let d k'
    let .fvar x := args[sh.arrPos]! | return .let d k'
    let .fvar i := args[sh.idxPos]! | return .let d k'
    unless zeros.contains i do return .let d k'
    let xt := (types.getD x anyExpr).consumeMData.headBeta
    unless xt.isAppOfArity ``Array 1 do return .let d k'
    let α := xt.appArg!
    if ← unknown α then return .let d k'
    let some name ← ensureSplit f α sh.elem shapes src | return .let d k'
    let n ← mkFreshFVarId
    let e ← mkFreshFVarId
    let sizeI ← arrayExternAt ``Array.size α
    let emptyI ← arrayExternAt ``Array.emptyWithCapacity sh.elem
    let nd : LetDecl .pure := { fvarId := n, binderName := `_x, type := mkConst ``Nat,
                                value := .const sizeI [] #[.erased, .fvar x] }
    let ed : LetDecl .pure := { fvarId := e, binderName := `_x, type := mkApp (mkConst ``Array) sh.elem,
                                value := .const emptyI [] #[.erased, .fvar n] }
    let args' := args[:sh.arrPos].toArray ++ #[.fvar x, .fvar e] ++ args[sh.arrPos + 1:].toArray
    return .let nd (.let ed (.let { d with value := .const name us args' } k'))
  | .jp d k =>
    let v ← splitEntries types zeros shapes src d.value
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← splitEntries types zeros shapes src k)
  | .fun d k _ =>
    let v ← splitEntries types zeros shapes src d.value
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← splitEntries types zeros shapes src k)
  | .cases cs =>
    let alts ← cs.alts.mapM fun
      | .alt ctor ps code _ => return .alt ctor ps (← splitEntries types zeros shapes src code)
      | .default code => return .default (← splitEntries types zeros shapes src code)
      | a => return a
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c

/-- Variables of `c` that hold the `USize` literal `0`: bound to it, or
join-point parameters that every jump passes such a variable. -/
partial def usizeZeros (c : Code .pure) : FVarIdSet := Id.run do
  let (lits, jps, jumps) := scan c ({}, #[], #[])
  let mut zeros := lits
  for _ in [:8] do
    let before := zeros.size
    for (j, ps) in jps do
      for h : i in [:ps.size] do
        let args := jumps.filterMap fun (j', as) => if j' == j then some as[i]? else none
        if !args.isEmpty && args.all (fun a => match a with | some (.fvar x) => zeros.contains x | _ => false) then
          zeros := zeros.insert ps[i]
    if zeros.size == before then break
  return zeros
where
  scan (c : Code .pure) (acc : FVarIdSet × Array (FVarId × Array FVarId) × Array (FVarId × Array (Arg .pure))) :
      FVarIdSet × Array (FVarId × Array FVarId) × Array (FVarId × Array (Arg .pure)) :=
    match c with
    | .let d k =>
      let (l, j, m) := acc
      scan k (if d.value matches .lit (.usize 0) then l.insert d.fvarId else l, j, m)
    | .jp d k =>
      let (l, j, m) := scan d.value acc
      scan k (l, j.push (d.fvarId, d.params.map (·.fvarId)), m)
    | .fun d k _ => scan k (scan d.value acc)
    | .cases cs => cs.alts.foldl (fun acc alt => scan alt.getCode acc) acc
    | .jmp j args => let (l, js, m) := acc; (l, js, m.push (j, args))
    | _ => acc

/-- Split the `map` loops whose element representation changes (see above):
rewrite their entry calls, add the split instances, and drop the original
loops that nothing reachable calls any more. -/
def splitMapLoops (decls : Array (Decl .pure)) (types : Array Types) (roots : Array Name) :
    MRetypeM (Array (Decl .pure)) := do
  let keys := (← get).keys
  let mut src : NameMap (Decl .pure × Types) := {}
  for h : i in [:decls.size] do
    let d := decls[i]
    if d.value matches .code _ && isMapLoop keys d.name then src := src.insert d.name (d, types[i]!)
  if src.isEmpty then return decls
  let mut shapes : NameMap LoopShape := {}
  for _ in [:3] do
    for (n, (d, ts)) in src.toList do
      unless shapes.contains n do
        if let some s ← loopShape? d ts shapes then shapes := shapes.insert n s
  if shapes.isEmpty then return decls
  let mut out := #[]
  for h : i in [:decls.size] do
    let d := decls[i]
    match d.value with
    | .code c => out := out.push { d with value := .code (← splitEntries types[i]! (usizeZeros c) shapes src c) }
    | _ => out := out.push d
  let added := (← get).splitDecls
  if added.isEmpty then return decls
  let all := out ++ added
  -- Original loops nothing reachable calls any more.
  let bodies : NameMap (Code .pure) := all.foldl (fun m d => match d.value with
    | .code c => m.insert d.name c
    | _ => m) {}
  let mut live : NameSet := {}
  let mut work := roots.toList
  while !work.isEmpty do
    let n :: rest := work | break
    work := rest
    if live.contains n then continue
    live := live.insert n
    let some c := bodies.find? n | continue
    for (f, _, _) in constApps c #[] do
      unless live.contains f do work := f :: work
  return all.filter fun d => !(shapes.contains d.name) || live.contains d.name

/-- An instance of `ST.Prim.mkRef` at a precise element type `α` returns a
`typedRef α` (Lean's mono type of a reference is `lcAny`): the references
it creates, and the binders they flow into by the rules above, get a typed
representation (translation plan §5.1). -/
def typeMkRef (d : Decl .pure) : MRetypeM (Decl .pure) := do
  unless d.value matches .extern _ do return d
  let some k := (← get).keys.find? d.name | return d
  unless k.decl == ``ST.Prim.mkRef do return d
  let some α := k.typeArgs[1]? | return d
  let α ← toMonoTypeKeep α
  if (← unknown α) || α.isErased then return d
  let ret := (splitArrows d.type d.params.size).2.consumeMData
  let args := ret.getAppArgs
  unless (ret.isAppOf ``ST.Out || ret.isAppOf ``EST.Out) && args.back? == some anyExpr do return d
  let d := withSig d d.params (mkAppN ret.getAppFn (args.pop.push (mkTypedRef α)))
  modify fun s => { s with sigs := s.sigs.insert d.name (declSig d) }
  return d

/-- Stage 3 on all mono declarations (bounded global fixpoint). `roots` are
the declarations the entry point calls (`main`, startup work). Returns the
declarations, including extern instances created by re-instantiation, and
the instance keys extended with theirs. -/
def retypeMono (stage2 : Stage2Config) (table : RelevanceTable) (decls : Array (Decl .pure)) (keys : NameMap InstKey)
    (roots : Array Name) : CoreM (Array (Decl .pure) × NameMap InstKey) := do
  let mut st : MRetypeState := { keys }
  let mut bodies : NameMap (Code .pure) := {}
  for d in decls do
    st := { st with sigs := st.sigs.insert d.name (declSig d) }
    match d.value with
    | .code c =>
      st := { st with codeDecls := st.codeDecls.insert d.name }
      bodies := bodies.insert d.name c
    | .extern _ =>
      if let some k := keys.find? d.name then
        if k.dicts.isEmpty then st := { st with instances := st.instances.insert (k.decl, k.typeArgs) d.name }
  -- Reachable declarations.
  let mut live : NameSet := {}
  let mut work := roots.toList
  while !work.isEmpty do
    let n :: rest := work | break
    work := rest
    if live.contains n then continue
    let some c := bodies.find? n | continue
    live := live.insert n
    for (f, _, _) in constApps c #[] do
      unless live.contains f do work := f :: work
  st := { st with live }
  let act : MRetypeM (Array (Decl .pure)) := do
    let mut decls ← decls.mapM typeMkRef
    let mut types : Array Types := decls.map fun _ => {}
    -- The fixpoint, then the split of `map` loops (whose split instances
    -- type the values they read, so a second fixpoint can type what those
    -- flow into, e.g. a closure capturing them).
    for round in [:2] do
      for _ in [:8] do
        let mut changed := false
        for i in [:decls.size] do
          let d := decls[i]!
          unless d.value matches .code _ do continue
          let (d, ch1, ts) ← localRetype d
          let (d, ch2) ← refineSignature d ts
          decls := decls.set! i d
          types := types.set! i ts
          changed := changed || ch1 || ch2
        let (decls', types', ch3) ← paramsFromCallers decls types
        decls := decls'
        types := types'
        if !(changed || ch3) then break
      if round == 1 then break
      let before := (← get).splitDecls.size
      let split ← splitMapLoops decls types roots
      if (← get).splitDecls.size == before then break
      let added := (← get).splitDecls
      modify fun s => { s with
        live := added.foldl (fun l d => l.insert d.name) s.live
        codeDecls := added.foldl (fun l d => l.insert d.name) s.codeDecls }
      types := split.map fun d => (decls.findIdx? (·.name == d.name)).map (types[·]!) |>.getD {}
      decls := split
    return decls ++ (← get).newExterns
  let (decls, st') ← (act.run { table, stage2 }).run st
  return (decls, st'.keys)

end LeanToReussir
