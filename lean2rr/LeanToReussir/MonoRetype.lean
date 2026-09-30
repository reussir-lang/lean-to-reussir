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
  let passes ← stage2Passes
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
  unless positions.size == key.typeArgs.size && base.params.size == args.size do return none
  let holes ← positions.mapM fun _ => mkFreshFVarId
  let mut assign : Array (Option Expr) := Array.replicate holes.size none
  let mut ty := eraseLevels base.type
  for h : i in [:args.size] do
    match ty.headBeta with
    | .forallE _ d b _ =>
      match positions.idxOf? i with
      | some j => ty := b.instantiate1 (.fvar holes[j]!)
      | none =>
        unless sc.isPlaceholder args[i] do
          assign := matchTy holes d (sc.argTy args[i]) assign
        ty := b.instantiate1 anyExpr
    | _ => return none
  let some typeArgs := assign.mapM id | return none
  for t in typeArgs do
    if (← unknown t) || t.hasFVar then return none
  let inst ← externInstance key.decl base (typeArgs.map eraseLevels)
  if inst == f then return none
  let some sig := (← get).sigs[inst]? | return none
  for h : i in [:args.size] do
    let p := sig.params[i]!.consumeMData
    if p.isErased || p.isSort || p == mkConst ``lcVoid then continue
    if sc.isPlaceholder args[i] then continue
    if (← norm (sc.argTy args[i])) != (← norm p) then return none
  -- A binder that already has a precise type keeps it; the instance must
  -- produce exactly that.
  unless (← unknown resTy) || (← norm resTy) == (← norm sig.ret) do return none
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
      -- Only types holding an erased array (`Array lcAny`, `Option (Array
      -- lcAny)`, …): code over a dynamically typed value (`Dynamic.get?`)
      -- casts it to other types in branches that a runtime check rules out,
      -- and at a precise parameter type those casts could not be translated.
      unless countArrayAny p.type > 0 && (← unknown p.type) do continue
      if sites.blocked.contains (d.name, j) then continue
      let ts := ((sites.args.getD (d.name, j) #[]).filterMap id)
      let some t := ts[0]? | continue
      let n ← norm t
      let mut agree := true
      for t' in ts do
        if (← unknown t') || (← norm t') != n then agree := false
      if !agree then continue
      if let some t ← refineTo? p.type (some t) then hyp := hyp.push (j, t)
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

/-- Stage 3 on all mono declarations (bounded global fixpoint). `roots` are
the declarations the entry point calls (`main`, startup work). Returns the
declarations, including extern instances created by re-instantiation, and
the instance keys extended with theirs. -/
def retypeMono (table : RelevanceTable) (decls : Array (Decl .pure)) (keys : NameMap InstKey)
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
    let mut decls := decls
    let mut types : Array Types := decls.map fun _ => {}
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
    return decls ++ (← get).newExterns
  let (decls, st') ← (act.run { table }).run st
  return (decls, st'.keys)

end LeanToReussir
