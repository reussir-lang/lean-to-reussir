import Lean
import LeanToReussir.ArrayKinds
import LeanToReussir.ErasedDomains
import LeanToReussir.MonoRetype
import LeanToReussir.LowerBase

/-!
# The whole-program check of compact arrays (C0)

With optimization `compact-arrays`, an `Array S` of a scalar `S` is
`RVec<k>` of `S`'s storage kind `k` (`ArrayKinds.lean`), and every other
array, `Array lcAny` included, an array of `Box`es. The lowering chooses
the representation by type, so a value must never go from one to the other
on its way through the program: the representations differ at the type
`Array lcAny` (generic code, a type that depends on a value), at a field
whose declared type is `Array α` (`Subarray.array`: one layout per
inductive, rule 1), and between two storage kinds (a cast). This analysis
turns a kind off, for the whole program, when that could happen, so that
every array of the kind is an array of `Box`es again, as without the
optimization:

* **Crossings.** At each place where a value goes from one binder or
  position to another (an argument and its parameter, a result and its
  binder, a jump argument and its join point's parameter, a returned value
  and the result type, a constructor argument and its field as the layout
  has it, a field and the binder it is read into, an extern's argument and
  parameter), the two types are compared position by position (`alignArr`:
  through function types, and the arguments of one inductive); where
  `Array S` meets `Array T` and `T` has another kind, or none (`lcAny`,
  `Nat`, …), both kinds are turned off. `Array S` against `lcAny` is a box:
  allowed (leanrt's kinds 7 to 12 box a compact array).
* **Flow classes.** The same places join the binders into classes
  (union-find, as rule 4's `flowAnalysis` follows function values), also
  through containers (a constructor's arguments and its value, a field and
  the value it is read from), externs (all their arguments and their
  result: a reference, a thunk, a task, an array of arrays) and function
  values (their arguments, results and the parameters of their code). A
  class with a binder whose type mentions `Array lcAny` holds a value that
  generic code may read as an array of `Box`es: every kind that a type in
  the class mentions is turned off. (A box of a compact array unboxed at
  `Array lcAny` would be converted by leanrt, the safety net; one of `Box`es
  unboxed at a compact kind would stop the program.) A position that is no
  binder (an extern's parameter or result, a constructor's field) and whose
  type mentions a storage kind gets a node of its own in the value's class
  (`posNode`): a box unboxed there at `Array UInt64` makes the class mention
  `u64` (review F1).
* **Casts.** In a program that can read a value as another type
  (`programCasts`), every kind is off.

Only binders whose type can hold an array (`mayHoldArr`) are joined: a
value of type `Nat` carries no array. Only the declarations the entry point
reaches are walked: a declaration nothing reaches never runs (its
crossings lower to a panic, which `conv-liveness` drops). A field `Array α`
of an inductive that the program instantiates with a scalar array there is
a box (`arrayFieldInductives`, the lowering's `nominalType`), and counts as
one here (`caFieldTypes`).
-/

namespace LeanToReussir
open Lean Compiler LCNF

structure CAState where
  /-- Node of each (declaration, binder); synthetic binders name results
  and `initialize` constants. -/
  ids : Std.HashMap (Name × FVarId) Nat := {}
  parent : Array Nat := #[]
  /-- The type of each node, and where it is (for the report). -/
  tys : Array Expr := #[]
  wheres : Array Name := #[]
  /-- Kinds turned off, with the first reason of each. -/
  off : Std.HashMap String String := {}
  /-- Binder types of the declaration being walked. -/
  vars : Std.HashMap FVarId Expr := {}
  /-- Join point parameters of the declaration being walked. -/
  jps : Std.HashMap FVarId (Array (FVarId × Expr)) := {}
  holdCache : Std.HashMap Expr Bool := {}
  mentionCache : Std.HashMap Expr (Array String × Bool) := {}

abbrev CAM := ReaderT (IO.Ref (Std.HashMap Name (Option String))) (StateRefT CAState CoreM)

def CAM.kindOf (t : Expr) : CAM (Option String) := do scalarKind? (← read) t

def CAM.turnOff (k : Option String) (why : String) : CAM Unit := do
  let some k := k | return
  unless (← get).off.contains k do modify fun s => { s with off := s.off.insert k why }

/-- The element type of `t`, if it is `Array X`. -/
def arrElemOf? (t : Expr) : Option Expr :=
  let t := t.consumeMData.headBeta
  if t.isAppOfArity ``Array 1 then some t.appArg!.consumeMData.headBeta else none

/-- Whether a value of mono type `t` can hold an array whose elements have
a storage kind, or be read as one (`lcAny`): an array of scalars or of
`lcAny`, a function type whose domains or codomain can, an inductive whose
type arguments or fields at those arguments (`ctorFieldTypes`) can, a type
`Box` represents. A plain reachability with one visited set, as
`mayHoldFn`. -/
partial def mayHoldArr (t : Expr) : CAM Bool := do
  let t := keyTy t
  if let some b := (← get).holdCache[t]? then return b
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let r ← go t visited
  unless r do
    for v in (← visited.get) do modify fun s => { s with holdCache := s.holdCache.insert v false }
  modify fun s => { s with holdCache := s.holdCache.insert t r }
  return r
where
  go (t : Expr) (visited : IO.Ref (Std.HashSet Expr)) : CAM Bool := do
    if let some b := (← get).holdCache[t]? then return b
    if (← visited.get).contains t then return false
    visited.modify (·.insert t)
    match t with
    | .forallE _ d b _ => return (← go (keyTy d) visited) || (← go (keyTy b) visited)
    | .sort _ => return false
    | _ =>
      let .const n _ := t.getAppFn | return true
      if t.isAppOfArity ``Array 1 then
        let e := keyTy t.appArg!
        if (← CAM.kindOf e).isSome || e == anyExpr then return true
        return ← go e visited
      if n == ``lcAny then return true
      if [``lcErased, ``lcVoid, ``Nat, ``Int, ``String, ``ByteArray, ``FloatArray, ``Unit, ``PUnit,
          ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32, ``Bool].contains n then
        return false
      if (← CAM.kindOf t).isSome then return false
      let env ← getEnv
      let some iv := inductiveOf env t | return mayBeBox env t
      for a in t.getAppArgs do
        if ← go (keyTy a) visited then return true
      for c in iv.ctors do
        for f in ← ctorFieldTypes c t do
          if ← go (keyTy f) visited then return true
      return false

/-- The kinds of the arrays mono type `t` mentions, and whether it mentions
an array of `Box`es that generic code reads (`Array lcAny`, or of another
type `Box` represents). -/
partial def mentions (t : Expr) : CAM (Array String × Bool) := do
  let t := keyTy t
  if let some r := (← get).mentionCache[t]? then return r
  let r ← go t (#[], false)
  modify fun s => { s with mentionCache := s.mentionCache.insert t r }
  return r
where
  go (t : Expr) (acc : Array String × Bool) : CAM (Array String × Bool) := do
    match t with
    | .forallE _ d b _ => go b (← go d acc)
    | .app .. =>
      let mut acc := acc
      if let some e := arrElemOf? t then
        match ← CAM.kindOf e with
        | some k => acc := (if acc.1.contains k then acc.1 else acc.1.push k, acc.2)
        | none => if e == anyExpr || mayBeBox (← getEnv) e then acc := (acc.1, true)
      for a in t.getAppArgs do acc ← go a acc
      return acc
    | _ => return acc

/-- Values of type `a` go to a position of type `b` (see the module
comment, "Crossings"). -/
partial def alignArr (a b : Expr) (why : String) (fuel : Nat := 16) : CAM Unit := do
  let a := keyTy a
  let b := keyTy b
  if a == b then return
  let fuel' + 1 := fuel | return
  match arrElemOf? a, arrElemOf? b with
  | some ea, some eb =>
    let ka ← CAM.kindOf ea
    let kb ← CAM.kindOf eb
    if ka != kb then
      CAM.turnOff ka s!"{why}: {a} meets {b}"
      CAM.turnOff kb s!"{why}: {a} meets {b}"
    else if ka.isNone then alignArr ea eb why fuel'
    return
  | _, _ => pure ()
  match a, b with
  | .forallE _ da ba _, .forallE _ db bb _ =>
    alignArr db da why fuel'
    alignArr ba bb why fuel'
  | _, _ =>
    if a.isApp && b.isApp && a.getAppNumArgs == b.getAppNumArgs then
      if let (.const m _, .const n _) := (a.getAppFn, b.getAppFn) then
        if sameInductive m n then
          for (x, y) in a.getAppArgs.zip b.getAppArgs do alignArr x y why fuel'

/-- The node of binder `x` of declaration `decl`, of type `t` (made at its
first sight), if `t` can hold an array. -/
def CAM.node (decl : Name) (x : FVarId) (t : Expr) : CAM (Option Nat) := do
  if let some i := (← get).ids[(decl, x)]? then return some i
  unless ← mayHoldArr t do return none
  let i := (← get).parent.size
  modify fun s => { s with ids := s.ids.insert (decl, x) i, parent := s.parent.push i, tys := s.tys.push t,
                           wheres := s.wheres.push decl }
  return some i

partial def CAM.find (i : Nat) : CAM Nat := do
  let p := (← get).parent[i]!
  if p == i then return i
  let r ← CAM.find p
  modify fun s => { s with parent := s.parent.set! i r }
  return r

def CAM.union (a b : Option Nat) : CAM Unit := do
  let (some a, some b) := (a, b) | return
  let ra ← CAM.find a
  let rb ← CAM.find b
  if ra != rb then modify fun s => { s with parent := s.parent.set! ra rb }

/-- The synthetic binder of a result (of a declaration, or of a local
function `f`). -/
def resultVar (f : Name := .anonymous) : FVarId := ⟨`_l2r_result ++ f⟩

/-- The parameter types and result of function type `ty` with `n`
parameters. -/
def caSplitFn (ty : Expr) (n : Nat) : Array Expr × Expr := Id.run do
  let mut ty := ty
  let mut ps := #[]
  for _ in [:n] do
    match ty.consumeMData.headBeta with
    | .forallE _ d b _ => ps := ps.push d; ty := b.instantiate1 anyExpr
    | _ => break
  return (ps, ty)

structure CADecl where
  params : Array (FVarId × Expr)
  ret : Expr
  /-- An extern instance (no code). -/
  ext : Bool

/-- Whether layout field type `t` is `Array lcAny` (a field `Array α`). -/
def isArrayAnyField (t : Expr) : Bool :=
  let t := t.consumeMData
  t.isAppOfArity ``Array 1 && t.appArg!.consumeMData == anyExpr

/-- The inductives that have a field `Array α` (`α` a parameter: `Array
lcAny` in the layout, rule 1) and that some type of the program's binders
instantiates with a scalar array there (`Subarray UInt64`, `Vector Bool
n`, a user's `Column UInt8`). The lowering makes such a field a `Box`
(`nominalType`, `LowerCtx.boxedArrayFields`), which holds a compact array
as well as an array of boxes; the layout field `Array lcAny` would meet the
compact array (a crossing, `compactArrayKinds`). -/
partial def arrayFieldInductives (decls : Array (Decl .pure)) : CoreM NameSet := do
  let env ← getEnv
  let cache ← IO.mkRef ({} : Std.HashMap Name (Option String))
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let out ← IO.mkRef ({} : NameSet)
  -- The inductives with a field `Array α`, by name (`none`: none).
  let withField ← IO.mkRef ({} : Std.HashMap Name (Array (Name × Nat)))
  let rec visit (t : Expr) : CoreM Unit := do
    let t := keyTy t
    if (← seen.get).contains t then return
    seen.modify (·.insert t)
    match t with
    | .forallE _ d b _ => visit d; visit b
    | .app .. | .const .. =>
      for a in t.getAppArgs do visit a
      let some iv := inductiveOf env t | return
      if (← out.get).contains iv.name then return
      let fields ← match (← withField.get)[iv.name]? with
        | some fs => pure fs
        | none => do
          let mut fs := #[]
          for c in iv.ctors do
            let lf ← layoutFieldTypes c t
            for h : i in [:lf.size] do
              if isArrayAnyField lf[i] then fs := fs.push (c, i)
          withField.modify (·.insert iv.name fs)
          pure fs
      for (c, i) in fields do
        let inst ← ctorFieldTypes c t
        if let some f := inst[i]? then
          if let some e := arrElemOf? f then
            if (← scalarKind? cache e).isSome then
              out.modify (·.insert iv.name)
              return
    | _ => pure ()
  let rec code (c : Code .pure) : CoreM Unit := do
    match c with
    | .let d k => visit d.type; code k
    | .fun d k _ | .jp d k =>
      for p in d.params do visit p.type
      code d.value; code k
    | .cases cs =>
      for alt in cs.alts do
        match alt with
        | .alt _ ps k _ => for p in ps do visit p.type
                           code k
        | .default k => code k
        | _ => pure ()
    | _ => pure ()
  for d in decls do
    visit d.type
    for p in d.params do visit p.type
    if let .code c := d.value then code c
  out.get

/-- The field types of constructor `ctor` of a value of type `valTy`, as the
lowering holds them: `flatten-structs`' tuples at their type arguments,
every other inductive at its layout (`layoutFieldTypes`), where a field
`Array α` of an inductive in `boxed` (`arrayFieldInductives`) is a box
(`lcAny`). -/
def caFieldTypes (boxed : NameSet) (ctor : Name) (valTy : Expr) : CoreM (Array Expr) := do
  if (flatTupleCtorArity? ctor).isSome then
    return (keyTy valTy).getAppArgs
  let fs ← layoutFieldTypes ctor valTy
  let some (.ctorInfo ci) := (← getEnv).find? ctor | return fs
  unless boxed.contains ci.induct do return fs
  return fs.map fun f => if isArrayAnyField f then anyExpr else f

/-- The flow of declaration `dn`'s code `c`, whose results go to node `res`
of type `rt`. -/
partial def caCode (boxed : NameSet) (byName : Std.HashMap Name CADecl) (inits : Std.HashMap Name Expr) (dn : Name)
    (res : Option Nat) (rt : Expr) (c : Code .pure) : CAM Unit := do
  let tyOf (x : FVarId) : CAM Expr := return (← get).vars.getD x anyExpr
  let nodeOf (x : FVarId) : CAM (Option Nat) := do CAM.node dn x (← tyOf x)
  let setTy (x : FVarId) (t : Expr) : CAM Unit := modify fun s => { s with vars := s.vars.insert x t }
  let why := s!"{dn}"
  match c with
  | .let d k =>
    setTy d.fvarId d.type
    let x ← CAM.node dn d.fvarId d.type
    match d.value with
    | .proj sn i y =>
      let env ← getEnv
      if let some iv := inductiveOf env (mkConst sn) then
        if let some ctor := iv.ctors.head? then
          let fs ← caFieldTypes boxed ctor (← tyOf y)
          let ft := fs[i]?.getD anyExpr
          alignArr ft d.type why
          -- The field as the layout holds it (a position, see `posNode`).
          let (ks, _) ← mentions ft
          unless ks.isEmpty do CAM.union x (← CAM.node dn ⟨d.fvarId.name ++ `_l2r_field⟩ ft)
      CAM.union x (← nodeOf y)
    | .fvar g args =>
      let mut t := keyTy (← tyOf g)
      let gn ← nodeOf g
      for a in args do
        let .fvar ax := a | continue
        match t with
        | .forallE _ dom b _ =>
          alignArr (← tyOf ax) dom why
          t := b
        | _ => pure ()
        CAM.union (← nodeOf ax) gn
      if !t.isForall then alignArr t d.type why
      CAM.union gn x
    | .const f _ args _ =>
      let env ← getEnv
      let argTy (a : Arg .pure) : CAM (Option Expr) := match a with
        | .fvar ax => some <$> tyOf ax
        | _ => pure none
      let argNode (a : Arg .pure) : CAM (Option Nat) := match a with
        | .fvar ax => nodeOf ax
        | _ => pure none
      -- A position that is no binder of the program (an extern's parameter
      -- or result, a constructor's field) and whose type mentions a storage
      -- kind: a node of its own, joined with the value there. A box that
      -- arrives there is unboxed at that type, so the kind must be off if
      -- the value can be an array of boxes (review F1: `v : lcAny` of a
      -- type-code universe read by `Array.size` at `UInt64`).
      let posNode (tag : Name) (i : Nat) (t : Expr) (v : Option Nat) : CAM Unit := do
        let (ks, _) ← mentions t
        if ks.isEmpty then return
        CAM.union v (← CAM.node dn ⟨Name.num (d.fvarId.name ++ tag) i⟩ t)
      if let some t := inits[f]? then
        alignArr t d.type why
        CAM.union x (← CAM.node f (resultVar `init) t)
      else if let some (.ctorInfo ci) := env.find? f then
        if isExtern env f then
          -- (A constructor the runtime implements, `ByteArray.mk`: its
          -- parameters as an extern's.)
          let (ps, r) := caSplitFn (← toMonoTypeKeep (← getOtherDeclBaseType f [])) (ci.numParams + ci.numFields)
          for h : i in [:args.size] do
            if let some pt := ps[i]? then
              if let some at_ ← argTy args[i] then alignArr at_ pt why
              posNode `_l2r_arg i pt (← argNode args[i])
          if args.size ≥ ps.size then posNode `_l2r_ret 0 r x
          for a in args do CAM.union (← argNode a) x
        else
          let arity := ci.numParams + ci.numFields
          if args.size ≥ arity then
            let fs ← caFieldTypes boxed f d.type
            for h : i in [ci.numParams:args.size] do
              if let some ft := fs[i - ci.numParams]? then
                if let some at_ ← argTy args[i] then alignArr at_ ft why
                posNode `_l2r_field i ft (← argNode args[i])
          for a in args do CAM.union (← argNode a) x
      else if let some cd := byName[f]? then
        if cd.ext then
          -- An extern instance: its parameters' types, and everything it
          -- takes joined with what it gives.
          for h : i in [:args.size] do
            if let some (_, pt) := cd.params[i]? then
              if let some at_ ← argTy args[i] then alignArr at_ pt why
              posNode `_l2r_arg i pt (← argNode args[i])
          if args.size == cd.params.size then alignArr cd.ret d.type why
          if args.size ≥ cd.params.size then posNode `_l2r_ret 0 cd.ret x
          let mut prev := x
          for a in args do
            let n ← argNode a
            CAM.union n prev
            if n.isSome then prev := n
        else
          for h : i in [:args.size] do
            if let some (p, pt) := cd.params[i]? then
              if let some at_ ← argTy args[i] then alignArr at_ pt why
              CAM.union (← argNode args[i]) (← CAM.node f p pt)
          let rn ← CAM.node f (resultVar) cd.ret
          if args.size == cd.params.size then
            alignArr cd.ret d.type why
            CAM.union rn x
          else if args.size < cd.params.size then
            -- A function value: its remaining parameters and its result.
            alignArr (mkFnTy (cd.params[args.size:].toArray.map (·.2)) cd.ret) d.type why
            for (p, pt) in cd.params[args.size:].toArray do CAM.union x (← CAM.node f p pt)
            CAM.union x rn
          else
            -- The result applied to the remaining arguments.
            let mut t := keyTy cd.ret
            for a in args[cd.params.size:].toArray do
              match t, ← argTy a with
              | .forallE _ dom b _, some at_ => alignArr at_ dom why; t := b
              | _, _ => pure ()
              CAM.union (← argNode a) rn
            if !t.isForall then alignArr t d.type why
            CAM.union rn x
      else
        -- A constant known only by its mono signature (a monomorphic
        -- extern of Lean's library), or not at all: its argument types if
        -- known, and everything joined.
        if let some md ← getMonoDecl? f then
          let (ps, r) := caSplitFn md.type md.params.size
          for h : i in [:args.size] do
            if let some pt := ps[i]? then
              if let some at_ ← argTy args[i] then alignArr at_ pt why
              posNode `_l2r_arg i pt (← argNode args[i])
          if args.size == ps.size then alignArr r d.type why
          if args.size ≥ ps.size then posNode `_l2r_ret 0 r x
        let mut prev := x
        for a in args do
          let n ← argNode a
          CAM.union n prev
          if n.isSome then prev := n
    | _ => pure ()
    caCode boxed byName inits dn res rt k
  | .fun d k _ =>
    setTy d.fvarId d.type
    let fnode ← CAM.node dn d.fvarId d.type
    for p in d.params do
      setTy p.fvarId p.type
      CAM.union fnode (← CAM.node dn p.fvarId p.type)
    let (_, r) := caSplitFn d.type d.params.size
    let rn ← CAM.node dn (resultVar d.fvarId.name) r
    CAM.union fnode rn
    caCode boxed byName inits dn rn r d.value
    caCode boxed byName inits dn res rt k
  | .jp d k =>
    for p in d.params do setTy p.fvarId p.type
    modify fun s => { s with jps := s.jps.insert d.fvarId (d.params.map fun p => (p.fvarId, p.type)) }
    caCode boxed byName inits dn res rt d.value
    caCode boxed byName inits dn res rt k
  | .jmp j args =>
    let ps := (← get).jps.getD j #[]
    for (a, (p, pt)) in args.zip ps do
      let .fvar ax := a | continue
      alignArr (← tyOf ax) pt why
      CAM.union (← nodeOf ax) (← CAM.node dn p pt)
  | .return x =>
    alignArr (← tyOf x) rt why
    CAM.union (← nodeOf x) res
  | .cases cs =>
    let dty ← tyOf cs.discr
    let dn' ← nodeOf cs.discr
    for alt in cs.alts do
      match alt with
      | .alt ctor ps k _ =>
        let fs ← caFieldTypes boxed ctor dty
        for h : i in [:ps.size] do
          let p := ps[i]
          setTy p.fvarId p.type
          let ft := fs[i]?.getD anyExpr
          alignArr ft p.type why
          let pn ← CAM.node dn p.fvarId p.type
          CAM.union dn' pn
          -- The field as the layout holds it (a position, see `posNode`).
          let (ks, _) ← mentions ft
          unless ks.isEmpty do CAM.union pn (← CAM.node dn ⟨p.fvarId.name ++ `_l2r_field⟩ ft)
        caCode boxed byName inits dn res rt k
      | .default k => caCode boxed byName inits dn res rt k
      | _ => pure ()
  | _ => pure ()

/-- The storage kinds the program can store compactly (see the module
comment), and why each other kind is off. `casts`: whether the program can
read a value as another type (`programCasts`); `inits`: its constants
defined by `initialize`, each with the declaration of its initializer. -/
def compactArrayKinds (decls : Array (Decl .pure)) (casts : Option Name) (inits : Array (Name × Name))
    (roots : Array Name) :
    CoreM (Array String × Array (String × String) × NameSet) := do
  if let some n := casts then
    return (#[], compactKinds.map fun k => (k, s!"the program can cast ({n})"), {})
  -- Only what the entry point reaches runs (a declaration nothing calls
  -- may keep a type Stage 3 refined in its callee only).
  let bodies : Std.HashMap Name (Code .pure) := decls.foldl (fun m d => match d.value with
    | .code c => m.insert d.name c
    | _ => m) {}
  let mut live : NameSet := {}
  let mut work := (roots ++ inits.map (·.2)).toList
  while !work.isEmpty do
    let n :: rest := work | break
    work := rest
    if live.contains n then continue
    live := live.insert n
    let some c := bodies[n]? | continue
    for (f, _, _) in constApps c #[] do
      unless live.contains f do work := f :: work
  -- (The boxed fields from every declaration: the lowering lowers the
  -- unreachable ones too, and a boxed field there removes a crossing that
  -- would lower to a panic.)
  let boxed ← arrayFieldInductives decls
  let decls := decls.filter fun d => live.contains d.name
  let mut byName : Std.HashMap Name CADecl := {}
  for d in decls do
    let (ps, r) := caSplitFn d.type d.params.size
    let params := d.params.mapIdx fun i p => (p.fvarId, (ps[i]?.getD p.type))
    byName := byName.insert d.name { params, ret := r, ext := !(d.value matches .code _) }
  let mut initTys : Std.HashMap Name Expr := {}
  for (c, _) in inits do
    initTys := initTys.insert c (← toMonoTypeKeep (← getOtherDeclBaseType c []))
  let act : CAM Unit := do
    for d in decls do
      let .code c := d.value | continue
      modify fun s => { s with vars := {}, jps := {} }
      let some cd := byName[d.name]? | continue
      for h : i in [:d.params.size] do
        let p := d.params[i]
        modify fun s => { s with vars := s.vars.insert p.fvarId p.type }
        -- Callers pass arguments at the declaration's type's parameter
        -- types; its body sees its parameters' own.
        if let some (_, q) := cd.params[i]? then alignArr q p.type s!"{d.name}"
        let _ ← CAM.node d.name p.fvarId p.type
      let rn ← CAM.node d.name resultVar cd.ret
      caCode boxed byName initTys d.name rn cd.ret c
    -- The startup glue stores an initializer's result into its constant.
    for (c, inst) in inits do
      let (some t, some cd) := (initTys[c]?, byName[inst]?) | continue
      CAM.union (← CAM.node c (resultVar `init) t) (← CAM.node inst resultVar cd.ret)
    -- The classes that reach an array of `Box`es.
    let n := (← get).parent.size
    let mut tainted : Std.HashMap Nat Name := {}
    for i in [:n] do
      let (_, anyArr) ← mentions (← get).tys[i]!
      if anyArr then
        let r ← CAM.find i
        unless tainted.contains r do tainted := tainted.insert r (← get).wheres[i]!
    for i in [:n] do
      let r ← CAM.find i
      if let some w := tainted[r]? then
        let (ks, _) ← mentions (← get).tys[i]!
        for k in ks do
          CAM.turnOff (some k) s!"{(← get).wheres[i]!}: a value of type {keyTy (← get).tys[i]!} meets an array of boxes (in {w})"
  let cache ← IO.mkRef {}
  let ((), st) ← (act.run cache).run {}
  let on := compactKinds.filter fun k => !st.off.contains k
  return (on, compactKinds.filterMap (fun k => st.off[k]?.map (k, ·)), if on.isEmpty then {} else boxed)

end LeanToReussir
