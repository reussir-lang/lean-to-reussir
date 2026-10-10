import Lean
import LeanToReussir.PassConfig

/-!
# Which binders can hold a resource (for `flatten-structs`)

In a program that creates resources whose release is observable (files,
child processes, promises: `programMakesResources`), `flatten-structs`
leaves alone every declaration with a parameter or a result that can hold
one (see `Flatten.resourceExcluded`). By type alone, every value of type
`lcAny` can be a handle (a handle's mono type in generic code is `lcAny`),
so a loop over a record with an `lcAny` field (lean-regex's `SearchState`,
whose `Vector σ.Update n` is `Array lcAny`) stays a heap record in every
program that reads a file. This analysis follows the values instead.

Every resource comes from a call of an extern of `resourceExterns`. A value
moves only along the program's flows, and each flow joins two binders into
one class (union-find, as `CompactArrays`' flow classes):
- an argument and its parameter (a declaration's, a join point's), a
  result and the binder it goes to, a returned value and the result of its
  declaration or local function, an alias;
- a container and what it holds: a constructor's arguments and its value,
  a projection and the value it reads, a `cases`' fields and its
  discriminant;
- an extern (or a constant without code): all its arguments with each other
  and with its result (a reference set and read later, a thunk, a task, an
  array);
- the standard streams: what `IO.setStdout` (and `setStdin`, `setStderr`)
  takes and what any `IO.getStdout` returns (the runtime keeps the stream;
  a stream over a file holds the handle in its closures);
- a function value: its parameters, its result, the arguments it is
  applied to, and what it captures (the outer variables its body uses, the
  arguments of a partial application). So a closure that captures a handle
  holds one, unlike Lower/Borrow's type rule, which does not look into
  closures.

Only binders whose type can carry a resource have a node (`mayCarry`:
`lcAny`, a handle, a function type, a thunk, a task, an array of such
elements, an inductive with a field that can). A value of another type
(`Nat`, `String`, `List Nat`, an IO result `EST.Out ε σ Unit`, whose state
field is `Void σ`) holds no resource. A class *holds a resource*
(`Info.held`) when it has a seed:
- the result of a call (or a function value) of an extern of
  `resourceExterns`;
- a binder whose type holds a handle or a child process outside function
  types (`mentionsResource`);
- the value of an `initialize` constant whose initializer is not found,
  and of any other constant that is neither a declaration of the program
  nor an extern (the analysis cannot see where its value comes from).
An `initialize` constant is joined with its initializer's result.

Example (lean-regex, test `RtFlattenResFlow`): the driver reads its input
with `IO.FS.readFile`, whose handle (`IO.FS.Handle.mk`'s result) goes to
`Handle.read` and to `readBinToEndInto.loop`, and to nothing that holds
regex data: only that class holds a resource, and `εClosure`'s
`SearchState` (its `updates : Array lcAny` get `σ.empty` and `σ.write`'s
results) is split. A record whose `lcAny` field gets a handle or a promise
is in the class of the extern's result (test `RtFlattenResHeld`).

The analysis is flow-insensitive and joins in both directions, so a class
can only be too large: a binder outside every seeded class never holds a
resource at run time. In a program that can read a value as another type
(`programCasts`), a value could leave its class through a type that has no
node, so the caller falls back to the type rule (`run` returns `none`).
-/

namespace LeanToReussir.Opt.ResourceFlow
open Lean Compiler LCNF

/-- Types whose values hold no other value, so no resource. -/
def leafTypeNames : List Name :=
  [``lcErased, ``lcVoid, ``Nat, ``Int, ``String, ``ByteArray, ``FloatArray, ``Unit, ``PUnit,
   ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32, ``Bool]

/-- Whether mono type `t` holds a file handle or a child process (its pipes)
outside function types. -/
partial def mentionsResource (t : Expr) : Bool :=
  match t.consumeMData with
  | .const n _ => n == ``IO.FS.Handle || n == ``IO.Process.Child
  | .app f a => mentionsResource f || mentionsResource a
  | .lam _ _ b _ => mentionsResource b
  | _ => false

structure RFDecl where
  params : Array (FVarId × Expr)
  ret : Expr
  /-- An extern instance (no code). -/
  ext : Bool

structure RFState where
  /-- Node of each (declaration, binder); `resultKey` names results. -/
  ids : Std.HashMap (Name × FVarId) Nat := {}
  parent : Array Nat := #[]
  /-- The type of each node, and where it is (for `L2R_RESFLOW_DEBUG`). -/
  tys : Array Expr := #[]
  wheres : Array (Name × FVarId) := #[]
  /-- Nodes that hold a resource from the start, each with the reason. -/
  seeds : Array (Nat × String) := #[]
  /-- Binder types of the declaration being walked. -/
  vars : Std.HashMap FVarId Expr := {}
  /-- Join point parameters of the declaration being walked. -/
  jps : Std.HashMap FVarId (Array (FVarId × Expr)) := {}
  carry : Std.HashMap Expr Bool := {}

abbrev RFM := StateRefT RFState CoreM

/-- The synthetic binder of a result (of a declaration, or of local function
`f`). -/
def resultKey (f : Name := .anonymous) : FVarId := ⟨`_l2r_rf_result ++ f⟩

/-- Whether a value of mono type `t` can hold a resource or give one: an
`lcAny`, a handle, a function type (a closure may capture one), a thunk or a
task (they hold a closure), an array of such elements, an inductive with a
field (`ctorFieldTypes`, at `t`'s type arguments) that can, a type the
analysis does not know. A plain reachability with one visited set: a `false` holds for
every type visited, and is cached for all of them. -/
partial def mayCarry (t : Expr) : RFM Bool := do
  let t := keyTy t
  if let some b := (← get).carry[t]? then return b
  let visited ← IO.mkRef ({} : Std.HashSet Expr)
  let r ← go t visited
  unless r do
    for v in (← visited.get) do modify fun s => { s with carry := s.carry.insert v false }
  modify fun s => { s with carry := s.carry.insert t r }
  return r
where
  go (t : Expr) (visited : IO.Ref (Std.HashSet Expr)) : RFM Bool := do
    if let some b := (← get).carry[t]? then return b
    if (← visited.get).contains t then return false
    visited.modify (·.insert t)
    match t with
    | .forallE .. => return true
    | .sort _ => return false
    | _ =>
      let .const n _ := t.getAppFn | return true
      if n == ``lcAny || n == ``IO.FS.Handle || n == ``Thunk || n == ``Task then return true
      if leafTypeNames.contains n then return false
      if n == ``Array then
        return ← match t.getAppArgs[0]? with
          | some a => go (keyTy a) visited
          | none => pure true
      -- An inductive's value holds what its fields hold (a type argument
      -- no field mentions is a phantom: `EST.Out`'s state is `Void σ`).
      let env ← getEnv
      let some iv := inductiveOf env t | return true
      for c in iv.ctors do
        let some (.ctorInfo ci) := env.find? c | return true
        let fs ← ctorFieldTypes c t
        if fs.size != ci.numFields then return true
        for f in fs do
          if ← go (keyTy f) visited then return true
      return false

def seed (i : Option Nat) (why : String) : RFM Unit := do
  if let some i := i then modify fun s => { s with seeds := s.seeds.push (i, why) }

/-- The node of binder `x` of declaration `decl`, of type `t` (made at its
first sight), if `t` can carry a resource (`force`: in any case). -/
def node (decl : Name) (x : FVarId) (t : Expr) (force := false) : RFM (Option Nat) := do
  if let some i := (← get).ids[(decl, x)]? then return some i
  unless force || (← mayCarry t) do return none
  let i := (← get).parent.size
  modify fun s => { s with ids := s.ids.insert (decl, x) i, parent := s.parent.push i, tys := s.tys.push t,
                           wheres := s.wheres.push (decl, x) }
  if mentionsResource t then seed (some i) "its type holds a handle or a child process"
  return some i

partial def find (i : Nat) : RFM Nat := do
  let p := (← get).parent[i]!
  if p == i then return i
  let r ← find p
  modify fun s => { s with parent := s.parent.set! i r }
  return r

def union (a b : Option Nat) : RFM Unit := do
  let (some a, some b) := (a, b) | return
  let ra ← find a
  let rb ← find b
  if ra != rb then modify fun s => { s with parent := s.parent.set! ra rb }

/-- What the walk needs about the program. -/
structure RFCtx where
  keys : NameMap InstKey
  byName : Std.HashMap Name RFDecl
  /-- The instance of each declaration instantiated without type arguments
  (an `initialize` constant's initializer). -/
  plainInst : Std.HashMap Name Name

/-- The C symbol of `f` (an instance), if it is an extern. -/
def externSym (ctx : RFCtx) (env : Environment) (f : Name) : Option String :=
  getExternNameFor env `c ((ctx.keys.find? f).map (·.decl) |>.getD f)

/-- The externs that store a standard stream for the runtime and give it
back: what `IO.setStdout` takes, a later `IO.getStdout` returns (a stream
over a file holds its handle in its closures). -/
def stdStreamExterns : List String :=
  ["lean_get_stdin", "lean_get_stdout", "lean_get_stderr",
   "lean_get_set_stdin", "lean_get_set_stdout", "lean_get_set_stderr"]

/-- The node of the standard streams (see `stdStreamExterns`). -/
def stdNode : RFM (Option Nat) := node .anonymous ⟨`_l2r_rf_std⟩ anyExpr (force := true)

/-- The flows of declaration `dn`'s code `c`, whose results go to node
`res`. -/
partial def walk (ctx : RFCtx) (dn : Name) (res : Option Nat) (c : Code .pure) : RFM Unit := do
  let tyOf (x : FVarId) : RFM Expr := return (← get).vars.getD x anyExpr
  let nodeOf (x : FVarId) : RFM (Option Nat) := do node dn x (← tyOf x)
  let argNode (a : Arg .pure) : RFM (Option Nat) := match a with
    | .fvar y => nodeOf y
    | _ => pure none
  let setTy (x : FVarId) (t : Expr) : RFM Unit := modify fun s => { s with vars := s.vars.insert x t }
  -- Everything joined (an extern, an unknown constant): the arguments
  -- with each other too, also when the result has no node (`ST.Ref.set`
  -- gives `EST.Out ε σ Unit`; review of the analysis, finding 2).
  let chain (x : Option Nat) (args : Array (Arg .pure)) : RFM Unit := do
    let mut prev := x
    for a in args do
      let n ← argNode a
      union n prev
      if prev.isNone then prev := n
  match c with
  | .let d k =>
    setTy d.fvarId d.type
    let x ← node dn d.fvarId d.type
    match d.value with
    | .proj _ _ y => union x (← nodeOf y)
    | .fvar g args =>
      let gn ← nodeOf g
      for a in args do union (← argNode a) gn
      union gn x
    | .const f _ args _ =>
      let env ← getEnv
      let sym := externSym ctx env f
      if sym.any (stdStreamExterns.contains ·) then
        -- A standard stream: stored by the runtime, given back by another
        -- call.
        let sn ← stdNode
        union x sn
        chain sn args
      -- A resource is made here (or a function value that makes one).
      let x ← if sym.any (resourceExterns.contains ·) then
          let x ← node dn d.fvarId d.type (force := true)
          seed x s!"a call of {f}"
          pure x
        else pure x
      if let some initFn := getInitFnNameFor? env f then
        -- An `initialize` constant: its initializer's result (an IO result
        -- that holds the value).
        match ctx.plainInst[initFn]?.bind (fun i => (ctx.byName[i]?).map (i, ·)) with
        | some (i, cd) => union x (← node i resultKey cd.ret)
        | none => seed (← node dn d.fvarId d.type (force := true)) s!"initialize constant {f}"
        chain x args
      else if let some (.ctorInfo _) := env.find? f then
        chain x args
      else if let some cd := ctx.byName[f]? then
        if cd.ext then chain x args
        else
          for h : i in [:args.size] do
            if let some (p, pt) := cd.params[i]? then union (← argNode args[i]) (← node f p pt)
          let rn ← node f resultKey cd.ret
          if args.size == cd.params.size then union rn x
          else if args.size < cd.params.size then
            -- A function value: its remaining parameters, its result and
            -- the arguments it captures.
            for (p, pt) in cd.params[args.size:].toArray do union x (← node f p pt)
            union x rn
            chain x args
          else
            -- The result applied to the remaining arguments.
            for a in args[cd.params.size:].toArray do union (← argNode a) rn
            union rn x
      else
        -- A constant known only by its mono signature (an extern of Lean's
        -- library), or not at all. Only a call of `resourceExterns` makes a
        -- resource, so an extern's value or result holds what it takes; the
        -- value of another such constant comes from where the analysis
        -- cannot see.
        chain x args
        let orig := (ctx.keys.find? f).map (·.decl) |>.getD f
        if args.isEmpty && !isExtern env orig && !isExtern env f then
          seed x s!"constant {f} without code"
    | _ => pure ()
    walk ctx dn res k
  | .fun d k _ =>
    let outer := (← get).vars
    setTy d.fvarId d.type
    let fnode ← node dn d.fvarId d.type (force := true)
    -- What the closure captures.
    let used : Std.HashSet FVarId := d.value.collectUsed {}
    for y in used do
      if outer.contains y then union fnode (← nodeOf y)
    for p in d.params do
      setTy p.fvarId p.type
      union fnode (← node dn p.fvarId p.type)
    let (_, r) := splitArrows d.type d.params.size
    let rn ← node dn (resultKey d.fvarId.name) r
    union fnode rn
    walk ctx dn rn d.value
    walk ctx dn res k
  | .jp d k =>
    for p in d.params do
      setTy p.fvarId p.type
      let _ ← node dn p.fvarId p.type
    modify fun s => { s with jps := s.jps.insert d.fvarId (d.params.map fun p => (p.fvarId, p.type)) }
    walk ctx dn res d.value
    walk ctx dn res k
  | .jmp j args =>
    let ps := (← get).jps.getD j #[]
    for (a, (p, pt)) in args.zip ps do union (← argNode a) (← node dn p pt)
  | .return x => union (← nodeOf x) res
  | .cases cs =>
    let dn' ← nodeOf cs.discr
    for alt in cs.alts do
      match alt with
      | .alt _ ps k _ =>
        for p in ps do
          setTy p.fvarId p.type
          union dn' (← node dn p.fvarId p.type)
        walk ctx dn res k
      | .default k => walk ctx dn res k
      | _ => pure ()
  | _ => pure ()

/-- The analysis' answer: the binders that can hold a resource. -/
structure Info where
  held : Std.HashSet (Name × FVarId) := {}
  /-- Nodes and classes, seeded classes (for `L2R_FLATTEN_DEBUG`). -/
  stats : String := ""

/-- Whether binder `x` of declaration `decl` can hold a resource. -/
def Info.holds (info : Info) (decl : Name) (x : FVarId) : Bool := info.held.contains (decl, x)

/-- The analysis of program `decls` (see the module comment); `none` when
the program can read a value as another type (`programCasts`). -/
def run (keys : NameMap InstKey) (decls : Array (Decl .pure)) : CoreM (Option Info) := do
  if (programCasts (← getEnv) keys decls).isSome then return none
  let mut byName : Std.HashMap Name RFDecl := {}
  for d in decls do
    let (_, r) := splitArrows d.type d.params.size
    byName := byName.insert d.name
      { params := d.params.map (fun p => (p.fvarId, p.type)), ret := r, ext := !(d.value matches .code _) }
  let plainInst := keys.foldl (init := ({} : Std.HashMap Name Name)) fun m n k =>
    if k.typeArgs.isEmpty && k.dicts.isEmpty then m.insert k.decl n else m
  let ctx : RFCtx := { keys, byName, plainInst }
  let act : RFM Info := do
    for d in decls do
      let .code c := d.value | continue
      modify fun s => { s with vars := {}, jps := {} }
      for p in d.params do
        modify fun s => { s with vars := s.vars.insert p.fvarId p.type }
        let _ ← node d.name p.fvarId p.type
      let some cd := byName[d.name]? | continue
      let rn ← node d.name resultKey cd.ret
      walk ctx d.name rn c
    let mut roots : Std.HashSet Nat := {}
    for (i, _) in (← get).seeds do roots := roots.insert (← find i)
    if (← IO.getEnv "L2R_RESFLOW_DEBUG").isSome then
      let st ← get
      for (i, why) in st.seeds do
        let (dn, x) := st.wheres[i]!
        IO.eprintln s!"resflow: seed {dn} {x.name} : {st.tys[i]!}: {why}"
      for i in [:st.parent.size] do
        if roots.contains (← find i) then
          let (dn, x) := st.wheres[i]!
          IO.eprintln s!"resflow: class {← find i}: {dn} {x.name} : {st.tys[i]!}"
    let mut held : Std.HashSet (Name × FVarId) := {}
    let mut classes : Std.HashSet Nat := {}
    for (k, i) in (← get).ids.toList do
      let r ← find i
      classes := classes.insert r
      if roots.contains r then held := held.insert k
    let stats := s!"{(← get).parent.size} nodes, {classes.size} classes, {roots.size} holding a resource \
      ({held.size} binders)"
    return { held, stats }
  let (info, _) ← act.run {}
  return some info

end LeanToReussir.Opt.ResourceFlow
