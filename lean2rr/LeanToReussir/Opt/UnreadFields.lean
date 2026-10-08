import Lean
import LeanToReussir.PassConfig
import LeanToReussir.Emit.Program
import LeanToReussir.Opt.Flatten

/-!
# Function values in unread fields left out (optimization `unread-fields`)

Off by default, as the owner decided (2026-10-08): `--enable-opt
unread-fields` turns it on. This is an exception to the rule that every
optional pass is on by default.

An `initialize` block of a library often stores callbacks for Lean's
elaborator: a linter's `run` (`addLinter`), an attribute's `add` and
`erase` (`registerBuiltinAttribute`, `registerTagAttribute`), the hooks of
an environment extension (`registerPersistentEnvExtension`). The program
runs these blocks at startup, as natively, but it never calls the
callbacks: only the elaborator reads those fields. lean2rr keeps every
function that kept code mentions, so the callbacks' code reaches C++
functions of the `Lean` package that lean2rr's runtime does not have
(`Lean.Expr.instantiate`, `Lean.Meta.isExprDefEqAux`, …), and the program
is refused.

The pass runs on Stage 2's declarations, before Stage 3. It computes,
from the declarations the entry point calls, a usefulness fixpoint that
knows constructor fields:
- a field (constructor `C`, field `j`) is *read* when kept code projects
  it, or matches `C` and uses the field's binder;
- a variable is *useful* when kept code returns it, matches it, applies
  it, passes it to an extern, or projects a field of it; when a useful
  `let` computes from it; when a read field or a useful parameter
  receives it;
- a parameter of a declaration (or of a join point) is useful when it is
  useful in the body;
- a `let` is kept when its variable is useful or when its value may have
  an effect (a full application, of a declaration, an extern or a
  function value); a declaration is kept when a kept `let` mentions it.
Then, in the kept declarations, an argument that a constructor stores in
an unread field, a declaration's unused parameter or a join point's
unused parameter receives becomes `◾` (the lowering passes a placeholder:
at a function type the nullary variant `z`); a `let` that is not useful
and has no effect goes, and so does every declaration no kept `let`
mentions. A closure that only an unread field held goes with the
values it captured: `registerTagAttribute`'s `validate` argument is
unused, so the caller's lambda goes too.

Only an argument whose type may hold a function value (a function type,
`lcAny`, a type variable, a task, thunk or reference, or an inductive with
such a field) is replaced: data stays as it is (`deriving Lean.ToExpr`
stores an `Expr`, which Lean's C++ builds, in the instance's
`toTypeExpr`: that stays).

The startup steps of the program and of `Init` and `Std` stay. A step of
the `Lean` package's `initialize` constants that the program uses (Stage 1
adds one for each such constant its code reads) stays when kept code
still reads the constant: the others do not run (`Main.pipeline` drops
them), as the steps of the constants the program does not use never did.

Soundness. A field counts as read in all the cases where something lean2rr
does not see may read it:
- every field of an inductive that an extern (or runtime function) that
  kept code mentions takes, by all its declared parameter types (also when
  the extern is a function value or partially applied), also inside other
  inductives and function types (`IO.setStderr` takes an `IO.FS.Stream`);
  a parameter declared at a type variable is parametric: the runtime
  stores the value and gives it back, but cannot look inside it
  (`Array.push`);
- every field of the types the lowering or the runtime reads by itself:
  `IO.FS.Stream` (the runtime writes panics and traces with the current
  stderr's `putStr`), the IO results `EST.Out` and `ST.Out` (the entry
  point and the startup chain read them), tasks, thunks, references,
  promises;
- a program that can read a value as another type (`programCasts`, the
  whole-program fact of the lowering, computed on the declarations kept):
  the pass then changes nothing;
- in a program whose kept code creates tasks, a closure is replaced only
  when the values it captured cannot hold a task (`holdsNoTask`, or the
  same test on the values of a constant): natively a constant's first
  evaluation waits for the tasks its value holds, closures' captured
  values included;
- in a program whose kept code makes resources (files, child processes),
  a value that may hold one is not replaced, neither at a field nor at an
  unused parameter: natively it would keep the resource alive, and a file
  handle released earlier is flushed and closed earlier (`taint`, below).
Address and sharing tests (`ptrAddrUnsafe`, `withPtrAddr`,
`isExclusiveUnsafe`, `dbgTraceIfShared`, `ShareCommon`) read no field:
the object they test stays the same object at the same address. A value
that a closure left out captured has one reference less, which
`dbgTraceIfShared` can see; lean2rr's counts are not native's anyway
(docs/implementation/representations/identity.md, "Sharing is not
observable").

Not covered: a closed term whose evaluation would panic, read only to
build a callback that the pass leaves out, is not evaluated; natively its
panic message would show.
-/

namespace LeanToReussir.Opt.UnreadFields
open Lean Compiler LCNF

/-- Inductives whose fields the lowering or the runtime reads by itself:
the standard streams (the runtime writes panics and traces with the
current stderr's `putStr`), the results of IO actions (the entry point
reads `main`'s, the startup chain stores an initializer's value and
reports its error), tasks, thunks, references and promises. -/
def alwaysRead : List Name := [``IO.FS.Stream, ``EST.Out, ``ST.Out] ++ opaqueTypes

/-- What the fixpoint knows about the whole program. -/
structure Facts where
  /-- Declarations with code that kept code mentions. -/
  live : NameSet := {}
  /-- Externs and runtime functions that kept code mentions. -/
  externs : NameSet := {}
  /-- Fields read: (constructor, field index). -/
  read : Std.HashSet (Name × Nat) := {}
  /-- Inductives all of whose fields count as read. -/
  allRead : NameSet := {}
  /-- The useful parameters of each declaration. -/
  params : Std.HashMap Name (Array Bool) := {}
  /-- Why each declaration or extern is kept: the declaration that
  mentions it and the reason (for `L2R_UNREAD_FIELDS_WHY`). -/
  why : Std.HashMap Name (Name × String) := {}
  /-- A declaration that reads each field read. -/
  readBy : Std.HashMap (Name × Nat) Name := {}
  /-- Externs whose declared parameter types were looked at. -/
  declaredDone : NameSet := {}
  /-- In a program whose kept code makes resources: the fields that may
  hold one, the declaration parameters that may receive one, the
  declarations that may return one, the declarations used as function
  values, whether one of those may return one, and whether a value that
  may hold one went where lean2rr does not follow it (an extern that may
  keep it, a function value: `rEscape`). -/
  rFields : Std.HashSet (Name × Nat) := {}
  rParams : Std.HashMap Name (Array Bool) := {}
  rRet : NameSet := {}
  fnValues : NameSet := {}
  rFnRet : Bool := false
  rEscape : Bool := false
  changed : Bool := false

/-- What the analysis of one declaration knows. -/
structure Local where
  useful : Std.HashSet FVarId := {}
  /-- Why each useful variable is (the first reason). -/
  why : Std.HashMap FVarId String := {}
  /-- The useful parameters of each join point. -/
  jps : Std.HashMap FVarId (Array Bool) := {}
  /-- Binder types. -/
  types : Std.HashMap FVarId Expr := {}
  /-- `let` values. -/
  values : Std.HashMap FVarId (LetValue .pure) := {}
  /-- In a program whose kept code makes resources: the variables that may
  hold one. -/
  rvars : Std.HashSet FVarId := {}
  /-- The parameters of each join point that may get one. -/
  rjps : Std.HashMap FVarId (Array Bool) := {}

structure Ctx where
  byName : Std.HashMap Name (Decl .pure)
  keys : NameMap InstKey
  roots : NameSet
  /-- The `Lean` package's `initialize` constants the program uses, each
  with its initializer: kept while kept code reads the constant. -/
  usedInits : NameMap Name
  /-- Every `initialize` constant of the startup steps, with its
  initializer. -/
  inits : NameMap Name := {}
  /-- Whether a value that may hold a resource stays where it is (the kept
  code makes resources, `programMakesResources`). -/
  resources : Bool := false
  /-- Whether a closure stored in an unread field must be shown to hold no
  task first (the kept code creates tasks). -/
  tasks : Bool
  /-- Whether the reasons are recorded (`L2R_UNREAD_FIELDS_WHY`). -/
  explain : Bool := false

/-- A reason, made only when the reasons are recorded. -/
abbrev Why := Unit → String

structure St where
  facts : Facts := {}
  loc : Local := {}
  cur : Name := .anonymous
  codeMemo : Std.HashMap Expr Bool := {}
  taskMemo : Std.HashMap Expr Bool := {}
  constTask : Std.HashMap Name Bool := {}
  constBusy : NameSet := {}
  /-- Rounds of the fixpoint (for `L2R_DEBUG`). -/
  rounds : Nat := 0

abbrev M := ReaderT Ctx (StateRefT St CoreM)

/-- How a constant in a `let` value is called. -/
inductive Callee where
  /-- A constructor lean2rr builds itself (not an extern). -/
  | ctor (c : ConstructorVal)
  /-- A declaration of the program with code. -/
  | code (d : Decl .pure)
  /-- An extern or runtime function (`orig`: Lean's declaration). -/
  | ext (orig : Name)

def classify (c : Name) : M Callee := do
  let env ← getEnv
  if let some (.ctorInfo cv) := env.find? c then
    unless isExtern env c do return .ctor cv
  match (← read).byName[c]? with
  | some d =>
    match d.value with
    | .code _ => return .code d
    | .extern _ => return .ext (((← read).keys.find? c).map (·.decl) |>.getD c)
  | none => return .ext c

/-- Whether a `let` value may have an effect, so that it stays when its
variable is not useful: a full application of a declaration, an extern or
a function value. A partial application, a constructor, a projection, a
literal and the read of a constant have none. -/
def effectful (v : LetValue .pure) : M Bool := do
  match v with
  | .const c _ args _ =>
    match ← classify c with
    | .ctor _ => return false
    | .code d => return args.size ≥ d.params.size && args.size > 0
    | .ext _ => return args.size > 0
  | .fvar _ args => return args.size > 0
  | _ => return false

def setChanged : M Unit := modify fun s => { s with facts := { s.facts with changed := true } }

def isUseful (x : FVarId) : M Bool := return (← get).loc.useful.contains x

def useVar (x : FVarId) (why : Why) : M Unit := do
  unless (← isUseful x) do
    let explain := (← read).explain
    let l := (← get).loc
    let why := if explain then l.why.insert x (why ()) else l.why
    modify fun s => { s with loc := { l with useful := l.useful.insert x, why } }

def useArg (a : Arg .pure) (why : Why) : M Unit := do
  if let .fvar x := a then useVar x why

/-- Whether argument `a` may hold a resource that must stay where it is
(only in a program whose kept code makes resources). -/
def isR (a : Arg .pure) : M Bool := do
  let .fvar x := a | return false
  return (← read).resources && (← get).loc.rvars.contains x

/-- Whether a value of mono type `t` may hold a function value: a function
type, `lcAny`, a type variable or any other head, a task, thunk, reference
or promise, or an inductive with such a field at the type's arguments. -/
partial def mayHoldCode (t : Expr) : M Bool := do
  let t := t.consumeMData.headBeta
  if let some b := (← get).codeMemo[t]? then return b
  -- Assumed data while its fields are followed (a recursive inductive is
  -- data if the rest is).
  modify fun s => { s with codeMemo := s.codeMemo.insert t false }
  let r ← go t
  modify fun s => { s with codeMemo := s.codeMemo.insert t r }
  return r
where
  go (t : Expr) : M Bool := do
    if t.isErased || t.isConstOf ``lcVoid then return false
    if t.isForall then return true
    let .const n _ := t.getAppFn | return true
    if n == ``lcAny || opaqueTypes.contains n then return true
    if atomicDataTypes.contains n then return false
    let some iv := inductiveOf (← getEnv) t | return true
    if t.getAppArgs.size < iv.numParams then return true
    for c in iv.ctors do
      for f in ← ctorFieldTypes c t do
        if ← mayHoldCode f then return true
    return false

/-- `holdsNoTask`, cached. -/
def typeNoTask (t : Expr) : M Bool := do
  if let some b := (← get).taskMemo[t]? then return b
  let b ← (holdsNoTask t).run' {}
  modify fun s => { s with taskMemo := s.taskMemo.insert t b }
  return b

/-- The binder types and `let` values of a body. -/
partial def collectBinders (c : Code .pure) (loc : Local) : Local :=
  match c with
  | .let d k =>
    collectBinders k { loc with types := loc.types.insert d.fvarId d.type, values := loc.values.insert d.fvarId d.value }
  | .fun d k _ | .jp d k =>
    let loc := d.params.foldl (fun l p => { l with types := l.types.insert p.fvarId p.type }) loc
    collectBinders k (collectBinders d.value loc)
  | .cases cs => cs.alts.foldl (init := loc) fun loc alt =>
    match alt with
    | .alt _ ps code _ =>
      collectBinders code (ps.foldl (fun l p => { l with types := l.types.insert p.fvarId p.type }) loc)
    | .default code => collectBinders code loc
    | _ => loc
  | _ => loc

/-- The variable straight-line code returns. -/
def returnedVar : Code .pure → Option FVarId
  | .let _ k => returnedVar k
  | .return x => some x
  | _ => none

mutual
/-- Whether the value of `x` (bound in the body described by `loc`) cannot
hold a task: a literal, a partial application or constructor whose
arguments cannot, the read of a constant whose value cannot, or a type
that cannot (`holdsNoTask`). -/
partial def noTaskValue (loc : Local) (x : FVarId) (depth : Nat) : M Bool := do
  let byType : M Bool := typeNoTask (loc.types.getD x anyExpr)
  if depth == 0 then return ← byType
  match loc.values[x]? with
  | some (.lit _) | some .erased => return true
  | some (.const c _ args _) =>
    let argsOk : M Bool := args.allM fun
      | .fvar y => noTaskValue loc y (depth - 1)
      | _ => pure true
    match ← classify c with
    | .ctor _ => argsOk
    | .code d =>
      if args.size < d.params.size then argsOk
      else if d.params.isEmpty && args.isEmpty then
        if ← constNoTask d depth then return true else byType
      else byType
    | .ext _ => byType
  | _ => byType

/-- Whether the value of constant `d` (straight-line code) cannot hold a
task. -/
partial def constNoTask (d : Decl .pure) (depth : Nat) : M Bool := do
  if let some b := (← get).constTask[d.name]? then return b
  if (← get).constBusy.contains d.name then return false
  let .code body := d.value | return false
  let some r := returnedVar body | return false
  modify fun s => { s with constBusy := s.constBusy.insert d.name }
  let b ← noTaskValue (collectBinders body {}) r (depth - 1)
  modify fun s => { s with constBusy := s.constBusy.erase d.name, constTask := s.constTask.insert d.name b }
  return b
end

/-- Whether field `j` of constructor `c` counts as read. -/
def fieldRead (c : ConstructorVal) (j : Nat) : M Bool := do
  let f := (← get).facts
  return f.allRead.contains c.induct || f.read.contains (c.name, j)

/-- Whether the argument `a` that constructor `c` stores in field `j` may be
replaced by `◾` when the field is not read. -/
def replaceable (c : ConstructorVal) (_j : Nat) (a : Arg .pure) : M Bool := do
  let .fvar x := a | return false
  if alwaysRead.contains c.induct then return false
  let loc := (← get).loc
  unless ← mayHoldCode (loc.types.getD x anyExpr) do return false
  if ← isR a then return false
  if (← read).tasks then noTaskValue loc x 8 else return true

def markRead (ctor : Name) (j : Nat) : M Unit := do
  unless (← get).facts.read.contains (ctor, j) do
    let cur := (← get).cur
    modify fun s => { s with facts := { s.facts with read := s.facts.read.insert (ctor, j),
                                                     readBy := s.facts.readBy.insert (ctor, j) cur,
                                                     changed := true } }

/-- Every field of inductive `ind`, and of the inductives its fields'
types mention, counts as read. -/
partial def markAllRead (ind : Name) : M Unit := do
  if (← get).facts.allRead.contains ind then return
  modify fun s => { s with facts := { s.facts with allRead := s.facts.allRead.insert ind, changed := true } }
  -- An inductive with computed fields (`Lean.Expr`) is built and matched
  -- through its implementation `ind._impl`.
  if let some (.inductInfo _) := (← getEnv).find? (ind ++ `_impl) then markAllRead (ind ++ `_impl)
  let some (.inductInfo iv) := (← getEnv).find? ind | return
  for c in iv.ctors do
    if let some ci := (← getEnv).find? c then
      discard <| markTypeConsts ci.type {}
where
  /-- The inductives `e` mentions, through type-level definitions (`IO`,
  `EIO`, …), count as read. -/
  markTypeConsts (e : Expr) (seen : NameSet) : M NameSet := do
    let env ← getEnv
    let mut seen := seen
    for k in e.getUsedConstants do
      if seen.contains k then continue
      seen := seen.insert k
      match env.find? k with
      | some (.inductInfo iv) =>
        unless isPropInductive iv do markAllRead k
      | some (.defnInfo dv) =>
        -- A type former: its value is a type expression.
        if dv.type.getForallBody.isSort then
          seen ← markTypeConsts dv.value seen
      | _ => pure ()
    return seen

/-- Projection `proj[i]` of structure `s`: field `i` of its constructor is
read. -/
def markReadProj (s : Name) (i : Nat) : M Unit := do
  match (← getEnv).find? s with
  | some (.inductInfo iv) =>
    if let [c] := iv.ctors then markRead c i else markAllRead s
  | _ => markAllRead s

def markLive (c : Name) (why : Why) : M Unit := do
  unless (← get).facts.live.contains c do
    let cur := (← get).cur
    let explain := (← read).explain
    let f := (← get).facts
    let why := if explain then f.why.insert c (cur, why ()) else f.why
    modify fun s => { s with facts := { f with live := f.live.insert c, why, changed := true } }

/-- A root found during the fixpoint: kept, every parameter useful. -/
def markRoot (r : Name) (why : Why) : M Unit := do
  let some d := (← read).byName[r]? | return
  markLive r why
  let ps := (← get).facts.params.getD r #[]
  unless ps.size == d.params.size && ps.all id do
    modify fun s => { s with facts := { s.facts with params := s.facts.params.insert r (d.params.map fun _ => true),
                                                     changed := true } }

def markExtern (c : Name) (why : Why) : M Unit := do
  unless (← get).facts.externs.contains c do
    let cur := (← get).cur
    let explain := (← read).explain
    let f := (← get).facts
    let why := if explain then f.why.insertIfNew c (cur, why ()) else f.why
    modify fun s => { s with facts := { f with externs := f.externs.insert c, why, changed := true } }
    -- A read of a `Lean` package's `initialize` constant: its initializer
    -- runs at startup.
    if let some i := (← read).usedInits.find? c then markRoot i fun _ => s!"initializer of {c}, read"

/-- The reads an extern call makes, by the extern's declared parameter
types. A parameter declared at a type variable is parametric: the runtime
stores such a value and gives it back, and cannot look inside it. Address
and sharing tests (`ptrAddrUnsafe`, `isExclusiveUnsafe`, `dbgTraceIfShared`,
`ShareCommon`) look at the object, not at its fields: an unread field
replaced keeps the object and its address, and lean2rr's sharing is not
native's anyway (`isExclusiveUnsafe` is `false`, `shareCommon` the
identity: docs/implementation/representations/identity.md). -/
def externReads (orig : Name) : M Unit := do
  if (← get).facts.declaredDone.contains orig then return
  modify fun s => { s with facts := { s.facts with declaredDone := s.facts.declaredDone.insert orig } }
  let some ci := (← getEnv).find? orig | return
  -- Every parameter, also those this mention does not pass: an extern can
  -- be a function value or partially applied, and gets the rest later.
  let mut ty := ci.type
  repeat
    let .forallE _ d b _ := ty.consumeMData | break
    ty := b
    -- A parameter declared at a type variable is parametric: nothing to mark.
    unless d.consumeMData.isBVar do
      discard <| markAllRead.markTypeConsts d {}


/-! ## Resources

In a program whose kept code makes resources (files, child processes:
`programMakesResources`), a value that may hold one stays where it is:
replaced, it would be released earlier than natively, and a file handle
is flushed and closed at its release. A forward, flow-insensitive
over-approximation over the kept code finds the variables that may hold
one: the results of the externs that make them (`resourceExterns`), and
whatever is computed from such a value, stored in a field, passed to a
parameter, returned, passed to a join point, or given to an extern or a
function value (then every extern's and function value's result, and the
parameters of every declaration used as a function value, may hold one).
Only values whose type may hold one count (`mayHoldRes`). -/

/-- Whether a value of mono type `t` may hold a resource, also through a
closure: a function type, `lcAny`, a type variable, a task, thunk,
reference or promise (`mayHoldCode`), a handle, or an inductive with such
a field (`holdsResource`). -/
def mayHoldRes (t : Expr) : M Bool := do
  let t := t.consumeMData.headBeta
  if t.isForall then return true
  if ← mayHoldCode t then return true
  Flatten.holdsResource t

def setREscape : M Unit := do
  unless (← get).facts.rEscape do
    modify fun s => { s with facts := { s.facts with rEscape := true, changed := true } }

def isRVar (x : FVarId) : M Bool := return (← get).loc.rvars.contains x

def isRArg : Arg .pure → M Bool
  | .fvar x => isRVar x
  | _ => pure false

def addR (x : FVarId) (t : Expr) : M Unit := do
  unless (← isRVar x) do
    if ← mayHoldRes t then
      modify fun s => { s with loc := { s.loc with rvars := s.loc.rvars.insert x } }

def markRField (c : Name) (j : Nat) : M Unit := do
  unless (← get).facts.rFields.contains (c, j) do
    modify fun s => { s with facts := { s.facts with rFields := s.facts.rFields.insert (c, j), changed := true } }

def markRParam (f : Name) (arity i : Nat) : M Unit := do
  let ps := (← get).facts.rParams.getD f (Array.replicate arity false)
  unless ps[i]?.getD true do
    modify fun s => { s with facts := { s.facts with rParams := s.facts.rParams.insert f (ps.set! i true), changed := true } }

def markRRet (f : Name) : M Unit := do
  let fa := (← get).facts
  unless fa.rRet.contains f do
    let fnRet := fa.rFnRet || fa.fnValues.contains f
    modify fun s => { s with facts := { s.facts with rRet := s.facts.rRet.insert f, rFnRet := fnRet, changed := true } }

def markFnValue (f : Name) : M Unit := do
  let fa := (← get).facts
  unless fa.fnValues.contains f do
    let fnRet := fa.rFnRet || fa.rRet.contains f
    modify fun s => { s with facts := { s.facts with fnValues := s.facts.fnValues.insert f, rFnRet := fnRet, changed := true } }

/-- Whether parameter `i` of extern `orig` is declared at a type whose
values the runtime only uses, without keeping them: a handle or a child
process. -/
def usesOnly (orig : Name) (i : Nat) : M Bool := do
  let some ci := (← getEnv).find? orig | return false
  let mut ty := ci.type
  for _ in [:i] do
    let .forallE _ _ b _ := ty.consumeMData | return false
    ty := b
  let .forallE _ d _ _ := ty.consumeMData | return false
  return d.consumeMData.getAppFn.constName?.any fun n => n == ``IO.FS.Handle || n == ``IO.Process.Child

/-- Whether the value of `let` value `v` may hold a resource; records the
flows it makes (fields, parameters, escapes). -/
def taintValue (v : LetValue .pure) : M Bool := do
  match v with
  | .lit _ | .erased => return false
  | .proj s i y _ =>
    let some (.inductInfo iv) := (← getEnv).find? s | return true
    let some c := iv.ctors.head? | return true
    return (← isRVar y) || (← get).facts.rFields.contains (c, i)
  | .fvar f args =>
    let anyR ← args.anyM isRArg
    if anyR then setREscape
    if args.isEmpty then return ← isRVar f
    let fa := (← get).facts
    return anyR || (← isRVar f) || fa.rEscape || fa.rFnRet
  | .const c _ args _ =>
    match ← classify c with
    | .ctor cv =>
      let mut anyR := false
      for h : i in [:args.size] do
        if i ≥ cv.numParams && (← isRArg args[i]) then
          markRField c (i - cv.numParams)
          anyR := true
      return anyR
    | .code d =>
      let n := d.params.size
      for h : i in [:args.size] do
        if i < n && (← isRArg args[i]) then markRParam c n i
      if args.size < n then
        -- A closure: it holds its arguments; whoever applies it gets `c`'s result.
        markFnValue c
        return ← args.anyM isRArg
      else
        let extra := args.extract n args.size
        let extraR ← extra.anyM isRArg
        if extraR then setREscape
        let fa := (← get).facts
        return fa.rRet.contains c || (args.size > n && (extraR || fa.rEscape || fa.rFnRet))
    | .ext orig =>
      let env ← getEnv
      let seed := (getExternNameFor env `c orig).any resourceExterns.contains
      let mut anyR := false
      for h : i in [:args.size] do
        if ← isRArg args[i] then
          anyR := true
          unless ← usesOnly orig i do setREscape
      let fa := (← get).facts
      -- The read of an `initialize` constant: its initializer's result
      -- (applied, also what that function value may return).
      if let some i := (← read).inits.find? c then
        if args.isEmpty then return fa.rRet.contains i || fa.rEscape
        return fa.rRet.contains i || anyR || fa.rEscape || fa.rFnRet
      -- An extern may also give back what a function value it calls returns
      -- (`IO.asTask`, `Thunk.get`).
      return seed || anyR || fa.rEscape || fa.rFnRet

/-- The forward pass over a body: the variables that may hold a resource,
and the flows the body makes. -/
partial def taint : Code .pure → M Unit
  | .let d k => do
    if ← taintValue d.value then addR d.fvarId d.type
    taint k
  | .jp fd k => do
    -- The jumps first (in the continuation), then the body.
    taint k
    let ps := (← get).loc.rjps.getD fd.fvarId #[]
    for h : i in [:fd.params.size] do
      if ps[i]?.getD false then addR fd.params[i].fvarId fd.params[i].type
    taint fd.value
  | .fun fd k _ => do
    -- A local function (lambda lifting leaves none in mono code): everything
    -- may hold one.
    setREscape
    for p in fd.params do addR p.fvarId p.type
    addR fd.fvarId fd.type
    taint fd.value
    taint k
  | .jmp j args => do
    for h : i in [:args.size] do
      if ← isRArg args[i] then
        let ps := (← get).loc.rjps.getD j (Array.replicate args.size false)
        modify fun s => { s with loc := { s.loc with rjps := s.loc.rjps.insert j (ps.set! i true) } }
  | .cases cs => do
    let rd ← isRVar cs.discr
    for alt in cs.alts do
      if let .alt ctor ps _ _ := alt then
        for h : i in [:ps.size] do
          if rd || (← get).facts.rFields.contains (ctor, i) then addR ps[i].fvarId ps[i].type
      taint alt.getCode
  | .return x => do
    if ← isRVar x then markRRet (← get).cur
  | _ => pure ()

/-- The resources pass over declaration `d` (its binders are in `loc`). -/
def taintDecl (d : Decl .pure) (body : Code .pure) : M Unit := do
  let fa := (← get).facts
  let ps := fa.rParams.getD d.name #[]
  let escaped := fa.rEscape && fa.fnValues.contains d.name
  for h : i in [:d.params.size] do
    if escaped || ps[i]?.getD false then addR d.params[i].fvarId d.params[i].type
  taint body

/-- Analysis of a `let` value that stays (`reason`: why it stays). -/
def useValue (v : LetValue .pure) (reason : Why) : M Unit := do
  match v with
  | .lit _ | .erased => pure ()
  | .proj s i y _ =>
    useVar y fun _ => "projected"
    markReadProj s i
  | .fvar f args =>
    useVar f fun _ => "applied"
    for a in args do useArg a fun _ => "argument of a function value"
  | .const c _ args _ =>
    match ← classify c with
    | .ctor cv =>
      for h : i in [:args.size] do
        if i < cv.numParams then useArg args[i] fun _ => s!"parameter of {c}"
        else
          let j := i - cv.numParams
          if ← fieldRead cv j then
            let by_ := (← get).facts.readBy[(c, j)]?
            useArg args[i] fun _ => s!"field {j} of {c}{(by_.map (s!", read by {·}")).getD ""}"
          else if !(← replaceable cv j args[i]) then
            useArg args[i] fun _ => s!"field {j} of {c} (data, or may hold a task)"
    | .code d =>
      markLive c fun _ => s!"{if args.size < d.params.size then "partial application" else "call"}, {reason ()}"
      let ps := (← get).facts.params.getD c #[]
      for h : i in [:args.size] do
        if i ≥ d.params.size || ps[i]?.getD false || (← isR args[i]) then
          useArg args[i] fun _ => s!"parameter {i} of {c}"
    | .ext orig =>
      markExtern c reason
      for a in args do useArg a fun _ => s!"argument of extern {orig}"
      externReads orig

/-- The backward pass over a body. -/
partial def go : Code .pure → M Unit
  | .let d k => do
    go k
    if ← isUseful d.fvarId then
      let w := (← get).loc.why.getD d.fvarId "useful"
      useValue d.value fun _ => s!"value {w}"
    else if ← effectful d.value then
      useValue d.value fun _ => "may have an effect"
  | .jp fd k => do
    go fd.value
    let ps ← fd.params.mapM (isUseful ·.fvarId)
    modify fun s => { s with loc := { s.loc with jps := s.loc.jps.insert fd.fvarId ps } }
    go k
  | .fun fd k _ => do
    -- A local function (lambda lifting leaves none in mono code): all of
    -- its body counts.
    go fd.value
    for p in fd.params do useVar p.fvarId fun _ => "parameter of a local function"
    useVar fd.fvarId fun _ => "local function"
    go k
  | .jmp j args => do
    let ps := (← get).loc.jps.getD j #[]
    for h : i in [:args.size] do
      if ps[i]?.getD true || (← isR args[i]) then useArg args[i] fun _ => "passed to a join point"
  | .cases cs => do
    useVar cs.discr fun _ => "matched"
    for alt in cs.alts do
      go alt.getCode
      if let .alt ctor ps _ _ := alt then
        for h : i in [:ps.size] do
          if ← isUseful ps[i].fvarId then markRead ctor i
  | .return x => useVar x fun _ => "returned"
  | _ => pure ()

/-- Analyze declaration `d` with the facts so far: its useful variables,
then the facts it adds (its useful parameters among them). -/
def analyzeDecl (d : Decl .pure) : M Local := do
  let .code body := d.value | return {}
  let seed : Local := { types := d.params.foldl (fun m p => m.insert p.fvarId p.type) {} }
  modify fun s => { s with cur := d.name, loc := collectBinders body seed }
  if (← read).resources then taintDecl d body
  go body
  let loc := (← get).loc
  let old := (← get).facts.params.getD d.name (d.params.map fun _ => false)
  let isRoot := (← read).roots.contains d.name
  let new := (d.params.zip old).map fun (p, o) => o || isRoot || loc.useful.contains p.fvarId
  if new != old then
    modify fun s => { s with facts := { s.facts with params := s.facts.params.insert d.name new, changed := true } }
  return loc

/-- The body rewritten with the facts (`loc`: its analysis). -/
partial def rewrite (loc : Local) : Code .pure → M (Code .pure)
  | .let d k => do
    let k ← rewrite loc k
    if !loc.useful.contains d.fvarId && !(← effectful d.value) then return k
    return .let { d with value := ← rewriteValue d.value } k
  | .jp fd k => do
    return .jp (FunDecl.mk fd.fvarId fd.binderName fd.params fd.type (← rewrite loc fd.value)) (← rewrite loc k)
  | .fun fd k _ => do
    return .fun (FunDecl.mk fd.fvarId fd.binderName fd.params fd.type (← rewrite loc fd.value)) (← rewrite loc k)
  | .jmp j args => do
    let ps := loc.jps.getD j #[]
    let keep (i : Nat) (a : Arg .pure) : Bool :=
      ps[i]?.getD true || (match a with | .fvar x => loc.rvars.contains x | _ => false)
    return .jmp j (args.mapIdx fun i a => if keep i a then a else erase a)
  | .cases cs => do
    let alts ← cs.alts.mapM fun
      | .alt ctor ps code _ => return .alt ctor ps (← rewrite loc code)
      | .default code => return .default (← rewrite loc code)
      | other => pure other
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c
where
  erase (a : Arg .pure) : Arg .pure := if a matches .fvar _ then .erased else a
  rewriteValue (v : LetValue .pure) : M (LetValue .pure) := do
    match v with
    | .const c us args _ =>
      match ← classify c with
      | .ctor cv =>
        let mut out := args
        for h : i in [:args.size] do
          if i < cv.numParams then continue
          let j := i - cv.numParams
          if !(← fieldRead cv j) && (← replaceable cv j args[i]) then out := out.set! i .erased
        return .const c us out
      | .code d =>
        let ps := (← get).facts.params.getD c #[]
        let mut out := args
        for h : i in [:args.size] do
          if i < d.params.size && !(ps[i]?.getD false) && !(← isR args[i]) then out := out.set! i (erase args[i])
        return .const c us out
      | .ext _ => return v
    | v => return v

/-- The fixpoint over `decls` from `roots`. -/
def fixpoint (decls : Array (Decl .pure)) : M Unit := do
  let roots := (← read).roots
  for r in roots do
    if let some d := (← read).byName[r]? then
      let f := (← get).facts
      let f := { f with live := f.live.insert r, params := f.params.insert r (d.params.map fun _ => true) }
      modify fun s => { s with facts := f }
  for ind in alwaysRead do markAllRead ind
  repeat
    modify fun s => { s with facts := { s.facts with changed := false }, rounds := s.rounds + 1 }
    for d in decls do
      if (← get).facts.live.contains d.name then discard <| analyzeDecl d
    unless (← get).facts.changed do break

/-- The kept declarations, rewritten. -/
def rewriteAll (decls : Array (Decl .pure)) : M (Array (Decl .pure) × Nat) := do
  let f := (← get).facts
  let mut out := #[]
  let mut dropped := 0
  for d in decls do
    match d.value with
    | .code _ =>
      if f.live.contains d.name then
        let loc ← analyzeDecl d
        let .code body := d.value | unreachable!
        out := out.push { d with value := .code (← rewrite loc body) }
      else dropped := dropped + 1
    | .extern _ =>
      if f.externs.contains d.name then out := out.push d else dropped := dropped + 1
  return (out, dropped)

/-- The chain of reasons that keeps `n`, from a root. -/
partial def chain (why : Std.HashMap Name (Name × String)) (n : Name) (fuel : Nat := 60) : List String :=
  match fuel, why[n]? with
  | 0, _ => ["…"]
  | _, none => []
  | fuel + 1, some (p, r) => s!"{n}  ({r} in {p})" :: if p == n then [] else chain why p fuel

/-- The pass (`PassConfig.prunePasses`): Stage 2's declarations `decls`,
the instance keys, the declarations the entry point always needs (`roots`)
and the `Lean` package's `initialize` constants the program uses, with
their initializers (`usedInits`). -/
def run (keys : NameMap InstKey) (roots : Array Name) (inits : Array (Name × Name × Bool))
    (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let env ← getEnv
  let debug := (← IO.getEnv "L2R_DEBUG").isSome
  let explain := (← IO.getEnv "L2R_UNREAD_FIELDS_WHY").isSome
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : Std.HashMap Name (Decl .pure))
  -- The `IO.Error` builders, which the lowering calls for fallible IO
  -- primitives (`LowerCtx.ioErrorBuilders`), are roots too.
  let byDecl : NameMap Name := keys.foldl (init := {}) fun m inst k =>
    if k.typeArgs.isEmpty && k.dicts.isEmpty then m.insert k.decl inst else m
  let exports ← (exportMap.run' {config := {}} : CoreM _)
  let builders := ioErrorBuilderSyms.filterMap fun sym => (exports.get? sym).bind byDecl.find?
  let roots := (roots ++ builders).foldl (fun s r => s.insert r) ({} : NameSet)
  let usedInits := inits.foldl (fun m (d, i, c) => if c then m.insert d i else m) {}
  let initMap := inits.foldl (fun m (d, i, _) => m.insert d i) {}
  let attempt (tasks resources : Bool) : CoreM (Array (Decl .pure) × Nat × St) := do
    let act : M (Array (Decl .pure) × Nat) := do
      fixpoint decls
      rewriteAll decls
    let ((out, dropped), st) ←
      (act.run { byName, keys, roots, usedInits, inits := initMap, tasks, resources, explain }).run {}
    return (out, dropped, st)
  -- First assuming that the kept code creates no task and no resource; if
  -- it does, again with what may hold one kept, until the kept code (which
  -- only grows) shows no new kind (at most three attempts).
  let mut (out, dropped, st) ← attempt false false
  let mut tasks := false
  let mut resources := false
  repeat
    let t := tasks || programCreatesTasks env keys out
    let r := resources || (← programMakesResources (out.foldl (fun m d => m.insert d.name d) {}) keys)
    if t == tasks && r == resources then break
    tasks := t
    resources := r
    (out, dropped, st) ← attempt tasks resources
  if let some n := programCasts env keys out then
    if debug then IO.eprintln s!"lean2rr: unread-fields: off, the program can cast ({n})"
    return decls
  if debug then
    IO.eprintln s!"lean2rr: unread-fields: {out.size} of {decls.size} declarations kept, {dropped} dropped; \
      {st.facts.read.size} fields read, {st.facts.allRead.size} types read whole, {st.rounds} rounds\
      {if tasks then ", tasks: closures checked" else ""}\
      {if resources then s!", resources: kept where they may be held ({if st.facts.rEscape then "escaped" else "followed"})" else ""}"
  if explain then
    for n in st.facts.externs do
      let isLean := (env.getModuleIdxFor? n).any fun i => (env.header.moduleNames[i.toNat]!).getRoot == `Lean
      if isLean && (getExternNameFor env `c ((keys.find? n).map (·.decl) |>.getD n)).isSome then
        IO.eprintln s!"lean2rr: unread-fields: {n} is kept by:\n  {"\n  ".intercalate (chain st.facts.why n)}"
  return out

/-- Registry entry point. -/
def install (c : PassConfig) : PassConfig :=
  { c with prunePasses := c.prunePasses.push run }

end LeanToReussir.Opt.UnreadFields
