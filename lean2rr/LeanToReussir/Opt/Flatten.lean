import Lean
import LeanToReussir.PassConfig

/-!
# Structure arguments and results spread into their fields (optimization `flatten-structs`)

Rule 1 gives every datatype one layout, with the fields of a type
parameter's type boxed (`LAny`). A loop's state of several variables
(`MProd Nat (MProd Nat Nat)`, `Nat × Nat`) and a monad's result
(`EST.Out ε σ (Except ε' α × σ')`) are such values: each iteration or call
allocates the records, boxes every field into them and unboxes them again
at the next step. This pass, a worker/wrapper transformation on the mono
code after Stage 3 (where binder types are precise), passes those values as
their fields instead, each at its precise type. No data layout changes.

**Shapes.** A `Shape` says how a value is spread over variables: a leaf is
one variable; a node is a value of an inductive with one constructor (a
structure) or two (`Except`, `EST.Out`, `Option`, `ForInStep`: results and
join points only), whose fields are spread in turn, nested at most
`maxDepth` levels and `maxLeaves` variables deep. A two-constructor node has
one more variable, its tag (a `Bool`: `true` for the second constructor),
and the fields of both constructors; those of the constructor the value
does not have are placeholders (`◾`, Lean's `box(0)` at their types: only
types with a finite placeholder qualify, `placeholderOk`). Two constructors
with the same field types share their fields (`Ctors.shared`). Only types
the lowering treats as ordinary inductives qualify (`indInfo?`).

**Known fields** (`Root`). A value's fields are known where it is a
constructor application of the same declaration, a split parameter or a
field of one, a value matched by an enclosing `cases` (an alias: its
fields are the alternative's parameters), a constant that only builds one
constructor (`constCtor?`: `pure 0` extracted as a closed term), or the
result of a call of a declaration that returns a tuple. A constructor
application used only where its fields suffice is not built.

**Arguments.** A parameter of a join point, or of a declaration that calls
itself (and is in no larger call cycle), whose type is a structure becomes
one parameter per relevant field; a parameter of another declaration only
where some caller passes it known fields (`prunePassed`), and never one
used whole there (nothing amortizes a rebuild). This requires every jump to the join
point, every saturated self-call, to pass a value whose fields are known,
and every other use of the parameter to be a projection, a `cases`, or such
an argument. Any other use ("whole": the value stored, passed to another
function, returned unsplit) keeps that level of the parameter whole, with
one exception (`allowedWhole`): a loop's parameter at the loop's exit,
when every step built a new value, is rebuilt from the fields there, where
no object the program shares reaches that level (`AState.existing`: a
matched value, a constant, a value the caller passed in). A value whose
object the program inspects (`ptrAddrUnsafe`, `dbgTraceIfShared`,
`isExclusiveUnsafe`) is never rebuilt. A value is built at most once per
run of the code that binds it: the rewrite remembers what it built along
the scope (`Env.mats`), and two rebuilds that do not share a scope (one in
a join point's body) keep that level whole (`constrainDecl`).

**Results.** A declaration whose result type is such a node with at least
two variables, none of them of a type with a function type in it, returns
the variables as a `[value]` tuple (`L2RFlat.Tuple<k>`, lowered by
`tupleType`) when every `return` returns a value whose fields are known.
Every saturated call reads the variables from the tuple: a caller that
matches the result follows the tag, one that uses it whole rebuilds it. A
level of the result stays whole when some declaration uses it whole while
no other declaration reads it field by field, or while the declaration may
return an existing object there (`pruneUnread`); the wrapper counts as a
use of every level (`wrapperUsers`).

**Wrapper.** A declaration with split parameters or a tuple result becomes
a worker (`f._l2r_flat`) with the new signature and the original body, and
a wrapper of the original name and signature that projects the fields,
calls the worker and rebuilds the result: function values (partial
applications) and the entry points use it. Every saturated call in the
program calls the worker, with the fields of the arguments (projected,
or read by a `cases`, when they are not known); a loop whose split
parameter is rebuilt at its exit keeps its first step in the wrapper and
is called through it (`AState.peel`).

**Resources.** In a program that creates files or processes, the pass
leaves alone every declaration with a parameter or result that may hold
one (`resourceExcluded`): lean2rr emulates native release times by Lean's
borrow inference on that code.

Only pure steps move: a constructor application not built, a projection
read from a known field, a value rebuilt, a match on a tag instead of on a
value. No call, effect or panic moves, and nothing runs more often. The
identity of a rebuilt value is not preserved (translation plan §9).
`L2R_FLATTEN_DEBUG=NAME` prints the decisions about the declarations whose
names contain NAME, `L2R_FLATTEN_TIME` the time of each phase.
-/

namespace LeanToReussir.Opt.Flatten
open Lean Compiler LCNF

/-- How deep nested values are split. -/
def maxDepth : Nat := 8
/-- At most this many variables from one value. -/
def maxLeaves : Nat := 16
/-- The largest declaration (`Code.size`) whose split parameter may be
rebuilt at its loop's exit: such a declaration's wrapper keeps a copy of
its body (see `allowedWhole`). -/
def maxPeelSize : Nat := 300

/-! ## Shapes -/

/-- A constructor of a node: its name, parameters and fields. -/
structure CInfo where
  name : Name
  numParams : Nat
  numFields : Nat
  deriving Inhabited, BEq

/-- Where constructor `c`'s fields start among a node's children. -/
def childOffset (ctors : Array CInfo) (c : Nat) : Nat :=
  (ctors.extract 0 c).foldl (· + ·.numFields) 0

/-- The constructor whose field child `j` is. -/
def ctorOfChild (ctors : Array CInfo) (j : Nat) : Nat := Id.run do
  let mut off := 0
  for h : c in [:ctors.size] do
    if j < off + ctors[c].numFields then return c
    off := off + ctors[c].numFields
  return ctors.size

/-- The constructors of a node; `shared`: two constructors with the same
field types (`ForInStep`: `done b | yield b`) share one set of children,
the fields of whichever constructor the value has. -/
structure Ctors where
  cs : Array CInfo
  shared : Bool := false
  deriving Inhabited, BEq

namespace Ctors

def size (k : Ctors) : Nat := k.cs.size

/-- Where constructor `c`'s children start. -/
def base (k : Ctors) (c : Nat) : Nat := if k.shared then 0 else childOffset k.cs c

/-- The constructor child `j` belongs to (`none`: every constructor's). -/
def owner? (k : Ctors) (j : Nat) : Option Nat := if k.shared then none else some (ctorOfChild k.cs j)

/-- Constructor `c`'s children among `fields`. -/
def kids (k : Ctors) (c : Nat) (fields : Array α) : Array α :=
  if k.shared then fields
  else
    let off := childOffset k.cs c
    fields.extract off (off + (k.cs[c]?.map (·.numFields)).getD 0)

end Ctors

/-- How a value is spread over variables: a leaf is one variable of type
`ty`; `irr` a field without data (a proof, a type, the world token) or,
in the shape of a value, a field of the constructor the value does not
have; a node a value of `induct` (one or two constructors) whose fields,
those of every constructor in order, are spread in turn (a node of two
constructors also has a tag variable). -/
inductive Shape where
  | leaf (ty : Expr)
  | irr (ty : Expr)
  | node (ty : Expr) (induct : Name) (ctors : Ctors) (fields : Array Shape)
  deriving Inhabited, BEq

namespace Shape

def ty : Shape → Expr
  | leaf t | irr t | node t .. => t

def isNode : Shape → Bool
  | node .. => true
  | _ => false

def boolTy : Expr := mkConst ``Bool

partial def leafTypes : Shape → Array Expr
  | leaf t => #[t]
  | irr _ => #[]
  | node _ _ cs fs => fs.foldl (· ++ ·.leafTypes) (if cs.size > 1 then #[boolTy] else #[])

/-- The sub-shape at `path`, if `path` goes through nodes. -/
def at? : Shape → List Nat → Option Shape
  | s, [] => some s
  | node _ _ _ fs, i :: p => fs[i]?.bind (·.at? p)
  | _, _ :: _ => none

/-- Whether the sub-shape at `path` is a node. -/
def nodeAt (s : Shape) (path : List Nat) : Bool :=
  (s.at? path).any (·.isNode)

/-- `s` with the node at `path` made a leaf. -/
partial def cutAt : Shape → List Nat → Shape
  | node t .., [] => leaf t
  | s, [] => s
  | node t ind cs fs, i :: p => node t ind cs (fs.modify i (·.cutAt p))
  | s, _ :: _ => s

end Shape

/-- A field without data: no variable. -/
def irrelevantTy (t : Expr) : Bool :=
  let t := t.consumeMData
  erasedDom t || t.isErased || t == mkConst ``lcVoid

/-- Whether type `t` mentions a function type (results only: such a field
would take Stage 4's analysis of erased domains through the tuple, which
it reads as boxed). -/
def mentionsFn (t : Expr) : Bool :=
  (t.find? (·.isForall)).isSome

/-- Memo tables of the type questions (`indInfo?`, `placeholderOk`), keyed
by mono type. The environment only grows by the pass's tuples meanwhile. -/
initialize indInfoCache : IO.Ref (Std.HashMap Expr (Option (InductiveVal × Ctors × Array (Array Expr)))) ← IO.mkRef {}
initialize placeholderCache : IO.Ref (Std.HashMap Expr Bool) ← IO.mkRef {}
initialize resourceCache : IO.Ref (Std.HashMap Expr Bool) ← IO.mkRef {}

/-- Whether a value of mono type `e` may hold a resource whose release is
observable: Lower/Borrow's `mayHoldResource` (the same rules: a handle,
`lcAny`, or an inductive or array with such a field or element at its type
arguments; types being examined count as not holding one), memoized here
(a `true` wherever it was found, a `false` at the top only), as the pass
asks it of every declaration's types. -/
partial def holdsResource (e : Expr) (seen : Array Expr := #[]) : CoreM Bool := do
  let e := e.consumeMData.headBeta
  if let some r := (← resourceCache.get)[e]? then
    if r || seen.isEmpty then return r
  let r ← go e seen
  if r || seen.isEmpty then resourceCache.modify (·.insert e r)
  return r
where
  go (e : Expr) (seen : Array Expr) : CoreM Bool := do
    if seen.contains e then return false
    let seen := seen.push e
    if e.isForall || e.isSort then return false
    let .const n _ := e.getAppFn | return true
    if n == ``lcAny || n == ``IO.FS.Handle then return true
    let args := e.getAppArgs
    if n == ``Array then
      return ← match args[0]? with
        | some a => holdsResource a seen
        | none => pure true
    if n == ``lcErased || n == ``lcVoid || builtinTypeNames.contains n then return false
    let env ← getEnv
    let some ival := (match env.find? (n ++ `_impl), env.find? n with
        | some (.inductInfo iv), _ => some iv
        | _, some (.inductInfo iv) => some iv
        | _, _ => none) | return true
    if ival.type.getForallBody.isProp then return false
    let params := (List.range ival.numParams).toArray.map fun i => (args[i]?.getD anyExpr).consumeMData
    for c in ival.ctors do
      let mut ty ← instantiateForall (← getOtherDeclBaseType c []) params
      repeat
        match ty.headBeta with
        | .forallE _ d b _ =>
          let m ← toMonoTypeKeep d
          if !(m.isErased || m == mkConst ``lcVoid) then
            if ← holdsResource m seen then return true
          ty := b.instantiate1 anyExpr
        | _ => break
    return false

/-- The inductive `ty` is, when the pass may spread it: one or two
constructors, not recursive (nor nested or mutual), no indices, not a
proposition, applied to its parameters, not a type the lowering builds in,
a computed-field type or `IO.Process.Child` (hidden fields), no constructor
an extern. Returns the inductive, its constructors and their field types at
`ty`'s arguments (mono types). -/
def indInfo? (ty : Expr) : CoreM (Option (InductiveVal × Ctors × Array (Array Expr))) := do
  let ty := ty.consumeMData.headBeta
  if let some r := (← indInfoCache.get)[ty]? then return r
  let r ← go ty
  indInfoCache.modify (·.insert ty r)
  return r
where
  go (ty : Expr) : CoreM (Option (InductiveVal × Ctors × Array (Array Expr))) := do
    let .const n _ := ty.getAppFn | return none
    if builtinTypeNames.contains n || (flatTupleArity? n).isSome || n == ``IO.Process.Child then return none
    let env ← getEnv
    if env.contains (n ++ `_impl) then return none
    let some (.inductInfo iv) := env.find? n | return none
    if iv.isRec || iv.numIndices != 0 || iv.all.length != 1 || iv.numNested != 0 || iv.isUnsafe then return none
    if iv.type.getForallBody.isProp then return none
    unless iv.ctors.length == 1 || iv.ctors.length == 2 do return none
    if ty.getAppNumArgs != iv.numParams then return none
    let mut cs := #[]
    let mut fts := #[]
    for c in iv.ctors do
      let some (.ctorInfo cv) := env.find? c | return none
      if isExtern env c then return none
      let ft ← ctorFieldTypes c ty
      if ft.size != cv.numFields then return none
      cs := cs.push { name := c, numParams := cv.numParams, numFields := cv.numFields }
      fts := fts.push ft
    let shared := cs.size == 2 && fts[0]! == fts[1]!
    return some (iv, { cs, shared }, fts)

/-- Whether a placeholder (`◾` at type `ty`, `zeroValue` in the lowering) is
certainly finite: scalars, numbers, strings, arrays, boxes, and an
inductive with a constructor whose fields at the uniform layout (every
parameter `lcAny`) all qualify. Conservative: `false` where unsure. -/
partial def placeholderOk (ty : Expr) (seen : List Name := []) : CoreM Bool := do
  let ty := ty.consumeMData.headBeta
  -- A `true` holds wherever it was found; a `false` only at the top (below,
  -- a type on the path counts as having none).
  if let some r := (← placeholderCache.get)[ty]? then
    if r || seen.isEmpty then return r
  let r ← go ty seen
  if r || seen.isEmpty then placeholderCache.modify (·.insert ty r)
  return r
where
  go (ty : Expr) (seen : List Name) : CoreM Bool := do
    if ty.isForall then return false
    let .const n _ := ty.getAppFn | return false
    if [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Float, ``Float32, ``Bool, ``Nat, ``Int,
        ``String, ``Unit, ``PUnit, ``lcAny, ``lcErased, ``lcVoid, ``Array, ``ByteArray,
        ``FloatArray].contains n then return true
    if builtinTypeNames.contains n || seen.contains n then return false
    let some (.inductInfo iv) := (← getEnv).find? n | return false
    if iv.type.getForallBody.isProp then return true
    for c in iv.ctors do
      let some (.ctorInfo cv) := (← getEnv).find? c | return false
      let fts ← ctorFieldTypes c (mkAppN (mkConst n) (Array.replicate iv.numParams anyExpr))
      if fts.size != cv.numFields then continue
      let mut ok := true
      for ft in fts do
        unless irrelevantTy ft || (← placeholderOk ft (n :: seen)) do
          ok := false
          break
      if ok then return true
    return false

/-- The largest shape of a value of type `ty`, within `depth` levels and a
budget of leaves (the state: leaves still allowed besides this one). Two
constructors only with `sums` (results) and when every variable of the
node has a finite placeholder. A value without relevant fields stays a
leaf. -/
partial def expandShape (sums : Bool) (ty : Expr) (depth : Nat) : StateT Nat CoreM Shape := do
  if depth == 0 then return .leaf ty
  let some (iv, cs, fts) ← indInfo? ty | return .leaf ty
  if cs.size > 1 && !sums then return .leaf ty
  let all := if cs.shared then fts[0]! else fts.foldl (· ++ ·) #[]
  let rel := (all.filter (!irrelevantTy ·)).size + (if cs.size > 1 then 1 else 0)
  if rel == 0 || (cs.size > 1 && rel == 1) then return .leaf ty
  let budget ← get
  if rel > budget + 1 then return .leaf ty
  set (budget + 1 - rel)
  let mut fs := #[]
  for ft in all do
    if irrelevantTy ft then fs := fs.push (.irr ft)
    else fs := fs.push (← expandShape sums ft (depth - 1))
  let s := Shape.node ty iv.name cs fs
  if cs.size > 1 then
    for t in s.leafTypes do
      unless ← placeholderOk t do return .leaf ty
  return s

def maxShape (ty : Expr) (sums : Bool := false) : CoreM Shape := do
  let (s, _) ← (expandShape sums ty maxDepth).run (maxLeaves - 1)
  return s

/-! ## The program's facts -/

/-- A parameter that may be split: of a declaration (by index), or of a
join point of a declaration. -/
inductive SlotId where
  | param (decl : Name) (i : Nat)
  | jp (decl : Name) (jp : FVarId) (i : Nat)
  deriving BEq, Hashable, Inhabited

/-- A place a value flows into: a parameter that may be split, or a
declaration's result. -/
inductive Tgt where
  | slot (s : SlotId)
  | res (f : Name)
  deriving BEq, Hashable, Inhabited

/-- Where the fields of a variable's value are known. -/
inductive Root where
  /-- The sub-value at `path` of a parameter that may be split. -/
  | slot (s : SlotId) (path : List Nat)
  /-- A value built by a constructor application in this declaration, or a
  value matched by an enclosing `cases` (`CtorLet.alias`). -/
  | ctor (x : FVarId)
  /-- The sub-value at `path` of the result of a call of `callee` (bound
  to `x`), whose result may be a tuple. -/
  | call (callee : Name) (x : FVarId) (path : List Nat)
  /-- A field without data, or of the constructor a value does not have. -/
  | irr
  /-- Anything else: a variable whose fields are not known. -/
  | opaque
  deriving Inhabited

/-- Where a use is: whether no self-call is reachable from it (the exit of
a loop). -/
abbrev Exit := Bool

/-- A use of a variable that the analysis constrains. -/
inductive Use where
  /-- `a` passed to the parameter `s` (a jump, a saturated self-call bound
  to `call`). -/
  | slot (a : FVarId) (s : SlotId) (exit : Exit) (call : Option FVarId)
  /-- Something without known fields passed to `s`. -/
  | slotOpaque (s : SlotId)
  /-- `a` returned. -/
  | ret (a : FVarId)
  /-- `a` passed as argument `i` of a saturated call of another declaration
  `f` (whose worker, if any, takes the fields), bound to `call`. -/
  | ext (a : FVarId) (f : Name) (i : Nat) (exit : Exit) (call : FVarId)
  /-- A `cases` on `v` or a projection of it, at inductive `typeName`. -/
  | inspect (v : FVarId) (typeName : Name) (exit : Exit)
  /-- Any other use of `a`: the whole value. -/
  | whole (a : FVarId) (exit : Exit)
  /-- `a`'s object inspected (`ptrAddrUnsafe`, `dbgTraceIfShared`,
  `isExclusiveUnsafe`): the value must be the one the program built, never
  a rebuilt copy. -/
  | pinned (a : FVarId)
  deriving Inhabited

/-- A constructor application of an inductive the pass may spread, bound in
the declaration, that the pass may leave unbuilt; or (`alias`) the value a
`cases` matches, inside the alternative of constructor `cidx` (its fields
are the alternative's parameters; nothing is built for it). -/
structure CtorLet where
  ctor : Name
  /-- The constructor's index among `ctors`. -/
  cidx : Nat
  ctors : Ctors
  args : Array (Arg .pure)
  ty : Expr
  /-- Whether no self-call is reachable from it. -/
  exit : Exit
  /-- Which of the constructor's fields have no data. -/
  irrFields : Array Bool
  /-- The matched variable, for a value matched by a `cases`. -/
  alias : Option FVarId := none
  /-- A constant whose value is this constructor (a closed term such as
  `Except.ok 0`): the variable holds it, its fields are read from it. -/
  const : Bool := false
  /-- How many join-point bodies enclose it. -/
  depth : Nat := 0
  deriving Inhabited

/-- What the analysis needs of a declaration's code, collected once. -/
structure DeclFacts where
  name : Name
  /-- Whether it calls itself (saturated). -/
  recursive : Bool := false
  /-- Whether every self-reference is a saturated call in tail position. -/
  tailOnly : Bool := true
  /-- A local function in the body (lambda lifting removes them): the pass
  leaves the declaration alone. -/
  hasFun : Bool := false
  /-- Join points and their parameters. -/
  jps : Std.HashMap FVarId (Array (Param .pure)) := {}
  /-- Variables bound as child `j` of `v` at inductive `typeName` (a `cases`
  parameter or a projection). -/
  fieldOf : Std.HashMap FVarId (FVarId × Nat × Name) := {}
  ctorLets : Std.HashMap FVarId CtorLet := {}
  /-- Variables bound to a saturated call of a declaration of the program
  with code: the callee. -/
  calls : Std.HashMap FVarId Name := {}
  /-- How many join-point bodies enclose each such call. -/
  callDepth : Std.HashMap FVarId Nat := {}
  /-- The types of all binders. -/
  types : Std.HashMap FVarId Expr := {}
  uses : Array Use := #[]
  /-- How many join-point bodies enclose each use (in `uses`' order). -/
  useDepth : Array Nat := #[]
  /-- The arguments passed to each split candidate (for `freshFed`), in
  order; `none` for an argument without known fields. -/
  flows : Std.HashMap SlotId (Array (Option FVarId)) := {}
  /-- The constructor lets in order of appearance. -/
  ctorOrder : Array FVarId := #[]
  /-- The parameter slot of each declaration and join-point parameter. -/
  slotOfVar : Std.HashMap FVarId SlotId := {}
  /-- The size of the body (`Code.size`). -/
  size : Nat := 0
  /-- Which join points' bodies may reach a self-call. -/
  jpRec : Std.HashMap FVarId Bool := {}
  deriving Inhabited

/-- What the program's declarations are, by name. -/
structure Program where
  decls : Std.HashMap Name (Decl .pure)
  facts : Std.HashMap Name DeclFacts


/-- The constructor a constant (a declaration without parameters) returns,
when its body only builds it: `let a := 0; let r := Except.ok a; return r`. -/
def constCtor? (prog : Std.HashMap Name (Decl .pure)) (g : Name) : Option Name :=
  match prog[g]? with
  | some d =>
    if !d.params.isEmpty then none else
    match d.value with
    | .code c => go c {}
    | _ => none
  | none => none
where
  go (c : Code .pure) (vals : Std.HashMap FVarId (LetValue .pure)) : Option Name :=
    match c with
    | .let l k => go k (vals.insert l.fvarId l.value)
    | .return r =>
      match vals[r]? with
      | some (.const ctor _ _ _) => some ctor
      | _ => none
    | _ => none

section Collect
variable (prog : Std.HashMap Name (Decl .pure)) (pinning : NameSet) (self : Name) (arity : Nat)

/-- Collect the facts of code `c`, and whether it may reach a self-call
(one pass, the continuation first, so that a `let` knows whether its rest
may: the exit of a loop); `refine` maps a variable a `cases` matches to its
alias inside the alternative being collected. -/
partial def collectCode (refine : Std.HashMap FVarId FVarId) (depth : Nat) (c : Code .pure) :
    StateT DeclFacts CoreM Bool := do
  let rv (x : FVarId) : FVarId := refine.getD x x
  let addUse (u : Use) : StateT DeclFacts CoreM Unit :=
    modify fun f => { f with uses := f.uses.push u, useDepth := f.useDepth.push depth }
  let setTy (x : FVarId) (t : Expr) : StateT DeclFacts CoreM Unit :=
    modify fun f => { f with types := f.types.insert x t }
  let addFlow (s : SlotId) (a : Option FVarId) : StateT DeclFacts CoreM Unit :=
    modify fun f => { f with flows := f.flows.insert s ((f.flows.getD s #[]).push a) }
  let wholeArgs (args : Array (Arg .pure)) (exit : Exit) : StateT DeclFacts CoreM Unit := do
    for a in args do
      if let .fvar x := a then addUse (.whole (rv x) exit)
  match c with
  | .let d k =>
    setTy d.fvarId d.type
    let kr ← collectCode refine depth k
    match d.value with
    | .proj sn i v =>
      modify fun f => { f with fieldOf := f.fieldOf.insert d.fvarId (v, i, sn) }
      addUse (.inspect (rv v) sn (!kr))
      return kr
    | .const g _ args _ =>
      let selfCall := g == self && args.size ≥ arity
      let exit := !selfCall && !kr
      if g == self then
        if args.size == arity then
          modify fun f => { f with recursive := true, calls := f.calls.insert d.fvarId g,
                                   callDepth := f.callDepth.insert d.fvarId depth }
          let tail := match k with | .return r => r == d.fvarId | _ => false
          unless tail do modify fun f => { f with tailOnly := false }
          for h : i in [:args.size] do
            let s := SlotId.param self i
            match args[i] with
            | .fvar x => addUse (.slot (rv x) s false (some d.fvarId)); addFlow s (some (rv x))
            | _ => addUse (.slotOpaque s); addFlow s none
        else
          -- A partial application (a closure of itself) or an
          -- over-application: its arguments are used whole.
          modify fun f => { f with tailOnly := false }
          wholeArgs args exit
      else
        let ctorLet? ← do
          let some (.ctorInfo cv) := (← getEnv).find? g | pure none
          if args.size != cv.numParams + cv.numFields then pure none else
          let some (_, cs, fts) ← indInfo? d.type | pure none
          let some ci := cs.cs.findIdx? (·.name == g) | pure none
          pure (some { ctor := g, cidx := ci, ctors := cs, args := args.map (fun | .fvar x => .fvar (rv x) | a => a),
                       ty := d.type, exit, depth, irrFields := (fts[ci]?.getD #[]).map irrelevantTy : CtorLet })
        -- A constant that is a known constructor application.
        let constLet? ← do
          if !args.isEmpty then pure none else
          let some ctor := constCtor? prog g | pure none
          let some (_, cs, fts) ← indInfo? d.type | pure none
          let some ci := cs.cs.findIdx? (·.name == ctor) | pure none
          pure (some { ctor, cidx := ci, ctors := cs, ty := d.type, exit, const := true,
                       args := Array.replicate (cs.cs[ci]!.numParams + cs.cs[ci]!.numFields) .erased,
                       irrFields := (fts[ci]?.getD #[]).map irrelevantTy : CtorLet })
        if let some cl := ctorLet? then
          modify fun f => { f with ctorLets := f.ctorLets.insert d.fvarId cl, ctorOrder := f.ctorOrder.push d.fvarId }
        else if let some cl := constLet? then
          modify fun f => { f with ctorLets := f.ctorLets.insert d.fvarId cl }
        else if pinning.contains g then
          for a in args do
            if let .fvar x := a then addUse (.pinned (rv x))
        else if let some callee := prog[g]? then
          if callee.value matches .code _ && args.size == callee.params.size && !callee.params.isEmpty then
            modify fun f => { f with calls := f.calls.insert d.fvarId g, callDepth := f.callDepth.insert d.fvarId depth }
            for h : i in [:args.size] do
              match args[i] with
              | .fvar x => addUse (.ext (rv x) g i exit d.fvarId)
              | _ => pure ()
          else wholeArgs args exit
        else wholeArgs args exit
      return selfCall || kr
    | .fvar g args =>
      addUse (.whole (rv g) (!kr))
      wholeArgs args (!kr)
      return kr
    | _ => return kr
  | .jp d k =>
    for h : i in [:d.params.size] do
      setTy d.params[i].fvarId d.params[i].type
      modify fun f => { f with slotOfVar := f.slotOfVar.insert d.params[i].fvarId (.jp self d.fvarId i) }
    modify fun f => { f with jps := f.jps.insert d.fvarId d.params }
    -- Jumps to it only follow in `k`.
    let br ← collectCode refine (depth + 1) d.value
    modify fun f => { f with jpRec := f.jpRec.insert d.fvarId br }
    collectCode refine depth k
  | .fun d k _ =>
    modify fun f => { f with hasFun := true }
    let br ← collectCode refine (depth + 1) d.value
    let kr ← collectCode refine depth k
    return br || kr
  | .jmp j args =>
    let rec_ := (← get).jpRec.getD j false
    for h : i in [:args.size] do
      let s := SlotId.jp self j i
      match args[i] with
      | .fvar x => addUse (.slot (rv x) s (!rec_) none); addFlow s (some (rv x))
      | _ => addUse (.slotOpaque s); addFlow s none
    return rec_
  | .cases cs =>
    let ty := (← get).types.getD cs.discr anyExpr
    let info? ← indInfo? ty
    let ctors? := info?.bind fun (iv, k, _) => if iv.name == cs.typeName then some k else none
    let mut rec_ := false
    let mut pending : Array (FVarId × CtorLet) := #[]
    for alt in cs.alts do
      if let .alt ctor ps k _ := alt then
        let ci := (ctors?.bind (·.cs.findIdx? (·.name == ctor))).getD 0
        let off := match ctors? with | some k' => k'.base ci | none => 0
        for h : i in [:ps.size] do
          setTy ps[i].fvarId ps[i].type
          modify fun f => { f with fieldOf := f.fieldOf.insert ps[i].fvarId (cs.discr, off + i, cs.typeName) }
        -- Inside the alternative, the matched value is known to be this
        -- constructor applied to the alternative's parameters (an alias).
        let mut refine := refine
        if let some cs' := ctors? then
          let alias ← mkFreshFVarId
          let np := cs'.cs[ci]!.numParams
          let cl : CtorLet := { ctor, cidx := ci, ctors := cs', ty, exit := false,
                                args := Array.replicate np .erased ++ ps.map (.fvar ·.fvarId),
                                irrFields := ps.map (irrelevantTy ·.type), alias := some (rv cs.discr) }
          modify fun f => { f with ctorLets := f.ctorLets.insert alias cl, types := f.types.insert alias ty }
          pending := pending.push (alias, cl)
          refine := refine.insert cs.discr alias
        rec_ := (← collectCode refine depth k) || rec_
      else rec_ := (← collectCode refine depth alt.getCode) || rec_
    -- The aliases' exits (not used: an alias is never built).
    for (a, cl) in pending do
      modify fun f => { f with ctorLets := f.ctorLets.insert a { cl with exit := !rec_ } }
    addUse (.inspect (rv cs.discr) cs.typeName (!rec_))
    return rec_
  | .return x => addUse (.ret (rv x)); return false
  | .unreach _ => return false

end Collect

def collectDecl (prog : Std.HashMap Name (Decl .pure)) (pinning : NameSet) (d : Decl .pure) : CoreM DeclFacts := do
  let .code body := d.value | return { name := d.name, hasFun := true }
  let init : DeclFacts := { name := d.name, types := d.params.foldl (fun m p => m.insert p.fvarId p.type) {},
                            slotOfVar := d.params.zipIdx.foldl (fun m (p, i) => m.insert p.fvarId (.param d.name i)) {} }
  let (_, f) ← (collectCode prog pinning d.name d.params.size {} 0 body).run init
  return { f with size := body.size }

/-! ## The analysis: a greatest fixed point -/

structure AState where
  /-- The shape of every parameter that may be split (absent: a leaf). -/
  slots : Std.HashMap SlotId Shape := {}
  /-- The shape of every declaration's result that may be a tuple. -/
  results : Std.HashMap Name Shape := {}
  /-- Constructor lets that stay (`(declaration, variable)`). -/
  built : Std.HashSet (Name × FVarId) := {}
  /-- The levels of results (declaration, path) that some other
  declaration reads field by field. -/
  benefit : Std.HashSet (Name × List Nat) := {}
  /-- The levels of results that some declaration uses whole (rebuilds). -/
  wholeUses : Std.HashSet (Name × List Nat) := {}
  /-- The levels of parameters that some caller passes a value whose
  fields are known (a non-recursive declaration's parameter is split only
  there). -/
  paramBenefit : Std.HashSet (SlotId × List Nat) := {}
  /-- The levels of parameters and results that receive a value whose
  object exists (a matched value, a constant, or such a level in turn):
  rebuilding it there would allocate what the program shared. Only grows. -/
  existing : Std.HashSet (Tgt × List Nat) := {}
  /-- The levels of a declaration's parameters that some other declaration
  passes an object that exists (a value whose fields are not known, a
  matched value, a constant, a value built anyway, an existing level):
  a loop that runs no step holds it until it returns (`isExisting`). Only
  grows. -/
  entryExisting : Std.HashSet (SlotId × List Nat) := {}
  /-- The call results (`(declaration, variable)`) that the declaration uses
  whole somewhere: rebuilt there from the tuple, an object that exists
  (another rebuild would be a second copy, `freshFed`). Only grows. -/
  builtCalls : Std.HashSet (Name × FVarId) := {}
  /-- The call results that the declaration rebuilds at two places that do
  not share a scope (`constrainDecl`): the declaration calls the wrapper
  there and keeps the result whole (one object per level, as the callee
  built; `rootOf`). Only grows. -/
  wholeCalls : Std.HashSet (Name × FVarId) := {}
  /-- Whether this round over every declaration (after a fixed point, on
  shapes that no longer shrink) records the rebuilds (`sites`, `callSites`)
  and acts on them: during the fixed point a level may be rebuilt only
  until it shrinks. -/
  checkSites : Bool := false
  /-- While constraining a declaration: how many join-point bodies enclose
  the current use, and the levels each use rebuilds, with whether a
  join-point body encloses it. -/
  siteDepth : Nat := 0
  sites : Std.HashMap SlotId (Array (List Nat × Bool)) := {}
  callSites : Std.HashMap FVarId (Array (List Nat × Bool)) := {}
  /-- While constraining a declaration (`checkSites`): the places a fresh
  constructor application or call result goes split (by its variable and
  level; `true`: another declaration's worker). -/
  flowSites : Std.HashMap (FVarId × List Nat) (Array Bool) := {}
  /-- (For `L2R_FLATTEN_DEBUG`: the sites that made a call result whole.) -/
  wholeCallSites : Std.HashMap (Name × FVarId) (Array (List Nat × Bool)) := {}
  /-- The declarations to constrain again (their facts depend on what
  changed). -/
  dirty : NameSet := {}
  /-- The declarations that call each declaration (saturated). -/
  callersOf : Std.HashMap Name (Array Name) := {}
  /-- The declarations some code of the program mentions (the others run
  only as entry points, at most once per start, or never: Lean's original
  of a `_redArg` declaration that every caller bypasses). -/
  referenced : NameSet := {}
  /-- The declarations with a split parameter rebuilt at the loop's exit:
  their wrappers run the first step (`allowedWhole`), and every other
  declaration calls them through it (whole arguments and result). Only
  grows. -/
  peel : NameSet := {}
  changed : Bool := false

abbrev AM := StateM AState

def SlotId.decl : SlotId → Name
  | .param d _ => d
  | .jp d _ _ => d

/-- Declaration `d` to constrain again. -/
def dirtyDecl (d : Name) : AM Unit :=
  modify fun st => { st with dirty := st.dirty.insert d, changed := true }

/-- Declaration `f` and its callers to constrain again (after a change to
its result, its peeling or its parameters' shapes, which callers read). -/
def dirtyCallers (f : Name) : AM Unit := do
  dirtyDecl f
  for c in (← get).callersOf.getD f #[] do dirtyDecl c

def slotShape (s : SlotId) : AM (Option Shape) := return (← get).slots[s]?

def resultShape (f : Name) : AM (Option Shape) := return (← get).results[f]?

/-- Whether `f` gets a worker: a split parameter or a tuple result. -/
def hasWorker (prog : Program) (f : Name) : AM Bool := do
  let st ← get
  if st.results[f]?.any (·.isNode) then return true
  let some d := prog.decls[f]? | return false
  return (List.range d.params.size).any fun i => st.slots[SlotId.param f i]?.any (·.isNode)

section Analysis
variable (facts : DeclFacts)

/-- The root of variable `v` in the current state. -/
partial def rootOf (v : FVarId) : AM Root := do
  if let some s := (← slotOf v) then return .slot s []
  if let some cl := facts.ctorLets[v]? then
    -- A matched value: its own root when its fields are known anyway.
    if let some m := cl.alias then
      match ← rootOf m with
      | .opaque | .irr => return .ctor v
      | r => return r
    return .ctor v
  if let some f := facts.calls[v]? then
    -- (Other declarations call a peeled one through its wrapper: a whole
    -- result there.)
    -- (A result the declaration keeps whole: through the wrapper,
    -- `wholeCalls`.)
    if (← resultShape f).any (·.isNode) && (f == facts.name || !(← get).peel.contains f) &&
        !(← get).wholeCalls.contains (facts.name, v) then
      return .call f v []
  if let some (p, i, tn) := facts.fieldOf[v]? then
    let r ← rootOf p
    let some (.node _ ind _ fs) ← shapeOfRoot r | return .opaque
    if ind != tn then return .opaque
    match fs[i]? with
    | some (.irr _) => return .irr
    | some _ => return ← subRoot r i
    | none => return .opaque
  return .opaque
where
  /-- The slot of a parameter that may be split. -/
  slotOf (v : FVarId) : AM (Option SlotId) := do
    let some s := facts.slotOfVar[v]? | return none
    return if (← get).slots.contains s then some s else none
  /-- The sub-value of root `r` at child `j`. -/
  subRoot (r : Root) (j : Nat) : AM Root := do
    match r with
    | .slot s p => return .slot s (p ++ [j])
    | .call f x p => return .call f x (p ++ [j])
    | .ctor x =>
      let some cl := facts.ctorLets[x]? | return .opaque
      let off := cl.ctors.base cl.cidx
      if j < off || j ≥ off + cl.irrFields.size then return .irr
      let i := j - off
      if cl.irrFields[i]?.getD false then return .irr
      match cl.args[cl.ctors.cs[cl.cidx]!.numParams + i]? with
      | some (.fvar a) => rootOf a
      | _ => return .opaque
    | _ => return .opaque
  /-- The shape of the value at root `r`, when its fields are known. -/
  shapeOfRoot (r : Root) : AM (Option Shape) := do
    match r with
    | .slot s p => return (← slotShape s).bind (·.at? p)
    | .call f _ p => return (← resultShape f).bind (·.at? p)
    | .ctor x => return some (← ctorShape x)
    | _ => return none
  /-- The shape of constructor let `x`: a node of its arguments' shapes (the
  other constructor's children `irr`). -/
  ctorShape (x : FVarId) : AM Shape := do
    let some cl := facts.ctorLets[x]? | return .leaf (facts.types.getD x anyExpr)
    let np := cl.ctors.cs[cl.cidx]!.numParams
    let mut fs := #[]
    for h : c in [:cl.ctors.size] do
      if cl.ctors.shared && c != cl.cidx then continue
      for h' : i in [:cl.ctors.cs[c]!.numFields] do
        if c != cl.cidx || (cl.irrFields[i]?.getD false) then
          fs := fs.push (.irr anyExpr)
        else
          match cl.args[np + i]? with
          | some (.fvar a) => fs := fs.push (← shapeOfVar a)
          | _ => fs := fs.push (.leaf anyExpr)
    let ind := cl.ty.consumeMData.getAppFn.constName
    return .node cl.ty ind cl.ctors fs
  /-- The shape of variable `v`'s value: its root's, or a leaf. -/
  shapeOfVar (v : FVarId) : AM Shape := do
    match ← shapeOfRoot (← rootOf v) with
    | some s => return s
    | none => return .leaf (facts.types.getD v anyExpr)

end Analysis

/-- Make the node at `path` of slot `s` a leaf. -/
def cutSlot (s : SlotId) (path : List Nat) : AM Unit := do
  let some sh ← slotShape s | return
  if sh.nodeAt path then
    modify fun st => { st with slots := st.slots.insert s (sh.cutAt path) }
    match s with
    | .param f _ => dirtyCallers f
    | .jp d .. => dirtyDecl d

def cutResult (f : Name) (path : List Nat) : AM Unit := do
  let some sh ← resultShape f | return
  if sh.nodeAt path then
    modify fun st => { st with results := st.results.insert f (sh.cutAt path) }
    dirtyCallers f

def markBuilt (d : Name) (x : FVarId) : AM Unit := do
  unless (← get).built.contains (d, x) do
    modify fun st => { st with built := st.built.insert (d, x) }
    dirtyDecl d

/-- Levels `paths` (below `path`) of parameter `s` receive an existing
object from another declaration. -/
def noteEntryExisting (s : SlotId) (path : List Nat) (paths : Array (List Nat)) : AM Unit := do
  for q in paths do
    unless (← get).entryExisting.contains (s, path ++ q) do
      modify fun st => { st with entryExisting := st.entryExisting.insert (s, path ++ q) }
      dirtyDecl s.decl

/-- Whether one path is a prefix of the other (levels of one value, one
inside the other). -/
def comparable (a b : List Nat) : Bool := a.isPrefixOf b || b.isPrefixOf a

/-- The paths of the nodes of shape `s` (`pre` first: parents before their
children). -/
partial def nodePaths (s : Shape) (pre : List Nat) : Array (List Nat) :=
  match s with
  | .node _ _ _ fs => fs.zipIdx.foldl (fun acc (f, i) => acc ++ nodePaths f (pre ++ [i])) #[pre]
  | _ => #[]

section Constraints
variable (facts : DeclFacts)

/-- The sub-value of root `r` at `path`. -/
def subRootAt (r : Root) (path : List Nat) : AM Root :=
  path.foldlM (fun r i => rootOf.subRoot facts r i) r

/-- Whether every value passed to slot `s` has, at `path`, a constructor
application of this declaration that the pass leaves unbuilt, or a call's
result that the callee built and this declaration does not rebuild
elsewhere, also through join-point parameters (values that are so in
turn; a join point's parameter is never rebuilt). -/
partial def freshFed (s : SlotId) (path : List Nat) : AM Bool := do
  let mut work : List (SlotId × List Nat) := [(s, path)]
  let mut seen : Std.HashSet (SlotId × List Nat) := {}
  repeat
    let (s, path) :: rest := work | break
    work := rest
    if seen.contains (s, path) then continue
    seen := seen.insert (s, path)
    let flows := facts.flows.getD s #[]
    if flows.isEmpty then return false
    for a? in flows do
      let some a := a? | return false
      match ← subRootAt facts (← rootOf facts a) path with
      | .ctor x =>
        if (facts.ctorLets[x]?.any fun cl => cl.alias.isSome || cl.const) then return false
        if (← get).built.contains (facts.name, x) then return false
      | .slot s'@(.jp ..) p' => work := (s', p') :: work
      -- A call's result, which the callee built at every call (it returns
      -- no existing object there), unless this declaration rebuilds it
      -- elsewhere too (a second copy).
      | .call g x p' =>
        if (← get).existing.contains (Tgt.res g, p') || (← get).builtCalls.contains (facts.name, x) then
          return false
      | _ => return false
  return true

/-- Whether a use of the whole value at root `.slot s path` may rebuild it
there (see the module comment): only a declaration's parameter at the exit
of a loop whose self-calls are all tail calls (no self-call reachable),
when every self-call passes a freshly built value (directly or through
join points): the loop built one per step before, and now builds one when
it ends. The first step runs in the wrapper (`peel`), on the value as it
came: a loop that ends at once returns it without a rebuild. So a run of
k steps that built k values builds at most one. A loop that passes the
value on unchanged keeps it whole (the rebuild would be an allocation it
never made), and so does a body larger than `maxPeelSize` (its copy would
be too large). A join point's parameter is never rebuilt (rebuilding one
gained nothing measurable on the benchmark programs). -/
def allowedWhole (s : SlotId) (path : List Nat) (exit : Exit) : AM Bool := do
  let loopExit := facts.recursive && facts.tailOnly && exit
  match s with
  | .jp .. => return false
  | .param .. =>
    if loopExit && facts.size ≤ maxPeelSize && (← freshFed facts s path) then
      unless (← get).peel.contains facts.name do
        modify fun st => { st with peel := st.peel.insert facts.name }
        dirtyCallers facts.name
        -- Its wrapper runs the first step on what every caller passes:
        -- existing objects there (`isExisting`).
        for (_, ps) in facts.slotOfVar.toList do
          if let .param .. := ps then
            if let some sh ← slotShape ps then noteEntryExisting ps [] (nodePaths sh [])
      return true
    return false

/-- A use of the whole value at root `r`: a constructor application stays
(a matched value is there already); a loop's parameter is rebuilt at its
exit where `allowedWhole` says so and no existing object reaches it there,
otherwise (and a join point's parameter always) the parameter is not split
there; a call's result is rebuilt there (the
callee no longer builds it; `pruneUnread` keeps it whole where that would
allocate a value the callee returned without building). -/
def wholeRoot (r : Root) (exit : Exit) : AM Unit := do
  match r with
  | .ctor x => markBuilt facts.name x
  | .slot s path =>
    if let some sh := (← slotShape s).bind (·.at? path) then
      if !sh.isNode then return
      if (← get).existing.contains (Tgt.slot s, path) then cutSlot s path
      else if ← allowedWhole facts s path exit then
        -- The rebuild builds every split level below too: a shared object
        -- there, or a value that is not a fresh one (another value's level,
        -- which would be a second copy of it), stays whole (a leaf).
        for q in nodePaths sh [] do
          if !q.isEmpty && ((← get).existing.contains (Tgt.slot s, path ++ q) ||
              !(← freshFed facts s (path ++ q))) then
            cutSlot s (path ++ q)
        -- The site, for `constrainDecl` (two rebuilds of one value where a
        -- join point's body holds one of them).
        if (← get).checkSites then
          let nested := (← get).siteDepth > 0
          modify fun st => { st with sites := st.sites.insert s ((st.sites.getD s #[]).push (path, nested)) }
      else cutSlot s path
  | .call f x path =>
    -- Rebuilt here, where the use is of a level the tuple spreads (not of
    -- a leaf): an object that exists (`builtCalls`); the site, for
    -- `constrainDecl` (`wholeCalls`).
    unless (← resultShape f).any (fun sh => sh.nodeAt path) do return
    unless (← get).builtCalls.contains (facts.name, x) do
      modify fun st => { st with builtCalls := st.builtCalls.insert (facts.name, x) }
      dirtyDecl facts.name
    if (← get).checkSites then
      let nested := (← get).siteDepth > facts.callDepth.getD x 0
      modify fun st => { st with callSites := st.callSites.insert x ((st.callSites.getD x #[]).push (path, nested)) }
    -- (A declaration no code mentions rebuilds at most once per start.)
    if (← get).referenced.contains facts.name then
      unless (← get).wholeUses.contains (f, path) do
        modify fun st => { st with wholeUses := st.wholeUses.insert (f, path) }
  | _ => pure ()

/-- A call's result read field by field at root `r` (by another
declaration: a self-call's result returned as it is only passes the tuple
on). -/
def noteBenefit (r : Root) : AM Unit := do
  if let .call f _ p := r then
    if f == facts.name then return
    unless (← get).benefit.contains (f, p) do
      modify fun st => { st with benefit := st.benefit.insert (f, p) }

/-- Whether the value at root `r` is an object that exists (a matched
value, a constant, a constructor application or a call result that stays
or is rebuilt anyway, a declaration's parameter, or a level that receives
one). -/
def isExisting (r : Root) : AM Bool := do
  match r with
  | .ctor x =>
    if facts.ctorLets[x]?.any fun cl => cl.alias.isSome || cl.const then return true
    return (← get).built.contains (facts.name, x)
  -- A declaration's parameter holds what its caller passed: where some
  -- self-call passes it on unchanged, or where some other declaration
  -- passes an existing object (a loop that runs no step returns it; a loop
  -- whose every step builds a new value holds the caller's only until its
  -- first step), also through the wrapper (callers the pass leaves alone,
  -- function values, a peeled loop's first step: `analyze`, `allowedWhole`).
  | .slot s@(.param ..) p =>
    if !(← freshFed facts s p) then return true
    return (← get).entryExisting.contains (s, p)
  | .slot s p => return (← get).existing.contains (Tgt.slot s, p)
  | .call f x p => return (← get).existing.contains (Tgt.res f, p) || (← get).builtCalls.contains (facts.name, x)
  | _ => return false

/-- A value (root `r`, shape `σ`) passed where shape `τ` is expected (into
`tgt`): `cut` the target where the value's fields are not known, and use
the value whole where the target takes it whole (`project`: where the
target is a node and the value is not, the value is projected there
instead, an argument of another declaration's worker). A child the value
does not have (the other constructor's) is a placeholder there. -/
partial def flowInto (τ : Shape) (r : Root) (σ : Shape) (path : List Nat) (exit : Exit)
    (cut : List Nat → AM Unit) (project : Bool) (tgt : Option Tgt := none) (pb : Option SlotId := none) :
    AM Unit := do
  match τ, σ with
  | .node _ ind _ tfs, .node _ ind' _ sfs =>
    if ind != ind' || tfs.size != sfs.size then
      cut path
      wholeRoot facts r exit
      if let some ps := pb then noteEntryExisting ps path (nodePaths τ [])
    else
      noteBenefit facts r
      -- (Where a fresh value goes split, for `constrainDecl`.)
      if (← get).checkSites then
        let key? : Option (FVarId × List Nat) := match r with
          | .ctor x => if facts.ctorLets[x]?.any (fun cl => cl.alias.isNone && !cl.const) then some (x, []) else none
          | .call _ x p => some (x, p)
          | _ => none
        if let some key := key? then
          modify fun st => { st with flowSites := st.flowSites.insert key ((st.flowSites.getD key #[]).push pb.isSome) }
      if let some ps := pb then
        unless (← get).paramBenefit.contains (ps, path) do
          modify fun st => { st with paramBenefit := st.paramBenefit.insert (ps, path) }
        -- (Every level below an existing object holds one too.)
        if ← isExisting facts r then noteEntryExisting ps path (nodePaths τ [])
      if let some t := tgt then
        if ← isExisting facts r then
          unless (← get).existing.contains (t, path) do
            modify fun st => { st with existing := st.existing.insert (t, path) }
            match t with
            | .slot s => dirtyDecl s.decl
            | .res f => dirtyCallers f
      for h : i in [:tfs.size] do
        let t := tfs[i]
        if t matches .irr _ then continue
        let some sf := sfs[i]? | continue
        if sf matches .irr _ then continue
        flowInto t (← rootOf.subRoot facts r i) sf (path ++ [i]) exit cut project tgt pb
  | .node .., _ =>
    unless project do cut path
    -- A value whose fields are not known here: an object that exists.
    if let some ps := pb then noteEntryExisting ps path (nodePaths τ [])
  | _, .node .. => wholeRoot facts r exit
  | _, _ => pure ()

/-- Apply every constraint of one declaration once. -/
def constrainDecl (prog : Program) : AM Unit := do
  modify fun st => { st with sites := {}, callSites := {}, flowSites := {} }
  -- A call's result kept whole here (`wholeCalls`): the wrapper rebuilds
  -- every level (a use of the whole result, for `pruneUnread`).
  if (← get).referenced.contains facts.name then
    for (x, f) in facts.calls.toList do
      if (← get).wholeCalls.contains (facts.name, x) then
        unless (← get).wholeUses.contains (f, []) do
          modify fun st => { st with wholeUses := st.wholeUses.insert (f, []) }
  for h : k in [:facts.uses.size] do
    let u := facts.uses[k]
    modify fun st => { st with siteDepth := facts.useDepth[k]?.getD 0 }
    match u with
    | .slot a s exit call =>
      let r ← rootOf facts a
      let σ ← rootOf.shapeOfVar facts a
      -- (A self-call through the wrapper, `wholeCalls`: the argument whole,
      -- the worker's parameter the fields of an existing object.)
      let wc := (← get).wholeCalls
      if call.any fun c => wc.contains (facts.name, c) then
        wholeRoot facts r exit
        if let some sh ← slotShape s then noteEntryExisting s [] (nodePaths sh [])
        continue
      match ← slotShape s with
      | some τ => flowInto facts τ r σ [] exit (cutSlot s) false (some (.slot s))
      | none => wholeRoot facts r exit
    | .slotOpaque s => cutSlot s []
    | .ret a =>
      let r ← rootOf facts a
      let σ ← rootOf.shapeOfVar facts a
      match ← resultShape facts.name with
      | some τ =>
        if τ.isNode then flowInto facts τ r σ [] true (cutResult facts.name) false (some (.res facts.name))
        else wholeRoot facts r true
      | none => wholeRoot facts r true
    | .ext a f i exit call =>
      let r ← rootOf facts a
      -- (A call through the wrapper, `wholeCalls`: the same.)
      if (← get).wholeCalls.contains (facts.name, call) then
        wholeRoot facts r exit
        if let some sh ← slotShape (.param f i) then noteEntryExisting (.param f i) [] (nodePaths sh [])
        continue
      if (← hasWorker prog f) && !(← get).peel.contains f then
        let σ ← rootOf.shapeOfVar facts a
        let τ := (← slotShape (.param f i)).getD (.leaf anyExpr)
        flowInto facts τ r σ [] exit (fun _ => pure ()) true none (some (.param f i))
      else wholeRoot facts r exit
    | .inspect v tn exit =>
      match ← rootOf.shapeOfVar facts v with
      | .node _ ind .. =>
        if ind != tn then wholeRoot facts (← rootOf facts v) exit
        else noteBenefit facts (← rootOf facts v)
      | _ => pure ()
    | .whole a exit => wholeRoot facts (← rootOf facts a) exit
    | .pinned a =>
      match ← rootOf facts a with
      | .ctor x => markBuilt facts.name x
      | .slot s path => cutSlot s path
      | .call f _ path => cutResult f path
      | _ => pure ()
  -- The arguments of a constructor application that stays are used whole.
  for x in facts.ctorOrder do
    if (← get).built.contains (facts.name, x) then
      let some cl := facts.ctorLets[x]? | continue
      let np := cl.ctors.cs[cl.cidx]!.numParams
      for h : i in [:cl.irrFields.size] do
        if cl.irrFields[i] then continue
        if let some (.fvar a) := cl.args[np + i]? then
          modify fun st => { st with siteDepth := cl.depth }
          wholeRoot facts (← rootOf facts a) cl.exit
  -- Each rebuild of a value runs once per run of the code that binds it
  -- only where the rebuilds share one scope (the rewrite builds a value
  -- once along its scope, `Env.mats`): a rebuild in a join point's body
  -- and another one of the same value (or of a level inside it) may both
  -- run, so that level stays whole.
  for (s, ss) in (← get).sites.toList do
    for h : i in [:ss.size] do
      for h' : j in [i + 1:ss.size] do
        let (p, n) := ss[i]
        let (q, m) := ss[j]
        if (n || m) && comparable p q then
          cutSlot s (if p.length ≤ q.length then p else q)
  -- A fresh value that goes split both to another declaration's worker
  -- (which may return it as it came, in a tuple a caller rebuilds) and to a
  -- second place (a self-call, a jump, a return, another call) counts as
  -- built: one object, which the callee gets as an existing one.
  for ((x, p), ks) in (← get).flowSites.toList do
    unless ks.size ≥ 2 && ks.any id do continue
    if facts.ctorLets.contains x then
      if p.isEmpty then markBuilt facts.name x
    else unless (← get).builtCalls.contains (facts.name, x) do
      modify fun st => { st with builtCalls := st.builtCalls.insert (facts.name, x) }
      dirtyDecl facts.name
  -- The same for a call's result: this declaration keeps it whole.
  for (x, ss) in (← get).callSites.toList do
    let conflict := (List.range ss.size).any fun i => (List.range ss.size).any fun j =>
      i < j && (ss[i]!.2 || ss[j]!.2) && comparable ss[i]!.1 ss[j]!.1
    if conflict && !(← get).wholeCalls.contains (facts.name, x) then
      modify fun st => { st with wholeCalls := st.wholeCalls.insert (facts.name, x),
                                 wholeCallSites := st.wholeCallSites.insert (facts.name, x) ss }
      dirtyDecl facts.name

end Constraints

/-! ## The transformation -/

/-- The tag of a value spread over variables: its constructor, known, or a
`Bool` variable (`true`: the second constructor). -/
inductive Tag where
  | known (c : Nat)
  | var (t : FVarId)
  deriving Inhabited

/-- A variable's value during the rewrite: a real argument, a field without
data (or of the constructor the value does not have: a placeholder), or a
value whose fields are known (`mat`: a variable holding it, once built). -/
inductive VVal where
  | real (a : Arg .pure)
  | irr (ty : Expr)
  | node (ty : Expr) (induct : Name) (ctors : Ctors) (tag : Tag) (fields : Array VVal) (mat : Option FVarId)
  deriving Inhabited

def fvarCmp (a b : FVarId) : Ordering := Name.quickCmp a.name b.name

/-- The rewrite's scope: the values of variables, the tuples call results
were read from, the tags known in the current alternative, and the values
built so far (`mats`, by `VVal.key`: a value reached through two variables,
such as a record and a projection of its inner record, is built once along
its scope). -/
structure Env where
  vals : Std.TreeMap FVarId VVal fvarCmp := {}
  tuples : Std.TreeMap FVarId FVarId fvarCmp := {}
  tags : Std.TreeMap FVarId Nat fvarCmp := {}
  mats : Std.TreeMap String FVarId compare := {}
  deriving Inhabited

/-- A key of a value whose fields are known: its constructors, tag and
leaves (the same key, the same value). -/
partial def VVal.key : VVal → String
  | .real (.fvar x) => s!"v{x.name}"
  | .real _ => "e"
  | .irr _ => "i"
  | .node _ ind _ tag fs _ =>
    let t := match tag with | .known c => s!"k{c}" | .var t => s!"t{t.name}"
    s!"({ind} {t}" ++ fs.foldl (fun acc f => acc ++ " " ++ f.key) "" ++ ")"

def Env.insert (env : Env) (x : FVarId) (v : VVal) : Env := { env with vals := env.vals.insert x v }

/-- The constructor of a tag, if known here. -/
def Env.tagOf? (env : Env) : Tag → Option Nat
  | .known c => some c
  | .var t => env.tags.get? t

/-- Code to put before a use: a `let`, or a join point over the rest (its
parameters) whose value is chosen by a `cases` on `scrut` (each arm: its
constructor and parameters, its own steps, the arguments of its jump). -/
inductive PreStep where
  | let (d : LetDecl .pure)
  | join (j : FVarId) (ps : Array (Param .pure)) (scrut : FVarId) (typeName : Name)
      (arms : Array (Name × Array (Param .pure) × Array PreStep × Array (Arg .pure)))

instance : Inhabited PreStep := ⟨.let default⟩

/-- The rewrite's context for one declaration. -/
structure XCtx where
  facts : DeclFacts
  st : AState
  prog : Program
  /-- This declaration's result shape when it returns a tuple. -/
  result : Option Shape
  /-- The type of the code's results (the tuple's, or the declaration's). -/
  resTy : Expr
  /-- The workers, by declaration. -/
  workers : Std.HashMap Name Name

structure XState where
  /-- The variables the rewrite introduced with pure values (projections,
  placeholders, rebuilt values): dropped again when unused. -/
  introduced : Std.HashSet FVarId := {}

abbrev XM := ReaderT XCtx (StateRefT XState CoreM)

def freshLet (binder : Name) (ty : Expr) (v : LetValue .pure) : XM (LetDecl .pure) := do
  let x ← mkFreshFVarId
  modify fun s => { s with introduced := s.introduced.insert x }
  return { fvarId := x, binderName := binder, type := ty, value := v }

def freshParam (binder : Name) (ty : Expr) : XM (Param .pure) := do
  return { fvarId := ← mkFreshFVarId, binderName := binder, type := ty, borrow := false }

/-- The steps, then `k`. -/
partial def wrapPre (pre : Array PreStep) (k : Code .pure) : XM (Code .pure) := do
  let resTy := (← read).resTy
  let mut k := k
  for st in pre.reverse do
    match st with
    | .let d => k := .let d k
    | .join j ps scrut tn arms =>
      let ty := ps.foldr (fun p acc => .forallE p.binderName p.type acc .default) resTy
      let alts ← arms.mapM fun (c, aps, steps, args) => do
        return Alt.alt c aps (← wrapPre steps (.jmp j args))
      k := .jp (FunDecl.mk j `_flat_j ps ty k) (.cases ⟨tn, resTy, scrut, alts⟩)
  return k

/-- The tuple type of the leaves of shape `s`. -/
def tupleTyOf (s : Shape) : Expr :=
  let ts := s.leafTypes
  mkAppN (mkConst (flatTupleName ts.size)) ts

/-- Add `L2RFlat.Tuple<k>` to the environment (once). -/
def ensureTuple (k : Nat) : CoreM Unit := do
  let n := flatTupleName k
  if (← getEnv).contains n then return
  let ty1 := mkSort levelOne
  let mut indTy := ty1
  for _ in [:k] do indTy := .forallE `α ty1 indTy .default
  -- Under the `k` type binders and the fields before it, field `j`'s type
  -- `α_j` is de Bruijn index `k - 1`; the result's `α_i` is `2k - 1 - i`.
  let res := mkAppN (mkConst n) ((List.range k).toArray.map fun i => .bvar (2 * k - 1 - i))
  let mut ctorTy := res
  for _ in [:k] do ctorTy := .forallE `a (.bvar (k - 1)) ctorTy .default
  for _ in [:k] do ctorTy := .forallE `α ty1 ctorTy .default
  addDecl (.inductDecl [] k [{ name := n, type := indTy, ctors := [{ name := flatTupleCtor k, type := ctorTy }] }] false)
  -- The compiler's caches of an inductive (its mono type, layouts), which
  -- Lean's own passes read (`getOtherDeclMonoType`, `getCtorLayout`).
  compileInductives #[n]

/-- The value of variable `x`. -/
def valOf (env : Env) (x : FVarId) : VVal := (env.vals.get? x).getD (.real (.fvar x))

/-- The value of argument `a`. -/
def argVal (env : Env) : Arg .pure → VVal
  | .fvar x => valOf env x
  | a => .real a

/-- A `Bool` literal for tag `c`. -/
def tagLit (c : Nat) : XM (LetDecl .pure) :=
  freshLet `_flat_tag Shape.boolTy (.const (if c == 1 then ``Bool.true else ``Bool.false) [] #[])

/-- Build the value: steps to add first, the argument holding it, and the
scope that remembers what was built (`Env.mats`). A value whose tag is not
known here is built in both constructors by a `cases` on its tag. -/
partial def materialize (env : Env) (v : VVal) : XM (Array PreStep × Arg .pure × Env) := do
  match v with
  | .real a => return (#[], a, env)
  | .irr _ => return (#[], .erased, env)
  | .node ty _ ctors tag fields mat =>
    if let some x := mat then return (#[], .fvar x, env)
    let key := v.key
    if let some x := env.mats.get? key then return (#[], .fvar x, env)
    let build (env : Env) (c : Nat) : XM (Array PreStep × Arg .pure × Env) := do
      let ci := ctors.cs[c]!
      let mut pre := #[]
      let mut env := env
      let mut args : Array (Arg .pure) := Array.replicate ci.numParams .erased
      for f in ctors.kids c fields do
        let (p, a, env') ← materialize env f
        pre := pre ++ p
        args := args.push a
        env := env'
      let d ← freshLet `_flat ty (.const ci.name [] args)
      return (pre.push (.let d), .fvar d.fvarId, { env with mats := env.mats.insert key d.fvarId })
    match env.tagOf? tag, tag with
    | some c, _ => build env c
    | none, .var t =>
      let x ← freshParam `_flat ty
      let j ← mkFreshFVarId
      let mut arms := #[]
      for c in [0, 1] do
        -- (What an arm builds stays in that arm.)
        let (steps, a, _) ← build { env with tags := env.tags.insert t c } c
        arms := arms.push ((if c == 1 then ``Bool.true else ``Bool.false), #[], steps, #[a])
      return (#[.join j #[x] t ``Bool arms], .fvar x.fvarId, { env with mats := env.mats.insert key x.fvarId })
    | none, .known c => build env c

/-- An argument as a variable (`◾` bound to a placeholder of type `ty`). -/
def asFVar (a : Arg .pure) (ty : Expr) : XM (Array PreStep × FVarId) := do
  match a with
  | .fvar x => return (#[], x)
  | _ =>
    let d ← freshLet `_flat ty .erased
    return (#[.let d], d.fvarId)

/-- A value of shape `s` whose leaves are `leaves` (in order). -/
partial def ofLeaves (s : Shape) (leaves : Array (Arg .pure)) (i : Nat := 0) : VVal × Nat :=
  match s with
  | .leaf _ => (.real (leaves[i]?.getD .erased), i + 1)
  | .irr t => (.irr t, i)
  | .node ty ind cs fs => Id.run do
    let mut j := i
    let tag := if cs.size > 1 then
        match leaves[i]? with
        | some (.fvar t) => Tag.var t
        | _ => Tag.known 0
      else Tag.known 0
    if cs.size > 1 then j := j + 1
    let mut out := #[]
    for f in fs do
      let (v, j') := ofLeaves f leaves j
      out := out.push v
      j := j'
    return (.node ty ind cs tag out none, j)

/-- The leaves of shape `s` from value `v`: known fields (placeholders for
the constructor the value does not have), fields read from a real
variable (projected, or by a `cases` for two constructors), or (where `s`
takes a value whole) the value built. -/
partial def explode (env : Env) (v : VVal) (s : Shape) : XM (Array PreStep × Array (Arg .pure) × Env) := do
  match s with
  | .irr _ => return (#[], #[], env)
  | .leaf _ =>
    let (pre, a, env) ← materialize env v
    return (pre, #[a], env)
  | .node sty ind cs sfs =>
    let placeholders (s : Shape) : Array (Arg .pure) := s.leafTypes.map fun _ => .erased
    match v with
    | .node _ ind' _ tag fs _ =>
      if ind != ind' then
        let (pre, a, env) ← materialize env v
        let (pre2, as, env) ← explode env (.real a) s
        return (pre ++ pre2, as, env)
      let known := env.tagOf? tag
      let mut pre := #[]
      let mut out := #[]
      let mut env := env
      if cs.size > 1 then
        match known, tag with
        | some c, _ =>
          let d ← tagLit c
          pre := pre.push (.let d)
          out := out.push (.fvar d.fvarId)
        | none, .var t => out := out.push (.fvar t)
        | none, .known c =>
          let d ← tagLit c
          pre := pre.push (.let d)
          out := out.push (.fvar d.fvarId)
      for h : j in [:sfs.size] do
        if let some c := known then
          if let some o := cs.owner? j then
            if o != c then
              out := out ++ placeholders sfs[j]
              continue
        let (p, as, env') ← explode env (fs[j]?.getD (.real .erased)) sfs[j]
        pre := pre ++ p
        out := out ++ as
        env := env'
      return (pre, out, env)
    | .real (.fvar x) =>
      if cs.size == 1 then
        let mut pre := #[]
        let mut out := #[]
        let mut env := env
        for h : i in [:sfs.size] do
          let sf := sfs[i]
          if sf matches .irr _ then continue
          let d ← freshLet `_flat sf.ty (.proj ind i x)
          pre := pre.push (.let d)
          let (p, as, env') ← explode env (.real (.fvar d.fvarId)) sf
          pre := pre ++ p
          out := out ++ as
          env := env'
        return (pre, out, env)
      -- Two constructors: a `cases` on `x`, each arm jumping with its
      -- leaves to a join point over the rest.
      let ps ← s.leafTypes.mapM fun t => freshParam `_flat t
      let j ← mkFreshFVarId
      let mut arms := #[]
      for h : c in [:cs.size] do
        let aps ← (cs.kids c sfs).mapM fun sf => freshParam `_flat sf.ty
        let fields := (List.range sfs.size).toArray.map fun k =>
          if (cs.owner? k).all (· == c) then VVal.real (.fvar aps[k - cs.base c]!.fvarId) else .irr sfs[k]!.ty
        let (steps, leaves, _) ← explode env (.node sty ind cs (.known c) fields (some x)) s
        arms := arms.push (cs.cs[c]!.name, aps, steps, leaves)
      return (#[.join j ps x ind arms], ps.map (.fvar ·.fvarId), env)
    | _ => return (#[], placeholders s, env)

/-- Fresh parameters for the leaves of shape `s`, and the value they make. -/
def leafParams (base : Name) (s : Shape) : XM (Array (Param .pure) × VVal) := do
  let ps ← s.leafTypes.mapM fun t => freshParam (base.appendAfter "_f") t
  return (ps, (ofLeaves s (ps.map (.fvar ·.fvarId))).1)

/-- The variable `x` built where it is used whole: steps to add first, the
variable, and the scope that remembers it. -/
def wholeVar (env : Env) (x : FVarId) : XM (Array PreStep × FVarId × Env) := do
  let v := valOf env x
  let ty := (← read).facts.types.getD x anyExpr
  let (pre, a, env) ← materialize env v
  let (pre2, y) ← asFVar a ty
  let env := match v with
    | .node t ind cs tag fs none => env.insert x (.node t ind cs tag fs (some y))
    | _ => env
  return (pre ++ pre2, y, env)

def wholeArg (env : Env) (a : Arg .pure) : XM (Array PreStep × Arg .pure × Env) := do
  match a with
  | .fvar x =>
    let (pre, y, env) ← wholeVar env x
    return (pre, .fvar y, env)
  | a => return (#[], a, env)

def wholeArgs (env : Env) (args : Array (Arg .pure)) : XM (Array PreStep × Array (Arg .pure) × Env) := do
  let mut pre := #[]
  let mut out := #[]
  let mut env := env
  for a in args do
    let (p, a', env') ← wholeArg env a
    pre := pre ++ p
    out := out.push a'
    env := env'
  return (pre, out, env)

/-- The arguments of a saturated call of a worker (or of a jump to a join
point with split parameters), whose parameters have shapes `shapes`: the
fields of the split parameters, the others whole. -/
def splitArgs (env : Env) (shapes : Array (Option Shape)) (args : Array (Arg .pure)) :
    XM (Array PreStep × Array (Arg .pure) × Env) := do
  let mut pre := #[]
  let mut out := #[]
  let mut env := env
  for h : i in [:args.size] do
    match shapes[i]?.join with
    | some s =>
      if s.isNode then
        let (p, as, env') ← explode env (argVal env args[i]) s
        pre := pre ++ p
        out := out ++ as
        env := env'
        continue
    | none => pure ()
    let (p, a, env') ← wholeArg env args[i]
    pre := pre ++ p
    out := out.push a
    env := env'
  return (pre, out, env)

/-- The shapes of `f`'s parameters (`none`: whole). -/
def paramShapes (st : AState) (f : Name) (n : Nat) : Array (Option Shape) :=
  (List.range n).toArray.map fun i => (st.slots[SlotId.param f i]?).filter (·.isNode)

/-- The worker's name of declaration `f`. -/
def workerName (f : Name) : Name := .str f "_l2r_flat"

/-- Bind the parameters `ps` of an alternative to the fields `fs` of a
known value (a field without data: a placeholder let). -/
def bindFields (env : Env) (ps : Array (Param .pure)) (fs : Array VVal) :
    XM (Array PreStep × Env) := do
  let mut pre := #[]
  let mut env := env
  for h : i in [:ps.size] do
    let p := ps[i]
    match fs[i]? with
    | some (.irr _) | none =>
      let d ← freshLet p.binderName p.type .erased
      pre := pre.push (.let d)
      env := env.insert p.fvarId (.real (.fvar d.fvarId))
    | some v => env := env.insert p.fvarId v
  return (pre, env)

/-- The call of a declaration with a worker: arguments split, and a tuple
result read into its variables. -/
def callWorker (env : Env) (d : LetDecl .pure) (f : Name) (args : Array (Arg .pure)) (k : Env → XM (Code .pure)) :
    XM (Code .pure) := do
  let ctx ← read
  let some callee := ctx.prog.decls[f]? | throwError "lean2rr: flatten: no declaration {f} (internal error)"
  let some w := ctx.workers[f]? | throwError "lean2rr: flatten: no worker of {f} (internal error)"
  let (pre, args', env) ← splitArgs env (paramShapes ctx.st f callee.params.size) args
  match ctx.st.results[f]?.filter (·.isNode) with
  | some rs =>
    let tty := tupleTyOf rs
    let t : LetDecl .pure := { fvarId := ← mkFreshFVarId, binderName := d.binderName, type := tty, value := .const w [] args' }
    let n := rs.leafTypes.size
    let mut projs := #[]
    for h : j in [:n] do
      projs := projs.push (PreStep.let (← freshLet `_flat rs.leafTypes[j]! (.proj (flatTupleName n) j t.fvarId)))
    let (v, _) := ofLeaves rs (projs.map fun | .let p => .fvar p.fvarId | _ => .erased)
    let env := env.insert d.fvarId v
    -- The tuple itself, for a `return` of the same type.
    let env := { env with tuples := env.tuples.insert d.fvarId t.fvarId }
    wrapPre (pre.push (.let t) ++ projs) (← k env)
  | none =>
    wrapPre (pre.push (.let { d with value := .const w [] args' })) (← k env)

mutual
  partial def xform (env : Env) (c : Code .pure) : XM (Code .pure) := do
    let ctx ← read
    match c with
    | .let d k =>
      match d.value with
      | .proj sn i v =>
        if let .node _ ind _ _ fs _ := valOf env v then
          if ind == sn then
            match fs[i]? with
            | some (.irr _) | none =>
              return .let { d with value := .erased } (← xform env k)
            | some fv => return ← xform (env.insert d.fvarId fv) k
        let (pre, y, env) ← wholeVar env v
        wrapPre pre (.let { d with value := .proj sn i y } (← xform env k))
      | .const g us args _ =>
        if let some cl := ctx.facts.ctorLets[d.fvarId]? then
          -- A known constructor constant stays: its fields are read from it
          -- where they are needed (`explode`).
          if cl.const then return .let d (← xform env k)
          let ind := cl.ty.consumeMData.getAppFn.constName
          let np := cl.ctors.cs[cl.cidx]!.numParams
          let mut fields := #[]
          for h : c in [:cl.ctors.size] do
            if cl.ctors.shared && c != cl.cidx then continue
            for h' : i in [:cl.ctors.cs[c]!.numFields] do
              fields := fields.push <|
                if c != cl.cidx || (cl.irrFields[i]?.getD false) then VVal.irr anyExpr
                else argVal env (args[np + i]?.getD .erased)
          if ctx.st.built.contains (ctx.facts.name, d.fvarId) then
            let (pre, args', env) ← wholeArgs env args
            let env := env.insert d.fvarId (.node cl.ty ind cl.ctors (.known cl.cidx) fields (some d.fvarId))
            return ← wrapPre pre (.let { d with value := .const g us args' } (← xform env k))
          return ← xform (env.insert d.fvarId (.node cl.ty ind cl.ctors (.known cl.cidx) fields none)) k
        if let some f := ctx.facts.calls[d.fvarId]? then
          -- Self-calls enter the worker; other declarations call a peeled
          -- one through its wrapper (`AState.peel`).
          -- (A result this declaration keeps whole: the wrapper, `wholeCalls`.)
          if ctx.workers.contains f && (f == ctx.facts.name || !ctx.st.peel.contains f) &&
              !ctx.st.wholeCalls.contains (ctx.facts.name, d.fvarId) then
            return ← callWorker env d f args (xform · k)
        let (pre, args', env) ← wholeArgs env args
        wrapPre pre (.let { d with value := .const g us args' } (← xform env k))
      | .fvar g args =>
        let (pre, g', env) ← wholeVar env g
        let (pre2, args', env) ← wholeArgs env args
        wrapPre (pre ++ pre2) (.let { d with value := .fvar g' args' } (← xform env k))
      | _ => return .let d (← xform env k)
    | .jp fd k =>
      let mut ps := #[]
      let mut envB := env
      let mut split := false
      for h : i in [:fd.params.size] do
        let p := fd.params[i]
        match ctx.st.slots[SlotId.jp ctx.facts.name fd.fvarId i]?.filter (·.isNode) with
        | some s =>
          let (lps, v) ← leafParams p.binderName s
          ps := ps ++ lps
          envB := envB.insert p.fvarId v
          split := true
        | none => ps := ps.push p
      let body ← xform envB fd.value
      let ty := if !split && ctx.result.isNone then fd.type else
        ps.foldr (fun p acc => .forallE p.binderName p.type acc .default) ctx.resTy
      return .jp (FunDecl.mk fd.fvarId fd.binderName ps ty body) (← xform env k)
    | .jmp j args =>
      let shapes := match ctx.facts.jps[j]? with
        | some ps => (List.range ps.size).toArray.map fun i =>
            (ctx.st.slots[SlotId.jp ctx.facts.name j i]?).filter (·.isNode)
        | none => #[]
      let (pre, args', _) ← splitArgs env shapes args
      wrapPre pre (.jmp j args')
    | .cases cs =>
      match valOf env cs.discr with
      | .node _ ind ctors tag fs mat =>
        if ind == cs.typeName then
          let arm (env : Env) (c : Nat) : XM (Code .pure) := do
            let some ci := ctors.cs[c]? | return .unreach ctx.resTy
            match cs.alts.find? (fun | .alt c' _ _ _ => c' == ci.name | _ => false) with
            | some (.alt _ ps k _) =>
              let (pre, env) ← bindFields env ps (ctors.kids c fs)
              wrapPre pre (← xform env k)
            | _ =>
              match cs.alts.findSome? (fun | .default k => some k | _ => none) with
              | some k => xform env k
              | none => return .unreach ctx.resTy
          let explicit := cs.alts.any fun | .alt .. => true | _ => false
          match env.tagOf? tag, tag with
          | some c, _ => return ← arm env c
          | none, .var t =>
            if !explicit then
              -- Only a default alternative: it runs whatever the tag.
              match cs.alts.findSome? (fun | .default k => some k | _ => none) with
              | some k => return ← xform env k
              | none => return .unreach ctx.resTy
            -- Built already, behind a join on its tag (`materialize`): a
            -- `cases` on the object, whose fields are the ones built there
            -- (each alternative's parameters; not built a second time).
            if let some m := mat then
              return ← xformCases env ⟨cs.typeName, cs.resultType, m, cs.alts⟩
            -- The tag decides: a `cases` on it, each arm knowing it.
            let k0 ← arm { env with tags := env.tags.insert t 0 } 0
            let k1 ← arm { env with tags := env.tags.insert t 1 } 1
            return .cases ⟨``Bool, ctx.resTy, t, #[.alt ``Bool.false #[] k0, .alt ``Bool.true #[] k1]⟩
          | none, .known c => return ← arm env c
        let (pre, y, env) ← wholeVar env cs.discr
        wrapPre pre (← xformCases env ⟨cs.typeName, cs.resultType, y, cs.alts⟩)
      | _ =>
        let (pre, y, env) ← wholeVar env cs.discr
        wrapPre pre (← xformCases env ⟨cs.typeName, cs.resultType, y, cs.alts⟩)
    | .return x =>
      match ctx.result with
      | some rs =>
        let tty := tupleTyOf rs
        -- The result of a call read from a tuple of the same type: that tuple.
        if let some t := env.tuples.get? x then
          if let some f := ctx.facts.calls[x]? then
            if ctx.st.results[f]?.any (tupleTyOf · == tty) then
              return .return t
        let (pre, leaves, _) ← explode env (valOf env x) rs
        let k := leaves.size
        let t ← freshLet `_flat tty (.const (flatTupleCtor k) [] (Array.replicate k .erased ++ leaves))
        wrapPre (pre.push (.let t)) (.return t.fvarId)
      | none =>
        let (pre, y, _) ← wholeVar env x
        wrapPre pre (.return y)
    | .unreach _ => return .unreach ctx.resTy
    | .fun .. => return c

  /-- A `cases` on a real variable: each alternative knows the matched
  value as its constructor applied to the alternative's parameters. -/
  partial def xformCases (env : Env) (cs : Cases .pure) : XM (Code .pure) := do
    let ctx ← read
    let ind := cs.typeName
    let ty := ctx.facts.types.getD cs.discr anyExpr
    let ctors? := (← indInfo? ty).bind fun (iv, k, _) => if iv.name == ind then some k else none
    let alts ← cs.alts.mapM fun
      | .alt c ps k h => do
        let mut env := env
        if let some ctors := ctors? then
          if let some ci := ctors.cs.findIdx? (·.name == c) then
            let mut fields := #[]
            for h : c' in [:ctors.size] do
              if ctors.shared && c' != ci then continue
              for h' : i in [:ctors.cs[c']!.numFields] do
                fields := fields.push <|
                  if c' == ci then (match ps[i]? with | some p => VVal.real (.fvar p.fvarId) | none => .irr anyExpr)
                  else .irr anyExpr
            env := env.insert cs.discr (.node ty ind ctors (.known ci) fields (some cs.discr))
        return .alt c ps (← xform env k) h
      | .default k => return .default (← xform env k)
      | a => return a
    return .cases ⟨cs.typeName, ctx.resTy, cs.discr, alts⟩
end

/-- The uses of the variables in `intro` in code `c` (counts). -/
partial def countUses (intro : Std.HashSet FVarId) (c : Code .pure) (m : Std.HashMap FVarId Nat) :
    Std.HashMap FVarId Nat :=
  let bump (m : Std.HashMap FVarId Nat) (x : FVarId) :=
    if intro.contains x then m.insert x (m.getD x 0 + 1) else m
  let bumpArgs (m : Std.HashMap FVarId Nat) (args : Array (Arg .pure)) :=
    args.foldl (fun m a => match a with | .fvar x => bump m x | _ => m) m
  match c with
  | .let d k =>
    let m := match d.value with
      | .proj _ _ x => bump m x
      | .const _ _ args => bumpArgs m args
      | .fvar g args => bumpArgs (bump m g) args
      | _ => m
    countUses intro k m
  | .jp fd k | .fun fd k _ => countUses intro k (countUses intro fd.value m)
  | .cases cs => cs.alts.foldl (fun m a => countUses intro a.getCode m) (bump m cs.discr)
  | .jmp _ args => bumpArgs m args
  | .return x => bump m x
  | .unreach _ => m

/-- `c` without the introduced lets (`intro`) that nothing uses (`counts`),
the counts of what they used lowered. -/
partial def dropDead (intro : Std.HashSet FVarId) (c : Code .pure) (counts : Std.HashMap FVarId Nat) :
    Code .pure × Std.HashMap FVarId Nat × Bool :=
  match c with
  | .let d k =>
    let (k, counts, ch) := dropDead intro k counts
    if intro.contains d.fvarId && counts.getD d.fvarId 0 == 0 then
      let dec (m : Std.HashMap FVarId Nat) (x : FVarId) :=
        if intro.contains x then m.insert x (m.getD x 1 - 1) else m
      let counts := match d.value with
        | .proj _ _ x => dec counts x
        | .const _ _ args => args.foldl (fun m a => match a with | .fvar x => dec m x | _ => m) counts
        | .fvar g args => args.foldl (fun m a => match a with | .fvar x => dec m x | _ => m) (dec counts g)
        | _ => counts
      (k, counts, true)
    else (.let d k, counts, ch)
  | .jp fd k =>
    let (b, counts, ch1) := dropDead intro fd.value counts
    let (k, counts, ch2) := dropDead intro k counts
    (.jp (FunDecl.mk fd.fvarId fd.binderName fd.params fd.type b) k, counts, ch1 || ch2)
  | .fun fd k h =>
    let (b, counts, ch1) := dropDead intro fd.value counts
    let (k, counts, ch2) := dropDead intro k counts
    (.fun (FunDecl.mk fd.fvarId fd.binderName fd.params fd.type b) k h, counts, ch1 || ch2)
  | .cases cs =>
    let (alts, counts, ch) := cs.alts.foldl (init := (#[], counts, false)) fun (as, counts, ch) a =>
      let (k, counts, ch') := dropDead intro a.getCode counts
      (as.push (a.updateCode k), counts, ch || ch')
    (.cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩, counts, ch)
  | c => (c, counts, false)

/-- Drop the introduced lets (`XState.introduced`) that nothing uses (in
rounds: a let dropped can leave the lets it read unused; a dropped let is
always after the lets it reads, which a later round sees). -/
partial def dropUnused (intro : Std.HashSet FVarId) (c : Code .pure) : Code .pure × Unit := Id.run do
  if intro.isEmpty then return (c, ())
  let mut counts := countUses intro c {}
  let mut c := c
  repeat
    let (c', counts', ch) := dropDead intro c counts
    c := c'
    counts := counts'
    unless ch do break
  return (c, ())

/-! ## The pass -/

/-- The declarations the pass leaves alone: no code, local functions, no
parameters (constants), lowered by special code (`IO.Process.output`), or
`excluded` (in a program that creates resources: see `resourceExcluded`). -/
def eligible (keys : NameMap InstKey) (excluded : NameSet) (d : Decl .pure) (facts : DeclFacts) : Bool :=
  d.value matches .code _ && !facts.hasFun && !d.params.isEmpty && !excluded.contains d.name &&
    ((keys.find? d.name).map (·.decl) |>.getD d.name) != ``IO.Process.output

/-- In a program that creates resources whose release is observable (files,
child processes, promises: `programMakesResources`), lean2rr emulates native Lean's
release times by running Lean's own borrow inference on its declarations
(Lower/Borrow). That inference depends on the code (a `cases` whose cell
Lean's reset/reuse would give to the worker's tuple makes the matched
parameter owned), so the pass leaves alone every declaration with a
parameter or a result that may hold such a resource (`holdsResource`):
their code, and so their inferred borrows, stay Lean's. -/
def resourceExcluded (keys : NameMap InstKey) (decls : Array (Decl .pure)) : CoreM (Bool × NameSet) := do
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : NameMap (Decl .pure))
  unless ← programMakesResources byName keys do return (false, {})
  let mut out : NameSet := {}
  for d in decls do
    unless d.value matches .code _ do continue
    let res := (splitArrows d.type d.params.size).2
    if (← d.params.anyM (holdsResource ·.type)) || (← holdsResource res) then
      out := out.insert d.name
  return (true, out)

/-- Result shape `s` (at `path` of `f`'s result) without the levels that
some declaration uses whole while no other declaration reads them field by
field (spreading them would only add the tuple's traffic to the rebuild),
or while `f` may return an existing object there (the rebuild would
allocate what `f` shares). The wrapper uses every level whole (`wrapped`:
`f` is reached through it); below a level used whole (`above`), a shared
object would be copied too. A level nobody uses whole stays as it is. -/
partial def pruneUnread (st : AState) (wrapped : Bool) (f : Name) (s : Shape) (path : List Nat)
    (above : Bool := false) : Shape :=
  match s with
  | .node t ind cs fs =>
    -- A level used whole, here or above (a rebuild builds every split
    -- level below it, which copies a shared object there).
    let here := wrapped || st.wholeUses.contains (f, path)
    let whole := here || above
    if (here && !st.benefit.contains (f, path)) || (whole && st.existing.contains (Tgt.res f, path)) then .leaf t
    else .node t ind cs (fs.mapIdx fun i sf => pruneUnread st wrapped f sf (path ++ [i]) whole)
  | s => s

/-- A non-recursive declaration's parameter shape `s` (at `path` of slot
`slot`) without the levels no caller passes known fields to (splitting them
would only move the projections to the callers). -/
partial def prunePassed (st : AState) (slot : SlotId) (s : Shape) (path : List Nat) : Shape :=
  match s with
  | .node t ind cs fs =>
    if !st.paramBenefit.contains (slot, path) then .leaf t
    else .node t ind cs (fs.mapIdx fun i sf => prunePassed st slot sf (path ++ [i]))
  | s => s

/-- The declarations some code reaches through their wrapper: referenced
other than by a saturated call (a function value, an over-application), or
called by a declaration the pass leaves alone. -/
partial def wrapperUsers (prog : Std.HashMap Name (Decl .pure)) (eligibleNames : NameSet)
    (decls : Array (Decl .pure)) : NameSet := Id.run do
  let mut out : NameSet := {}
  for d in decls do
    let .code c := d.value | continue
    out := go (eligibleNames.contains d.name) c out
  return out
where
  go (elig : Bool) (c : Code .pure) (out : NameSet) : NameSet :=
    match c with
    | .let l k =>
      let out := match l.value with
        | .const g _ args _ =>
          match prog[g]? with
          | some callee =>
            if callee.value matches .code _ && (!elig || args.size != callee.params.size) then out.insert g else out
          | none => out
        | _ => out
      go elig k out
    | .jp fd k | .fun fd k _ => go elig k (go elig fd.value out)
    | .cases cs => cs.alts.foldl (fun out a => go elig a.getCode out) out
    | _ => out

/-- The fixed point over the whole program (see the module comment). -/
def analyze (keys : NameMap InstKey) (excluded : NameSet) (resources : Bool) (decls : Array (Decl .pure))
    (prog : Program) : CoreM AState := do
  let tA0 ← IO.monoMsNow
  let cycles := callCycles decls
  let mut st : AState := {}
  -- Saturated calls of each declaration from anywhere.
  let mut called : NameSet := {}
  for d in decls do
    let some f := prog.facts[d.name]? | continue
    for (_, g) in f.calls.toList do called := called.insert g
  for d in decls do
    let some f := prog.facts[d.name]? | continue
    unless eligible keys excluded d f do continue
    -- Parameters of a declaration that calls itself (and nothing else of
    -- its call cycle).
    -- (A declaration that does not call itself: kept only where a caller
    -- passes a value whose fields are known, `prunePassed`.)
    if !f.recursive || (cycles.find? d.name).all (·.size ≤ 1) then
      for h : i in [:d.params.size] do
        let s ← maxShape d.params[i].type
        if s.isNode then st := { st with slots := st.slots.insert (.param d.name i) s }
    -- Join-point parameters (also of two constructors: a join point is
    -- internal to the declaration).
    for (j, ps) in f.jps.toList do
      for h : i in [:ps.size] do
        if resources && (← holdsResource ps[i].type) then continue
        let s ← maxShape ps[i].type (sums := true)
        if s.isNode then st := { st with slots := st.slots.insert (.jp d.name j i) s }
    -- The result.
    if called.contains d.name then
      let s ← maxShape (splitArrows d.type d.params.size).2 (sums := true)
      if let some pat := (← IO.getEnv "L2R_FLATTEN_DEBUG") then
        if (d.name.toString.splitOn pat).length > 1 then
          IO.eprintln s!"flatten: {d.name}: initial result leaves {s.leafTypes}"
      if s.isNode && s.leafTypes.size ≥ 2 && !s.leafTypes.any mentionsFn then
        st := { st with results := st.results.insert d.name s }
  -- Shrink until nothing changes, constraining again only the
  -- declarations a change concerns (`dirty`); then results are split only
  -- at the levels `pruneUnread` keeps (`benefit` and `wholeUses`, collected
  -- by one round over every declaration), and again until nothing changes.
  let elig := decls.filter fun d => (prog.facts[d.name]?.any (eligible keys excluded d ·))
  let wrapped := wrapperUsers prog.decls (elig.foldl (·.insert ·.name) {}) decls
  let mut callersOf : Std.HashMap Name (Array Name) := {}
  for d in elig do
    let some f := prog.facts[d.name]? | continue
    let gs := f.calls.fold (init := ({} : NameSet)) fun s _ g => s.insert g
    for g in gs do callersOf := callersOf.insert g ((callersOf.getD g #[]).push d.name)
  let referenced := decls.foldl (init := ({} : NameSet)) fun acc d =>
    match d.value with
    | .code c => (codeConsts c #[]).foldl (·.insert ·) acc
    | _ => acc
  st := { st with callersOf, referenced, dirty := elig.foldl (·.insert ·.name) {} }
  -- A declaration reached through its wrapper (a function value, a caller
  -- the pass leaves alone) gets whatever objects those callers pass.
  for d in elig do
    unless wrapped.contains d.name do continue
    for h : i in [:d.params.size] do
      let ps := SlotId.param d.name i
      if let some sh := st.slots[ps]? then
        for q in nodePaths sh [] do st := { st with entryExisting := st.entryExisting.insert (ps, q) }
  let round (st : AState) (todo : Array (Decl .pure)) : AState := Id.run do
    let ((), st') := (do
      for d in todo do
        if let some f := prog.facts[d.name]? then constrainDecl f prog
      : AM Unit).run st
    return st'
  let tA ← IO.monoMsNow
  let mut rounds := 0
  repeat
    while !st.dirty.isEmpty do
      let todo := elig.filter (st.dirty.contains ·.name)
      st := round { st with dirty := {} } todo
      rounds := rounds + 1
    st := round { st with benefit := {}, wholeUses := {}, paramBenefit := {}, checkSites := true } elig
    st := { st with checkSites := false }
    rounds := rounds + 1
    unless st.dirty.isEmpty do continue
    let mut cut := false
    -- Parameters of declarations that do not call themselves: split only
    -- at the levels some caller passes known fields.
    for d in elig do
      let some f := prog.facts[d.name]? | continue
      if f.recursive then continue
      for h : i in [:d.params.size] do
        let s := SlotId.param d.name i
        let some sh := st.slots[s]? | continue
        let sh' := prunePassed st s sh []
        if sh' != sh then
          st := { st with slots := st.slots.insert s sh' }
          let ((), st') := (dirtyCallers d.name).run st
          st := st'
          cut := true
    for (f, rs) in st.results.toList do
      let rs' := pruneUnread st (wrapped.contains f || st.peel.contains f) f rs []
      if rs' != rs then
        st := { st with results := st.results.insert f rs' }
        let ((), st') := (dirtyCallers f).run st
        st := st'
        cut := true
    unless cut do break
  st := { st with results := st.results.filter fun _ s => s.isNode && s.leafTypes.size ≥ 2,
                  slots := st.slots.filter fun _ s => s.isNode }
  -- A loop peeled while its parameter was split, whose parameters ended up
  -- whole: no first step to keep in the wrapper.
  st := { st with peel := st.peel.filter fun f =>
    (prog.decls[f]?.map (·.params.size)).any fun n => (List.range n).any (st.slots.contains <| .param f ·) }
  if (← IO.getEnv "L2R_FLATTEN_TIME").isSome then
    IO.eprintln s!"flatten: candidates {tA - tA0} ms, {rounds} rounds {(← IO.monoMsNow) - tA} ms"
  -- `L2R_FLATTEN_DEBUG=NAME`: the decisions about declarations whose name
  -- contains NAME, on stderr.
  if let some pat := (← IO.getEnv "L2R_FLATTEN_DEBUG") then
    let hit (n : Name) := (n.toString.splitOn pat).length > 1
    for d in decls do
      if hit d.name then
        IO.eprintln s!"flatten: {d.name}: result {(st.results[d.name]?.map (·.leafTypes.size))} peel {st.peel.contains d.name}"
        for (f, p) in st.benefit.toList do
          if f == d.name then IO.eprintln s!"  benefit {p}"
        for (f, p) in st.wholeUses.toList do
          if f == d.name then IO.eprintln s!"  whole use {p}"
        for (t, p) in st.existing.toList do
          if t == .res d.name then IO.eprintln s!"  existing {p}"
        for (c, x) in st.wholeCalls.toList do
          if c == d.name then
            IO.eprintln s!"  keeps whole the result of {(prog.facts[c]?.bind (·.calls[x]?))} (sites {st.wholeCallSites[(c, x)]?}, call depth {(prog.facts[c]?.bind (·.callDepth[x]?))})"
          else if (prog.facts[c]?.bind (·.calls[x]?)) == some d.name then
            IO.eprintln s!"  result kept whole by {c}"
        for h : i in [:d.params.size] do
          if let some sh := st.slots[SlotId.param d.name i]? then
            IO.eprintln s!"  param {i}: {sh.leafTypes.size} leaves"
          for (s, p) in st.entryExisting.toList do
            if s == SlotId.param d.name i then IO.eprintln s!"  param {i}: existing from a caller {p}"
  return st

/-- The pass over the program. -/
def run (keys : NameMap InstKey) (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let timing := (← IO.getEnv "L2R_FLATTEN_TIME").isSome
  let t0 ← IO.monoMsNow
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : Std.HashMap Name (Decl .pure))
  -- The instances of `ptrAddrUnsafe`, `dbgTraceIfShared` and
  -- `isExclusiveUnsafe` (`Use.pinned`: they look at the object itself, its
  -- address or whether it is shared).
  let env ← getEnv
  let pinning := decls.foldl (init := ({} : NameSet)) fun s d =>
    let orig := (keys.find? d.name).map (·.decl) |>.getD d.name
    if ["lean_ptr_addr", "lean_dbg_trace_if_shared", "lean_is_exclusive_obj"].any
        (getExternNameFor env `c orig == some ·) then s.insert d.name else s
  let mut facts : Std.HashMap Name DeclFacts := {}
  for d in decls do
    facts := facts.insert d.name (← collectDecl byName pinning d)
  let prog : Program := { decls := byName, facts }
  let t1 ← IO.monoMsNow
  let (resources, excluded) ← resourceExcluded keys decls
  let st ← analyze keys excluded resources decls prog
  let t2 ← IO.monoMsNow
  -- Workers.
  let mut workers : Std.HashMap Name Name := {}
  for d in decls do
    let some f := facts[d.name]? | continue
    unless eligible keys excluded d f do continue
    let w := st.results.contains d.name ||
      (List.range d.params.size).any fun i => st.slots.contains (.param d.name i)
    if w then workers := workers.insert d.name (workerName d.name)
  -- Tuples of every arity a result needs.
  for (_, s) in st.results.toList do ensureTuple s.leafTypes.size
  let jpSlotDecls := st.slots.fold (init := ({} : NameSet)) fun acc s _ =>
    match s with | .jp n .. => acc.insert n | _ => acc
  let mut out := #[]
  for d in decls do
    let some f := facts[d.name]? | out := out.push d; continue
    let .code body := d.value | out := out.push d; continue
    if !eligible keys excluded d f then
      out := out.push d; continue
    let touched := workers.contains d.name ||
      jpSlotDecls.contains d.name ||
      f.calls.toList.any (fun (_, g) => workers.contains g) ||
      f.ctorLets.toList.any (fun (x, cl) => cl.alias.isNone && !cl.const && !st.built.contains (d.name, x))
    unless touched do out := out.push d; continue
    let result := st.results[d.name]?
    let origRes := (splitArrows d.type d.params.size).2
    let resTy := match result with | some rs => tupleTyOf rs | none => origRes
    let ctx : XCtx := { facts := f, st, prog, result, resTy, workers }
    -- The worker's (or the declaration's own) parameters.
    let mut params := #[]
    let mut env : Env := {}
    for h : i in [:d.params.size] do
      let p := d.params[i]
      match st.slots[SlotId.param d.name i]? with
      | some s =>
        let ((lps, v), _) ← ((leafParams p.binderName s).run ctx).run {}
        params := params ++ lps
        env := env.insert p.fvarId v
      | none => params := params.push p
    let (body', xs) ← ((xform env body).run ctx).run {}
    let (body', _) := dropUnused xs.introduced body'
    let ty := params.foldr (fun p acc => .forallE p.binderName p.type acc .default) resTy
    match workers[d.name]? with
    | some w =>
      out := out.push { d with name := w, params, type := ty, value := .code body', inlineAttr? := none }
      let wctx : XCtx := { ctx with result := none, resTy := origRes }
      if st.peel.contains d.name then
        -- The wrapper runs the first step: the body with the parameters
        -- whole, its self-calls entering the worker (`allowedWhole`); its
        -- binders made fresh (it is a copy of the worker's).
        let (pbody, pxs) ← ((xform {} body).run wctx).run {}
        let (pbody, _) := dropUnused pxs.introduced pbody
        let wrapper ← CompilerM.run (phase := .mono) ({ d with value := .code pbody } : Decl .pure).internalize
        out := out.push wrapper
        continue
      -- The wrapper: the original signature, projections, the call, the
      -- result rebuilt.
      let wps ← d.params.mapM fun p => return { p with fvarId := ← mkFreshFVarId }
      let wbody ← (do
        let (pre, args', _) ← splitArgs {} (paramShapes st d.name d.params.size) (wps.map (.fvar ·.fvarId))
        match result with
        | some rs =>
          let tty := tupleTyOf rs
          let t ← freshLet `_flat tty (.const w [] args')
          let k := rs.leafTypes.size
          let mut projs := #[]
          for h : j in [:k] do
            projs := projs.push (← freshLet `_flat rs.leafTypes[j]! (.proj (flatTupleName k) j t.fvarId))
          let (v, _) := ofLeaves rs (projs.map (.fvar ·.fvarId))
          let (pre2, a, _) ← materialize {} v
          let (pre3, y) ← asFVar a origRes
          wrapPre (pre.push (.let t) ++ projs.map .let ++ pre2 ++ pre3) (.return y)
        | none =>
          let r ← freshLet `_flat origRes (.const w [] args')
          wrapPre (pre.push (.let r)) (.return r.fvarId)
        : XM (Code .pure)).run wctx |>.run {}
      out := out.push { d with params := wps, value := .code wbody.1 }
    | none =>
      out := out.push { d with params, type := ty, value := .code body' }
  if timing then
    IO.eprintln s!"flatten: {decls.size} declarations: collect {t1 - t0} ms, analysis {t2 - t1} ms, rewrite {(← IO.monoMsNow) - t2} ms"
  return out

end Flatten

/-- Registry entry point. -/
def Flatten.install (c : PassConfig) : PassConfig :=
  { c with monoPassesCore := c.monoPassesCore.push Flatten.run }

end LeanToReussir.Opt
