import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Util.SCC
import LeanToReussir.RR

/-!
# Outlining deep and long function bodies

rrc's per-function analyses grow faster than linearly in two shapes of
code that Lean programs produce routinely (reussir-bugs/, issues 16
and 17, costs):
- nesting: every IO bind is a `match` on the action's result whose `ok` arm
  holds the rest of the function, so a `main` of N statements nests N
  matches deep (a 3000-arm literal match nests 3000 `if`s), and reuse across
  calls costs about depth^2.6;
- length: a straight-line body of N `let`s on `Nat` costs memory in N^2.

Reussir has no early return that would let the error checks be flat, so
lean2rr bounds both on its side, after lowering. A tail path of a function
goes through the arms of a `match` or the branches of an `if` that is the
function's result, recursively, and through the rest of a block after a
`let`. A function is cut when a tail path is `triggerDepth` levels deep or
`triggerLets` `let`s long, or when the value of one of its `let`s is that
deep or long. Ordinary code is below the triggers and comes out unchanged.
In a function that is cut:
- once a tail path is `maxDepth` levels deep or `maxLets` `let`s long, the
  rest of the path becomes a new function of the variables it uses, called
  in tail position (its result is the function's result);
- a `let` whose value is `maxDepth` levels deep or `maxLets` `let`s long
  gets its value from a new function of the variables the value uses (the
  value then is that function's body, cut in turn).

A recursive function (one that can reach itself through the program's
calls) keeps its loops: its tail calls to the functions of its cycle stay in
it. A rest of a tail path that holds such a call (`g(…)` as the path's
result, or `let x = g(…); x`) is outlined as a function that *returns* what
to do: a value of a generated enum `L2RStep_k` with a variant `done(v)` for
a result `v` and one per function `g` of the cycle with `g`'s parameters,
for a call `g(…)` in tail position. The cut point becomes
`match part(…) { done(v) => v, c0(a, b) => g(a, b), … }`: the part runs and
returns, and the tail call is made by the function itself, so a loop that
LLVM turns into a jump stays one (a cycle of tail calls through the parts
would not always be a sibling call and would use stack per iteration). A
step value is a `[value]` enum, so it needs no heap cell, when its layout
is safe to move (`stepItem`); otherwise it is shared, a heap cell per
iteration, only in functions this long. A step value goes only from a
part's result to the match at the cut point (through the chain of parts
that return it): it is never stored in a field, an array, a `Cell` or a
`Box`, and no conversion exists for it (this pass runs after lowering).

A block is outlined only if every variable it uses has a known type: the
parameters, typed `let`s and the fields of matched variants (from the type
declarations). Otherwise it stays where it is.

This is part of the core translation, run over the generated functions
before the optional passes on them (which then see bounded functions): it
does not make the program faster, but without it rrc's build time and
memory grow superlinearly on long `main`s and big literal matches, and so do
the `.rr` text, whose indentation follows the nesting (a 3000-arm literal
match: 126 MB instead of 1 MB), and lean2rr's own passes over it.
-/

namespace LeanToReussir.Outline
open RR

/-- Bounds on a tail path or a `let` value (see the module comment). -/
structure Limits where
  /-- A function is cut only if a tail path or a `let` value is this deep… -/
  triggerDepth : Nat := 32
  /-- …or has this many `let`s. -/
  triggerLets : Nat := 256
  /-- Then it is cut into parts of at most this depth… -/
  maxDepth : Nat := 8
  /-- …and this many `let`s on a path. -/
  maxLets : Nat := 64
  /-- A rest of a block shorter than this, with no nested `match`/`if`, is
  left in place. -/
  minRest : Nat := 16

/-- Identifier tokens of an atom's text (`x == k`, `i + one`): atoms can
mention variables. -/
def atomIdents (t : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for c in t.toList do
    if c.isAlphanum || c == '_' then cur := cur.push c
    else
      if !cur.isEmpty then out := out.push cur
      cur := ""
  if !cur.isEmpty then out := out.push cur
  return out.filter fun s => !(s.front.isDigit)

/-- Free variables, in order of first use. -/
structure Fvs where
  order : Array String := #[]
  seen : Std.HashSet String := {}
  /-- Names used as variables (`.var`), as opposed to atom tokens. -/
  vars : Std.HashSet String := {}

def Fvs.add (f : Fvs) (n : String) (isVar : Bool) : Fvs :=
  let f := if isVar then { f with vars := f.vars.insert n } else f
  if f.seen.contains n then f else { f with order := f.order.push n, seen := f.seen.insert n }

mutual
  partial def exprFvs (bound : Std.HashSet String) (e : Expr) (acc : Fvs) : Fvs :=
    match e with
    | .var n =>
      -- `.var` also carries other verbatim operands (`L2RUnit::u{}`).
      if !n.all (fun c => c.isAlphanum || c == '_') then
        (atomIdents n).foldl (fun a n => if bound.contains n then a else a.add n false) acc
      else if bound.contains n then acc else acc.add n true
    | .atom t => (atomIdents t).foldl (fun a n => if bound.contains n then a else a.add n false) acc
    | .call _ _ args => args.foldl (fun a x => exprFvs bound x a) acc
    | .apply f x => exprFvs bound x (exprFvs bound f acc)
    | .ctor _ _ args => args.foldl (fun a x => exprFvs bound x a) acc
    | .field x _ => exprFvs bound x acc
    | .cast x _ => exprFvs bound x acc
    | .lam p _ b => blockFvs (bound.insert p) b acc
    | .ite c t f => blockFvs bound f (blockFvs bound t (exprFvs bound c acc))
    | .mtch s arms => arms.foldl (init := exprFvs bound s acc) fun a arm =>
        blockFvs (arm.binders.foldl (fun bs b => match b with | some n => bs.insert n | none => bs) bound) arm.body a
    | .block b => blockFvs bound b acc
  partial def blockFvs (bound : Std.HashSet String) (b : Block) (acc : Fvs) : Fvs := Id.run do
    let mut bound := bound
    let mut acc := acc
    for (x, _, e) in b.lets do
      acc := exprFvs bound e acc
      bound := bound.insert x
    return exprFvs bound b.result acc
end

/-- The variables in scope at a point of a function: name ↦ (type if
known, binding index). -/
abbrev Env := Std.HashMap String (Option Ty × Nat)

def Env.bind (env : Env) (x : String) (t : Option Ty) : Env := env.insert x (t, env.size)

/-! ## Step values: their layout

A step enum is `[value]` (returned in registers or the caller's frame, no
heap cell) when Reussir moves its values without losing bytes. Reussir moves
a `[value]` enum as the LLVM struct of one arm, its *representative*: the
last arm with the largest alignment. Another arm's bytes survive the move
only where the representative's own type carries every byte: an integer or
a pointer does; a `bool` (an `i1`, one bit of its byte) does not (Reussir
issue 1, reussir-bugs/01-value-enum-payload.md; patch 01-a makes every move
carry all bytes, but lean2rr's output also stays right without it).
Floating-point values and padding are conservatively not counted as carried
(Reussir lays a record's padding out as bytes, Opt/FieldOrder; the guard
relies neither on that nor on how a move copies a floating-point value). So
`stepItem` makes the enum `[value]` only when the layout model below knows
every field type, and every other arm's bytes lie in the prefix of the
representative that it carries; otherwise the enum stays shared, as
before. The model follows Reussir's layout of a record's members in
declaration order (the driver always passes `--no-pack-record-members`):
each member at the next multiple of its alignment. -/

/-- A field type's storage in a step arm, as far as the guard needs it:
size and alignment in bytes, and the length of the prefix of its bytes that
a move of a value of this type carries for sure (`carried = size`: all). -/
structure FieldLayout where
  size : Nat
  align : Nat
  carried : Nat
  deriving Inhabited, Repr

/-- The generated and prelude type declarations by name (`.enum` and
`.struct` items), for `fieldLayout`. -/
abbrev TypeTable := Std.HashMap String Item

def typeTable (items : Array Item) : TypeTable :=
  items.foldl (init := {}) fun m it => match it with
    | .enum n .. | .struct n .. => m.insert n it
    | _ => m

/-- The members `fs` laid out in order, each at the next multiple of its
alignment: (alignment, end of the last member, carried prefix). -/
def compoundLayout (fs : Array FieldLayout) : Nat × Nat × Nat := Id.run do
  let mut off := 0
  let mut align := 1
  let mut carried := 0
  let mut open_ := true
  for f in fs do
    let o := (off + f.align - 1) / f.align * f.align
    if open_ then
      if o == carried then
        carried := o + f.carried
        open_ := f.carried == f.size
      else open_ := false
    off := o + f.size
    align := max align f.align
  return (align, off, carried)

/-- The storage of a value of type `t` in a step arm, or `none` if the
model does not know it (the step enum then stays shared). Pointer-sized,
all bytes carried: what Reussir stores as a pointer or one tagged word (a
shared record or enum, a function value, a closure, an opaque runtime type:
`rrAlign8` in LowerBase lists them). A `[value]` struct is its fields in
order; a `[value]` enumeration without fields, such as `L2RUnit`, is its
tag (8 bits up to 256 variants, then 16, then 32: Reussir's `getTagType`). A
`[value]` enum with fields (a step enum) is unknown. -/
partial def fieldLayout (types : TypeTable) (t : Ty) (fuel : Nat := 8) : Option FieldLayout :=
  let word : FieldLayout := ⟨8, 8, 8⟩
  match t with
  | .named n =>
    match n with
    | "u8" | "i8" => some ⟨1, 1, 1⟩
    | "u16" | "i16" => some ⟨2, 2, 2⟩
    | "u32" | "i32" => some ⟨4, 4, 4⟩
    | "u64" | "i64" => some word
    | "bool" => some ⟨1, 1, 0⟩
    | "f32" => some ⟨4, 4, 0⟩
    | "f64" => some ⟨8, 8, 0⟩
    | "Nat" | "Int" | "LStr" | "LHandle" | "LAny" => some word
    | "L2RUnit" => some ⟨1, 1, 1⟩
    | _ =>
      match types[n]? with
      | some (.enum _ false _) | some (.struct _ false _) => some word
      | some (.enum _ true vs) =>
        if !vs.all (·.2.isEmpty) then none
        else if vs.size ≤ 256 then some ⟨1, 1, 1⟩
        else if vs.size ≤ 65536 then some ⟨2, 2, 2⟩
        else some ⟨4, 4, 4⟩
      | some (.struct _ true fs) =>
        if fuel == 0 then none else do
        let ls ← fs.mapM (fieldLayout types · (fuel - 1))
        let (align, dataEnd, carried) := compoundLayout ls
        let size := (dataEnd + align - 1) / align * align
        some ⟨size, align, carried⟩
      | _ => none
  | .app n _ => if n ∈ ["RVec", "LRef", "LCell", "Cell"] then some word else none
  | .fn .. | .cls .. => some word

/-- The order of a step variant's fields (indices into the callee's
parameters `ps`): decreasing alignment, the fields that carry all their
bytes first, ties in parameter order. So the variant has no padding between
fields (like a record with optimization `field-order`, and the order of
fields that Reussir issue 2's workaround needs), and its carried prefix is
as long as it can be. Parameter order if a type is unknown. -/
def stepFieldOrder (types : TypeTable) (ps : Array Ty) : Array Nat :=
  match ps.mapM (fieldLayout types ·) with
  | none => (List.range ps.size).toArray
  | some ls =>
    (List.range ps.size).toArray.qsort fun i j =>
      let a := ls[i]!
      let b := ls[j]!
      let fa := a.carried == a.size
      let fb := b.carried == b.size
      a.align > b.align || (a.align == b.align && ((fa && !fb) || (fa == fb && i < j)))

/-- A function of the cycle that a part calls in tail position: its step
variant `c<k>` holds its arguments. -/
structure StepCall where
  fn : String
  /-- Its parameter types. -/
  params : Array Ty
  /-- The variant's fields: `params[order[0]]`, `params[order[1]]`, …
  (`stepFieldOrder`). -/
  order : Array Nat
  deriving Inhabited

/-- What a recursive function's parts return (see the module comment). -/
structure StepInfo where
  /-- The generated enum. -/
  name : String
  /-- The function's result type (variant `done`). -/
  ret : Ty
  /-- The functions of the cycle called in tail position by a part, in the
  order of their variants `c0`, `c1`, …. -/
  calls : Array StepCall := #[]
  deriving Inhabited

/-- The item of step enum `info`: `[value]` when its layout is safe to move
(see "Step values: their layout"), with its representative, the arm with
the largest alignment and of those the longest carried prefix, declared
last; otherwise shared, with its variants in order. -/
def stepItem (types : TypeTable) (info : StepInfo) : Item := Id.run do
  let arms : Array (String × Array Ty) := #[("done", #[info.ret])] ++
    info.calls.mapIdx fun i c => (s!"c{i}", c.order.map (c.params[·]!))
  let shared := Item.enum info.name false arms
  let some lays := arms.mapM (fun (_, fs) => fs.mapM (fieldLayout types ·)) | return shared
  let shapes := lays.map compoundLayout
  -- The representative: largest alignment, then longest carried prefix,
  -- then the last.
  let mut r := 0
  for h : i in [1:shapes.size] do
    let (a, _, c) := shapes[i]
    let (ar, _, cr) := shapes[r]!
    if a > ar || (a == ar && c ≥ cr) then r := i
  let (_, _, carried) := shapes[r]!
  for h : i in [:shapes.size] do
    let (_, dataEnd, _) := shapes[i]
    if i != r && dataEnd > carried then return shared
  return .enum info.name true ((arms.eraseIdx! r).push arms[r]!)

/-- The function being cut and its cycle. -/
structure FnCtx where
  /-- The original function's name (parts are named after it). -/
  base : String
  /-- The functions of its cycle (empty for a function that is not
  recursive). -/
  cycle : Std.HashSet String := {}
  /-- Its result type. -/
  ret : Ty
  /-- The functions of its cycle it calls in tail position. -/
  tailCalls : Array String := #[]

structure Ctx where
  limits : Limits
  /-- Field types of each variant: (type name, variant) ↦ fields. -/
  variants : Std.HashMap (String × String) (Array Ty)
  /-- Parameter types of every function of the program. -/
  params : Std.HashMap String (Array Ty)
  /-- The type declarations, for the layout of step variants. -/
  types : TypeTable := {}

structure St where
  /-- Function names in use. -/
  taken : Std.HashSet String
  /-- The outlined functions. -/
  out : Array Item := #[]
  /-- Step enums, per original function (see `StepInfo`). -/
  steps : Std.HashMap String StepInfo := {}
  /-- The original functions in the order their step enums were made. -/
  stepOrder : Array String := #[]
  counter : Nat := 0

abbrev M := ReaderT Ctx (StateM St)

/-- The depth (nested `match`/`if`) and the number of `let`s of the deepest
and longest paths of a block, counting the paths into `let` values as well
as the tail paths (a `let` value's path does not continue the block's). -/
partial def extent (b : Block) : Nat × Nat :=
  let (d, l) := exprExtent b.result
  b.lets.foldl (init := (d, l + b.lets.size)) fun (d, l) (_, _, e) =>
    let (d', l') := exprExtent e
    (max d d', max l l')
where
  exprExtent : Expr → Nat × Nat
    | .mtch _ arms => arms.foldl (init := (0, 0)) fun (d, l) arm =>
        let (d', l') := extent arm.body
        (max d (d' + 1), max l l')
    | .ite _ t f =>
        let (d1, l1) := extent t
        let (d2, l2) := extent f
        (max d1 d2 + 1, max l1 l2)
    | .block b' => extent b'
    | _ => (0, 0)

/-- Whether a tail block goes on: it nests a `match`/`if`, or has at least
`minRest` `let`s. -/
partial def heavy (minRest : Nat) (b : Block) : Bool :=
  b.lets.size ≥ minRest || match b.result with
    | .mtch .. | .ite .. => true
    | .block b' => heavy (minRest - b.lets.size) b'
    | _ => false

/-- A new function name: the original function's, with a part number. -/
def freshName (base : String) : M String := do
  let mut k := 0
  repeat
    let n := s!"{base}_l2rpart{k}"
    unless (← get).taken.contains n do
      modify fun s => { s with taken := s.taken.insert n }
      return n
    k := k + 1
  return base

/-- A fresh local name for the variables of a cut point. -/
def freshLocal (pre : String) : M String := do
  let k := (← get).counter
  modify fun s => { s with counter := k + 1 }
  return s!"{pre}{k}"

/-- The call of a function of the cycle that a tail expression is, if it
is one: `g(…)`, or `{ …; let x = g(…); x }` (the block's other `let`s are
returned too). -/
def cycleCall? (cycle : Std.HashSet String) (b : Block) : Option (Array (String × Option Ty × Expr) × String × Array Expr) :=
  match b.result with
  | .call g #[] args => if cycle.contains g then some (b.lets, g, args) else none
  | .var x =>
    match b.lets.back? with
    | some (y, _, .call g #[] args) =>
      if y == x && cycle.contains g then some (b.lets.pop, g, args) else none
    | _ => none
  | _ => none

/-- Whether a tail block holds a call of a function of `cycle` in tail
position. -/
partial def hasCycleCall (cycle : Std.HashSet String) (b : Block) : Bool :=
  if (cycleCall? cycle b).isSome then true else
  match b.result with
  | .mtch _ arms => arms.any fun a => hasCycleCall cycle a.body
  | .ite _ t f => hasCycleCall cycle t || hasCycleCall cycle f
  | .block b' => hasCycleCall cycle b'
  | _ => false

/-- The functions of `cycle` called in tail position in tail block `b`, in
order of first call. -/
partial def tailCycleCalls (cycle : Std.HashSet String) (b : Block) (acc : Array String) : Array String :=
  match cycleCall? cycle b with
  | some (_, g, _) => if acc.contains g then acc else acc.push g
  | none =>
    match b.result with
    | .mtch _ arms => arms.foldl (fun acc a => tailCycleCalls cycle a.body acc) acc
    | .ite _ t f => tailCycleCalls cycle f (tailCycleCalls cycle t acc)
    | .block b' => tailCycleCalls cycle b' acc
    | _ => acc

/-- The variant of step enum `info` for a tail call of `g`, adding it if
needed. -/
def stepVariant (fc : FnCtx) (g : String) : M (String × Array Nat) := do
  let info := (← get).steps[fc.base]!
  match info.calls.findIdx? (·.fn == g) with
  | some i => return (s!"c{i}", info.calls[i]!.order)
  | none =>
    let ps := (← read).params.getD g #[]
    let order := stepFieldOrder (← read).types ps
    modify fun s => { s with steps := s.steps.insert fc.base { info with calls := info.calls.push { fn := g, params := ps, order } } }
    return (s!"c{info.calls.size}", order)

/-- The step enum of the function being cut, made on first use, with a
variant for every function of its cycle that it calls in tail position
(`FnCtx.tailCalls`), so that every cut point matches all of them. -/
def stepInfo (fc : FnCtx) : M StepInfo := do
  if let some i := (← get).steps[fc.base]? then return i
  let k := (← get).stepOrder.size
  let ps := (← read).params
  let types := (← read).types
  let info : StepInfo := { name := s!"L2RStep_{k}", ret := fc.ret,
                           calls := fc.tailCalls.map fun g =>
                             let gps := ps.getD g #[]
                             { fn := g, params := gps, order := stepFieldOrder types gps } }
  modify fun s => { s with steps := s.steps.insert fc.base info, stepOrder := s.stepOrder.push fc.base }
  return info

/-- Tail block `b` as a part of a recursive function: each tail call of a
function of the cycle becomes its step variant, every other result
`done(result)`. -/
partial def stepify (fc : FnCtx) (b : Block) : M Block := do
  let info ← stepInfo fc
  if let some (lets, g, args) := cycleCall? fc.cycle b then
    let (v, order) ← stepVariant fc g
    -- (A call of a function of the program passes all its parameters.)
    let fields := if order.size == args.size then order.map (args[·]!) else args
    return ⟨lets, .ctor info.name (some v) fields⟩
  match b.result with
  | .mtch s arms => return ⟨b.lets, .mtch s (← arms.mapM fun a => do return { a with body := ← stepify fc a.body })⟩
  | .ite c t f => return ⟨b.lets, .ite c (← stepify fc t) (← stepify fc f)⟩
  | .block b' => return ⟨b.lets, .block (← stepify fc b')⟩
  | e => return ⟨b.lets, .ctor info.name (some "done") #[e]⟩

/-- The parameters for outlining `b` (its free variables, in binding
order), or `none` if one of them has no known type. -/
def partParams (env : Env) (b : Block) : Option (Array (String × Ty)) := Id.run do
  let fv := blockFvs {} b {}
  let mut params : Array (String × Ty × Nat) := #[]
  for n in fv.order do
    match env[n]? with
    | some (some t, k) => params := params.push (n, t, k)
    | some (none, _) => return none
    | none => if fv.vars.contains n then return none
  return some ((params.qsort fun a b => a.2.2 < b.2.2).map fun (n, t, _) => (n, t))

mutual
  /-- Process a tail block of a function of result type `ret` (the
  function being cut: `fc`) at `depth` levels and `lets` lets from the
  function's start. `stepped`: the block is (part of) a part that returns
  steps, so no further step conversion is needed. -/
  partial def walkBlock (fc : FnCtx) (ret : Ty) (stepped : Bool) (env : Env) (depth lets : Nat) (b : Block) :
      M Block := do
    let lim := (← read).limits
    let mut env := env
    let mut newLets := #[]
    for h : i in [:b.lets.size] do
      let (x, t, e) := b.lets[i]
      newLets := newLets.push (x, t, ← walkValue fc env t e)
      env := env.bind x t
    -- Once the path is `maxLets` long, the rest of the block is cut, into a
    -- chain of parts of `maxLets` lets each when it is longer.
    let i0 := if lim.maxLets > lets then lim.maxLets - lets else 1
    if i0 < b.lets.size then
      let restLets := b.lets.size - i0
      let resultHeavy := match b.result with
        | .mtch .. | .ite .. => true
        | .block b' => heavy (lim.minRest - restLets) b'
        | _ => false
      if restLets ≥ lim.minRest || resultHeavy then
        if let some blk ← cutLong fc ret stepped env newLets i0 b.result then
          return blk
    let lets := lets + b.lets.size
    let result ← match b.result with
      | .mtch s arms =>
        let vs := (← read).variants
        let arms ← arms.mapM fun arm => do
          let fields := match arm.ctor with
            | some c => vs.getD (arm.ty, c) #[]
            | none => #[]
          let env' := arm.binders.zipIdx.foldl (init := env) fun e (bnd, j) => match bnd with
            | some n => e.bind n fields[j]?
            | none => e
          return { arm with body := ← walkTail fc ret stepped env' (depth + 1) lets arm.body }
        pure (Expr.mtch s arms)
      | .ite c t f =>
        pure (.ite c (← walkTail fc ret stepped env (depth + 1) lets t) (← walkTail fc ret stepped env (depth + 1) lets f))
      | .block b' => pure (.block (← walkBlock fc ret stepped env depth lets b'))
      | e => pure e
    return ⟨newLets, result⟩

  /-- A tail block one level deeper: outlined once the path is too deep. -/
  partial def walkTail (fc : FnCtx) (ret : Ty) (stepped : Bool) (env : Env) (depth lets : Nat) (b : Block) :
      M Block := do
    let lim := (← read).limits
    if depth ≥ lim.maxDepth && heavy lim.minRest b then
      if let some call ← outlineTail fc ret stepped env b then
        return .ofExpr call
    walkBlock fc ret stepped env depth lets b

  /-- The value `e` of a `let` of type `t`: from a new function when it is
  too deep or long and its type is known. -/
  partial def walkValue (fc : FnCtx) (env : Env) (t : Option Ty) (e : Expr) : M Expr := do
    let lim := (← read).limits
    let some ty := t | return e
    let body : Block := match e with
      | .block b => b
      | _ => .ofExpr e
    unless e matches .mtch .. | .ite .. | .block .. do return e
    let (d, l) := extent body
    if d < lim.maxDepth && l < lim.maxLets then return e
    let some ps := partParams env body | return e
    let name ← freshName fc.base
    let env' : Env := ps.foldl (fun e (n, t) => e.bind n (some t)) {}
    -- A value holds no tail call of the function's cycle: a plain part.
    let body ← walkBlock { fc with cycle := {}, ret := ty } ty false env' 0 0 body
    modify fun s => { s with out := s.out.push (.fn name ps ty body) }
    return .call name #[] (ps.map fun (n, _) => .var n)

  /-- Make the rest of a tail path `b` a new function of the variables it
  uses and return what replaces it, or `none` if one of them has no known
  type. In a recursive function, a rest that holds a tail call of the
  function's cycle becomes a part returning steps (see the module
  comment). -/
  partial def outlineTail (fc : FnCtx) (ret : Ty) (stepped : Bool) (env : Env) (b : Block) : M (Option Expr) := do
    let some ps := partParams env b | return none
    let name ← freshName fc.base
    let env' : Env := ps.foldl (fun e (n, t) => e.bind n (some t)) {}
    let args := ps.map fun (n, _) => Expr.var n
    if stepped || !hasCycleCall fc.cycle b then
      let body ← walkBlock fc ret stepped env' 0 0 b
      modify fun s => { s with out := s.out.push (.fn name ps ret body) }
      return some (.call name #[] args)
    -- The rest returns a step; the cut point makes the tail call.
    let b ← stepify fc b
    let stepTy := Ty.named (← stepInfo fc).name
    let body ← walkBlock fc stepTy true env' 0 0 b
    modify fun s => { s with out := s.out.push (.fn name ps stepTy body) }
    return some (← stepDispatch fc (.call name #[] args))

  /-- Cut the `let`s of a block from position `i0` on (`lets`, already
  processed, then `result`) into a chain of parts of `maxLets` lets, each
  calling the next in tail position, the last ending with `result` (cut in
  turn); the block becomes its first `i0` lets and the call of the first
  part. In one pass from the end, so that a block of `n` lets (a spliced
  literal) costs time linear in `n`. `none` if some part would need a
  variable of unknown type. -/
  partial def cutLong (fc : FnCtx) (ret : Ty) (stepped : Bool) (env : Env) (lets : Array (String × Option Ty × Expr))
      (i0 : Nat) (result : Expr) : M (Option Block) := do
    let lim := (← read).limits
    let n := lets.size
    let mut starts := #[i0]
    while starts.back! + lim.maxLets < n do starts := starts.push (starts.back! + lim.maxLets)
    let last : Block := ⟨lets.extract starts.back! n, result⟩
    -- A rest that holds a tail call of the function's cycle returns steps.
    let step := !stepped && hasCycleCall fc.cycle last
    let partRet ← if step then do pure (Ty.named (← stepInfo fc).name) else pure ret
    -- Every variable bound before a part (names are unique in a function).
    let envAll := lets.foldl (fun e (x, t, _) => e.bind x t) env
    let some ps := partParams envAll last | return none
    let name ← freshName fc.base
    let lastBody ← if step then stepify fc last else pure last
    let env' : Env := ps.foldl (fun e (x, t) => e.bind x (some t)) {}
    let body ← walkBlock fc partRet (stepped || step) env' 0 0 lastBody
    let mut parts : Array Item := #[.fn name ps partRet body]
    let mut next : Expr := .call name #[] (ps.map fun (x, _) => .var x)
    for k' in [:starts.size - 1] do
      let k := starts.size - 2 - k'
      let blk : Block := ⟨lets.extract starts[k]! starts[k + 1]!, next⟩
      let some ps := partParams envAll blk | return none
      let name ← freshName fc.base
      parts := parts.push (.fn name ps partRet blk)
      next := .call name #[] (ps.map fun (x, _) => .var x)
    modify fun s => { s with out := s.out ++ parts }
    let call ← if step then stepDispatch fc next else pure next
    return some ⟨lets.extract 0 i0, call⟩

  /-- At a cut point of a recursive function: the step `call` returns,
  matched; a tail call of the cycle is made here. -/
  partial def stepDispatch (fc : FnCtx) (call : Expr) : M Expr := do
    let info := (← get).steps[fc.base]!
    let stepTy := Ty.named info.name
    let st ← freshLocal "l2rst"
    let v ← freshLocal "l2rsv"
    let mut arms : Array Arm := #[{ ty := info.name, ctor := some "done", binders := #[some v], body := .ofExpr (.var v) }]
    for h : i in [:info.calls.size] do
      let c := info.calls[i]
      let xs ← c.params.mapM fun _ => freshLocal "l2rsa"
      -- The binders in the variant's field order, the call's arguments in
      -- parameter order.
      arms := arms.push { ty := info.name, ctor := some s!"c{i}", binders := c.order.map (some xs[·]!),
                          body := .ofExpr (.call c.fn #[] (xs.map .var)) }
    return .block ⟨#[(st, some stepTy, call)], .mtch (.var st) arms⟩
end

/-- Field types of the variants of the enums declared by `items` and by the
prelude's source (`enum [value] L2RUnit { u }`). -/
def variantTable (items : Array Item) (prelude : String) : Std.HashMap (String × String) (Array Ty) := Id.run do
  let mut out : Std.HashMap (String × String) (Array Ty) := {}
  for it in items do
    if let .enum n _ vs := it then
      for (v, fs) in vs do out := out.insert (n, v) fs
  let mut cur : Option String := none
  for line in prelude.splitOn "\n" do
    let l := line.trimAscii.toString
    let l := if l.startsWith "pub " then (l.drop 4).toString else l
    if l.startsWith "enum " then
      let rest := (l.drop 5).toString
      let rest := if rest.startsWith "[value] " then (rest.drop 8).toString else rest
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      -- Generic enums (`enum Foo<T>`) are skipped: their field types depend
      -- on the instance.
      cur := if (rest.drop name.length).toString.trimAscii.startsWith "{" then some name else none
    else if l.startsWith "}" then cur := none
    else if let some n := cur then
      let l := if l.endsWith "," then (l.dropEnd 1).toString else l
      let v := (l.takeWhile fun c => c.isAlphanum || c == '_').toString
      if v.isEmpty then continue
      let inner := (l.drop v.length).toString.trimAscii.toString
      if inner.isEmpty then out := out.insert (n, v) #[]
      else if inner.startsWith "(" && inner.endsWith ")" then
        let args := ((inner.drop 1).dropEnd 1).toString
        -- Top-level commas only.
        let (parts, last, _) := args.foldl (init := (#[], "", 0)) fun (ps, c, d) ch =>
          if ch == ',' && d == 0 then (ps.push c, "", d)
          else (ps, c.push ch, if ch == '<' || ch == '(' then d + 1 else if ch == '>' || ch == ')' then d - 1 else d)
        match (parts.push last).toList.mapM parseTy with
        | some tys => out := out.insert (n, v) tys.toArray
        | none => pure ()
  return out

mutual
  /-- The functions an expression calls. -/
  partial def exprCalls (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .var _ | .atom _ => acc
    | .call f _ args => args.foldl (fun a x => exprCalls x a) (acc.push f)
    | .apply f x => exprCalls x (exprCalls f acc)
    | .ctor _ _ args => args.foldl (fun a x => exprCalls x a) acc
    | .field x _ | .cast x _ => exprCalls x acc
    | .lam _ _ b | .block b => blockCalls b acc
    | .ite c t f => blockCalls f (blockCalls t (exprCalls c acc))
    | .mtch s arms => arms.foldl (fun a arm => blockCalls arm.body a) (exprCalls s acc)
  partial def blockCalls (b : Block) (acc : Array String) : Array String :=
    exprCalls b.result (b.lets.foldl (fun a (_, _, e) => exprCalls e a) acc)
end

/-- The cycles of the call graph `callees`: each function that can reach
itself ↦ the functions of its strongly connected component. -/
def cycles (callees : Std.HashMap String (Array String)) : Std.HashMap String (Std.HashSet String) := Id.run do
  let comps := Lean.SCC.scc (callees.toList.map (·.1)) fun f => ((callees.getD f #[]).filter callees.contains).toList
  let mut out : Std.HashMap String (Std.HashSet String) := {}
  for c in comps do
    let set : Std.HashSet String := c.foldl (·.insert ·) {}
    match c with
    | [f] => if (callees.getD f #[]).contains f then out := out.insert f set
    | _ => for f in c do out := out.insert f set
  return out

/-- Outline the deep and long tail paths and `let` values of every function
of `fns` (`taken`: every function name of the program; `types`: the type
declarations, `typeTable`). Returns the functions, each followed by the
functions outlined from it, and the step enums of the recursive functions
that were cut (`stepItem`). -/
def outlineFns (limits : Limits) (variants : Std.HashMap (String × String) (Array Ty))
    (types : TypeTable) (taken : Std.HashSet String) (fns : Array Item) : Array Item × Array Item := Id.run do
  let mut callees : Std.HashMap String (Array String) := {}
  let mut params : Std.HashMap String (Array Ty) := {}
  for it in fns do
    if let .fn name ps _ body := it then
      callees := callees.insert name (blockCalls body #[])
      params := params.insert name (ps.map (·.2))
  let cyc := cycles callees
  let mut st : St := { taken }
  let mut out := #[]
  for it in fns do
    match it with
    | .fn name ps ret body =>
      let (d, l) := extent body
      if d < limits.triggerDepth && l < limits.triggerLets then
        out := out.push it
        continue
      let env : Env := ps.foldl (fun e (n, t) => e.bind n (some t)) {}
      let cycle := cyc.getD name {}
      let fc : FnCtx := { base := name, cycle, ret, tailCalls := tailCycleCalls cycle body #[] }
      let (body, st') := ((walkBlock fc ret false env 0 0 body).run { limits, variants, params, types }).run { st with out := #[] }
      out := out.push (.fn name ps ret body) ++ st'.out
      st := st'
    | _ => out := out.push it
  return (out, st.stepOrder.map fun f => stepItem types st.steps[f]!)

/-- Every function name of the program: the prelude's (`preludeFns`) and
those of `fns` (including the functions of raw items). -/
def takenNames (preludeFns : Std.HashSet String) (fns : Array Item) : Std.HashSet String :=
  fns.foldl (init := preludeFns) fun acc it => match it with
    | .fn n .. => acc.insert n
    | .raw t => (t.splitOn "fn ").foldl (init := acc) fun acc chunk =>
      let name := chunk.takeWhile fun c => c.isAlphanum || c == '_'
      if name.isEmpty then acc else acc.insert name.toString
    | _ => acc

end LeanToReussir.Outline
