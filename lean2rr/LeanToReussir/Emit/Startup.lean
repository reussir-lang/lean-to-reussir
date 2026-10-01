import Lean
import LeanToReussir.Lower

/-!
# Program startup

What runs before `main` (translation plan §5.12): the program's startup
items in Lean's initializer order (`startupItems`, `moduleStartupKeys`), and
the startup chain that runs them (`startupChain`), cut into functions of at
most `startupChunk` steps.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Whether a module belongs to the Lean toolchain (its constants are
evaluated lazily; see translation plan §5.12). -/
def isToolchainModule (m : Name) : Bool :=
  m.getRoot ∈ [`Init, `Std, `Lean, `Lake]

/-- What a program does at startup, before `main`, like Lean's module
initializers: for each module in import order, for each declaration in
order, run an `initialize` action, or run the init function of an
`initialize c : T ← act` constant and store its result, or evaluate a
constant (native Lean evaluates every constant of a module, used or not,
instances included: their fields may compute or trace). -/
inductive StartupItem where
  | caf (decl : Name)
  | ioUnit (fn : Name)
  | init (decl fn : Name)
  deriving Inhabited

def StartupItem.root : StartupItem → Name
  | .caf d => d
  | .ioUnit f => f
  | .init _ f => f

/-- Lexicographic order on arrays of numbers (shorter first on a common
prefix). -/
def lexLtNat (a b : Array Nat) : Bool := Id.run do
  for i in [:min a.size b.size] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size < b.size

/-- Source positions compared as (line, column). -/
def posLt (a b : Position) : Bool := a.line < b.line || (a.line == b.line && a.column < b.column)

def posLe (a b : Position) : Bool := !posLt b a

/-- A declaration's source position for ordering: its range's start, then
its name's position (`selectionRange`), each as (line, column). The
declarations of one macro expansion all have the macro call's range; their
names, when the macro takes them from its arguments, keep their own
positions. -/
def rangeKey (r : DeclarationRanges) : Array Nat :=
  #[r.range.pos.line, r.range.pos.column, r.selectionRange.pos.line, r.selectionRange.pos.column]

/-- Strings compared with their runs of digits as numbers (`_unsafe_4`
before `_unsafe_10`, `spec_9` before `spec_10`). -/
def natStrLt (a b : String) : Bool := Id.run do
  let mut i := 0
  let mut j := 0
  let a := a.toList.toArray
  let b := b.toList.toArray
  while i < a.size && j < b.size do
    if a[i]!.isDigit && b[j]!.isDigit then
      let mut x := 0
      while i < a.size && a[i]!.isDigit do
        x := x * 10 + (a[i]!.toNat - '0'.toNat)
        i := i + 1
      let mut y := 0
      while j < b.size && b[j]!.isDigit do
        y := y * 10 + (b[j]!.toNat - '0'.toNat)
        j := j + 1
      if x != y then return x < y
    else
      if a[i]! != b[j]! then return a[i]! < b[j]!
      i := i + 1
      j := j + 1
  return a.size - i < b.size - j

/-- Names compared component by component, numbers in strings by value
(see `natStrLt`); the last resort among startup declarations that nothing
else orders. -/
def natNameLt (n1 n2 : Name) : Bool := go n1.components n2.components
where
  go : List Name → List Name → Bool
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | c1 :: r1, c2 :: r2 =>
      match c1, c2 with
      | .str _ s1, .str _ s2 => if s1 == s2 then go r1 r2 else natStrLt s1 s2 || (!natStrLt s2 s1 && s1 < s2)
      | .num _ k1, .num _ k2 => if k1 == k2 then go r1 r2 else k1 < k2
      | .num .., .str .. => true
      | _, _ => false

/-- The last resort among startup declarations that nothing else orders:
two hygienic names made in one command by their macro scopes (which
increase as the command expands its macros), then `natNameLt`. -/
def startupNameLt (n1 n2 : Name) : Bool :=
  if n1.hasMacroScopes && n2.hasMacroScopes then
    let s1 := (extractMacroScopes n1).scopes.reverse
    let s2 := (extractMacroScopes n2).scopes.reverse
    if s1 != s2 then lexLtNat s1.toArray s2.toArray else natNameLt n1 n2
  else natNameLt n1 n2

/-- Position of a declaration for ordering: module index, then the source
position of the declaration or of its nearest prefix that has one. -/
def declOrder (n : Name) : CoreM (Array Nat) := do
  let idx := ((← getEnv).getModuleIdxFor? n).map (·.toNat) |>.getD 0
  let mut m := n
  while !m.isAnonymous do
    if let some r ← findDeclarationRanges? m then return #[idx] ++ rangeKey r
    m := m.getPrefix
  return #[idx]

/-- A name rebuilt from its components (`Name.append` would reinterpret the
macro scopes of a hygienic component, such as an `initialize` function's
`_private.M.0.initFn._@.M._hyg.2`). -/
def nameOfComponents (cs : List Name) : Name :=
  cs.foldl (init := .anonymous) fun acc c => match c with
    | .str _ s => .str acc s
    | .num _ k => .num acc k
    | .anonymous => acc

/-- For a specialization `f._at_.g.spec_N`, the name after the last `_at_`
(`g.spec_N`): Lean made it while compiling `g`. -/
def specTarget? (n : Name) : Option Name := Id.run do
  let cs := n.components
  let some i := (List.range cs.length).reverse.find? (cs[·]! == `_at_) | return none
  let rest := cs.drop (i + 1)
  if rest.isEmpty then return none
  return some (nameOfComponents rest)

/-- The declaration that compiled to the IR-only declaration `n`: `n`
without the suffixes the compiler appends (`c._closed_3`, `c._boxed`,
`c._lam_0`, `f._at_.c.spec_2._redArg`), the nearest prefix that `known`
accepts. A hygienic name keeps its macro scopes at the end
(`zz._closed_0._@.M._hyg.3` is a closed term of `zz._@.M._hyg.3`). -/
partial def compiledOwner (known : Name → Bool) (n : Name) : Option Name :=
  if known n then some n
  else if n.hasMacroScopes then
    let v := extractMacroScopes n
    match v.name with
    | .str p _ | .num p _ => compiledOwner known { v with name := p }.review
    | .anonymous => none
  else match n with
    | .str p _ | .num p _ => compiledOwner known p
    | .anonymous => none

/-- Lean's compilation order of a module's declarations, as far as the
`.olean` records it: the module's `extraConstNames` are its IR
declarations that are not kernel constants (closed terms, `_boxed`
wrappers, lifted lambdas, specializations), newest first, and Lean adds a
command's IR when it compiles the command. So each declaration that
compiled to at least one of them (in practice every constant whose value
calls a function) gets the index of its first one; the specializations
made while compiling a declaration come right before it. Native Lean runs
the module's initializers in exactly this order (`EmitC.emitInitFn`). -/
def compileOrder (idx : Nat) : CoreM (Std.HashMap Name Nat) := do
  let env ← getEnv
  let some md := env.header.moduleData[idx]? | return {}
  let mut baseNames : Std.HashSet Name := {}
  for d in baseExt.getModuleEntries env idx (level := .private) do
    baseNames := baseNames.insert d.name
  let known (n : Name) : Bool := baseNames.contains n || env.contains n
  let extra := md.extraConstNames
  let mut out : Std.HashMap Name Nat := {}
  for i in [:extra.size] do
    if let some d := compiledOwner known extra[extra.size - 1 - i]! then
      unless out.contains d do out := out.insert d i
  return out

/-- Lean's initializer order for the startup declarations `items` of one
module (translation plan §5.12), as far as the program's structure tells
it; `startupItems` then puts the items that `comp` (`compileOrder`) places
in that order. Native Lean initializes a module's declarations in
compilation order. A `def`/`instance` command is compiled after it is
elaborated, together with its `where`/`let rec` helpers: the elaborator
lists the helpers (those of later mutual members first, outer before
nested ones, a member's `where` helpers before the `let rec`s of its body)
and then the command's declarations, and compiles the strongly connected
components of their reference graph one by one, callees first (Tarjan over
that list, `addPreDefinitions`). The specializations made while compiling
a component come before its members, and an auxiliary declaration made
during elaboration (`c.unsafe_1`, `instInhabitedP.default`) before the
whole command. lean2rr sees the command through declaration ranges: a
helper's range lies inside its parent's, the kernel's `all` lists a
recursive mutual block, and a `mutual` block whose members do not call
each other shows in `comp` (a later member's code compiled before an
earlier one's). Returns a sort key per item. -/
partial def moduleStartupKeys (idx : Nat) (items : Array Name) (comp : Std.HashMap Name Nat) :
    CoreM (Std.HashMap Name (Array Nat)) := do
  let env ← getEnv
  let some md := env.header.moduleData[idx]? | return {}
  -- Ranges of the module's declarations, and each `initialize` function's
  -- constant (the function belongs to its constant's position).
  let mut ranges : Std.HashMap Name DeclarationRanges := {}
  let mut initOf : Std.HashMap Name Name := {}
  for c in md.constNames do
    if let some r ← findDeclarationRanges? c then ranges := ranges.insert c r
    if let some f := getInitFnNameFor? env c <|> getBuiltinInitFnNameFor? env c then
      initOf := initOf.insert f c
  let ranged? (n : Name) : Option Name := Id.run do
    let mut m := n
    while !m.isAnonymous do
      if ranges.contains m then return some m
      m := m.getPrefix
    return none
  let vertexOf? (n : Name) : Option Name := (ranged? n).map fun v => initOf.getD v v
  -- A `where`/`let rec` helper's range is a part of its parent's. Equal
  -- ranges are not enclosure: every declaration of a macro expansion has
  -- the macro call's range (`mk foo foo.bar` defines two commands).
  let encloses (outer inner : Name) : Bool := Id.run do
    let some o := ranges[outer]? | return false
    let some i := ranges[inner]? | return false
    let same := o.range.pos == i.range.pos && o.range.endPos == i.range.endPos
    return !same && posLe o.range.pos i.range.pos && posLe i.range.endPos o.range.endPos
  -- Declarations that no position orders (the instances of one `deriving
  -- instance … for A, B` command have the same range and name position):
  -- the order in which the module added its instances.
  let mut instIdx : Std.HashMap Name Nat := {}
  for e in Meta.instanceExtension.ext.getModuleEntries env idx do
    let i := match e with | .global i | .scoped _ i => i
    if let some g := i.globalName? then
      unless instIdx.contains g do instIdx := instIdx.insert g (instIdx.size + 1)
  let posKey (v : Name) : Array Nat :=
    ((ranges[v]?.map rangeKey).getD #[0, 0, 0, 0]).push (instIdx.getD v 0)
  -- The enclosing declaration of a helper (outermost prefix whose range
  -- contains its range), and its nesting depth.
  let memberOf (v : Name) : Name × Nat := Id.run do
    let mut top := v
    let mut depth := 0
    let mut p := v.getPrefix
    while !p.isAnonymous do
      if ranges.contains p && encloses p v then
        top := p
        depth := depth + 1
      p := p.getPrefix
    return (initOf.getD top top, depth)
  -- The members of a recursive mutual block, in the block's order.
  let allOf (main : Name) : List Name := match env.find? main with
    | some (.defnInfo d) => d.all
    | some (.opaqueInfo o) => o.all
    | _ => [main]
  -- The first member of a recursive mutual block (by position, then the
  -- block's order: a macro-made block has one range).
  let blockOf (main : Name) : Name := Id.run do
    let mut best := main
    let mut bestKey := posKey main
    for m in allOf main do
      if ranges.contains m && lexLtNat (posKey m) bestKey then
        best := m
        bestKey := posKey m
    return best
  let rootOf0 (v : Name) : Name := blockOf (memberOf v).1
  -- `mutual` blocks whose members do not call each other (the kernel
  -- records them as separate definitions): Lean compiles one command after
  -- another, in source order, so a command with code compiled before code of
  -- an earlier command (`comp`) shares a `mutual` block with it, and with
  -- every command in between. The commands, by position, are merged into
  -- groups whose compilation intervals overlap.
  let mut rootC : Std.HashMap Name Nat := {}
  for (d, i) in comp do
    if let some v := vertexOf? ((specTarget? d).getD d) then
      let r := rootOf0 v
      if rootC.getD r i ≥ i then rootC := rootC.insert r i
  let mut rootSet : Std.HashSet Name := {}
  for (c, _) in ranges do
    unless initOf.contains c do rootSet := rootSet.insert (rootOf0 c)
  let roots := rootSet.toArray.qsort fun a b =>
    lexLtNat (posKey a) (posKey b) || (posKey a == posKey b && natNameLt a b)
  -- A stack of groups (members, the latest first compilation among them);
  -- the latter never decreases up the stack.
  let mut groups : Array (Array Name × Nat) := #[]
  for r in roots do
    match rootC[r]? with
    | none => groups := groups.push (#[r], (groups.back?.map (·.2)).getD 0)
    | some c =>
      let mut members := #[r]
      let mut top := c
      while h : groups.size > 0 do
        let g := groups[groups.size - 1]
        unless g.2 > c do break
        members := g.1 ++ members
        top := max top g.2
        groups := groups.pop
      groups := groups.push (members, top)
  let mut superOf : Std.HashMap Name Name := {}
  let mut superMembers : Std.HashMap Name (List Name) := {}
  for (ms, _) in groups do
    if ms.size > 1 then
      for m in ms do superOf := superOf.insert m ms[0]!
      superMembers := superMembers.insert ms[0]! ms.toList
  let rootOf (v : Name) : Name := let r := rootOf0 v; superOf.getD r r
  let rootKey (root : Name) : Array Nat := posKey root
  -- The vertices of the commands that have startup items.
  let mut wanted : Std.HashSet Name := {}
  for n in items do
    if let some v := vertexOf? ((specTarget? n).getD n) then wanted := wanted.insert (rootOf v)
  let mut blocks : Std.HashMap Name (Array Name) := {}
  for (c, _) in ranges do
    if initOf.contains c then continue
    let r := rootOf c
    if wanted.contains r then blocks := blocks.insert r ((blocks.getD r #[]).push c)
  -- Rank of each vertex: the index of its component in compilation order.
  let mut rank : Std.HashMap Name Nat := {}
  for (r, vs) in blocks do
    if vs.size == 1 then
      rank := rank.insert vs[0]! 0
      continue
    let vset : Std.HashSet Name := vs.foldl (·.insert ·) {}
    let order := superMembers[r]?.getD (allOf r)
    let blockIdx (v : Name) : Nat := (order.findIdx? (· == v)).getD order.length
    let mains := (vs.filter fun v => (memberOf v).1 == v).qsort fun a b =>
      lexLtNat ((posKey a).push (blockIdx a)) ((posKey b).push (blockIdx b))
    let memberIdx (v : Name) : Nat := (mains.findIdx? (· == (memberOf v).1)).getD 0
    -- A member's `where` helpers come before the `let rec`s of its body (a
    -- `where` clause is a `let rec` around the body). They are the last
    -- direct helpers: the last one ends where the member ends, and the
    -- others start at its column on earlier lines (each `where` declaration
    -- on a new line starts at the first one's column).
    let mut whereHelpers : Std.HashSet Name := {}
    for m in mains do
      let direct := (vs.filter fun v => v != m && memberOf v == (m, 1)).qsort fun a b =>
        lexLtNat (posKey a) (posKey b)
      let some last := direct.back? | continue
      let (some mr, some lr) := (ranges[m]?, ranges[last]?) | continue
      unless lr.range.endPos == mr.range.endPos do continue
      whereHelpers := whereHelpers.insert last
      let mut next := lr.selectionRange.pos
      for i in [:direct.size - 1] do
        let v := direct[direct.size - 2 - i]!
        let some vr := ranges[v]? | break
        let p := vr.selectionRange.pos
        unless p.column == next.column && p.line < next.line do break
        whereHelpers := whereHelpers.insert v
        next := p
    let key (v : Name) : Array Nat :=
      let depth := (memberOf v).2
      #[mains.size - memberIdx v, depth, if depth == 1 && !whereHelpers.contains v then 1 else 0] ++ posKey v
    let helpers := (vs.filter fun v => (memberOf v).1 != v).qsort fun a b =>
      lexLtNat (key a) (key b) || (key a == key b && startupNameLt a b)
    -- References of a vertex's value to other vertices of the command,
    -- through its own auxiliary declarations (`._unary`, `.match_1`); a
    -- `partial` definition's code is its `._unsafe_rec`. Lean lists them in
    -- reverse order of first occurrence.
    let succs (v : Name) : List Name := Id.run do
      let mut out : Array Name := #[]
      let mut seen : Std.HashSet Name := {}
      let mut todo : Array Name := #[if env.contains (v ++ `_unsafe_rec) then v ++ `_unsafe_rec else v]
      let mut visited : Std.HashSet Name := {}
      while h : todo.size > 0 do
        let c := todo.back
        todo := todo.pop
        if visited.contains c then continue
        visited := visited.insert c
        let some info := env.find? c | continue
        let some val := info.value? (allowOpaque := true) | continue
        for d in val.getUsedConstants do
          match vertexOf? d with
          | some u =>
            if u != v && vset.contains u then
              unless seen.contains u do
                seen := seen.insert u
                out := out.push u
            else if u == v && !ranges.contains d then
              todo := todo.push d
          | none => pure ()
      return out.toList.reverse
    let comps := Lean.SCC.scc (helpers ++ mains).toList succs
    for h : i in [:comps.length] do
      for v in comps[i] do rank := rank.insert v i
  -- Keys: command position, then component, then: auxiliary declarations
  -- first (component 0), specializations before their component's members,
  -- specializations by number.
  let specNo (n : Name) : Nat :=
    match n.components.getLast? with
    | some (.str _ s) => if s.startsWith "spec_" then ((s.drop 5).toString.toNat?).getD 0 else 0
    | _ => 0
  let none5 : Array Nat := #[0, 0, 0, 0, 0]
  let mut out : Std.HashMap Name (Array Nat) := {}
  for n in items do
    let key := match specTarget? n with
      | some g => match vertexOf? g with
        | some v => rootKey (rootOf v) ++ #[1 + rank.getD v 0, 0, specNo n]
        | none => none5 ++ #[0, 0, specNo n]
      | none => match vertexOf? n with
        | some v =>
          if ranges.contains n then rootKey (rootOf v) ++ #[1 + rank.getD v 0, 1, 0]
          else rootKey (rootOf v) ++ #[0] ++ posKey (ranged? n |>.getD v)
        | none => none5 ++ #[0, 0, 0]
    out := out.insert n key
  return out

/-- The startup items of the program's own (non-toolchain) modules, in
order. Constants are the module's compiled zero-parameter declarations
(as native Lean's module initializer), so compiler-generated ones such as
specializations with every parameter fixed are included. -/
def startupItems : CoreM (Array StartupItem) := do
  let env ← getEnv
  let mut byModule : Std.HashMap Nat (Array (StartupItem × Name)) := {}
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    if isToolchainModule modName then continue
    let item? :=
      if isIOUnitInitFn env n then some (StartupItem.ioUnit n)
      else if let some f := getInitFnNameFor? env n then some (.init n f)
      else none
    let some item := item? | continue
    byModule := byModule.insert idx.toNat ((byModule.getD idx.toNat #[]).push (item, n))
  -- The constants each constant reads (see the end).
  let mut reads : Std.HashMap Name (Array Name) := {}
  for h : idx in [:env.header.moduleNames.size] do
    if isToolchainModule env.header.moduleNames[idx] then continue
    for d in baseExt.getModuleEntries env idx (level := .private) do
      let n := d.name
      let .code c := d.value | continue
      unless d.params.isEmpty do continue
      if isIOUnitInitFn env n || (getInitFnNameFor? env n).isSome then continue
      byModule := byModule.insert idx ((byModule.getD idx #[]).push (.caf n, n))
      reads := reads.insert n (codeConsts c #[])
  -- Ties: by name (`startupNameLt`). Then the items that Lean's recorded
  -- compilation order places (`compileOrder`) are put in that order, in the
  -- places the sort gave them: they include every specialization, and in
  -- practice every constant that can trace or panic.
  let mut out := #[]
  for idx in (byModule.toArray.map (·.1)).qsort (· < ·) do
    let its := byModule.getD idx #[]
    let comp ← compileOrder idx
    let keys ← moduleStartupKeys idx (its.map (·.2)) comp
    let sorted := its.qsort fun (_, n1) (_, n2) =>
      let k1 := keys.getD n1 #[]
      let k2 := keys.getD n2 #[]
      lexLtNat k1 k2 || (k1 == k2 && startupNameLt n1 n2)
    -- An item's compiled code: an `initialize` constant's is its action's,
    -- a `partial` constant's its `_unsafe_rec`.
    let compOf (it : StartupItem) (n : Name) : Option Nat :=
      comp[n]? <|> (match it with | .init _ f => comp[f]? | _ => none) <|> comp[n ++ `_unsafe_rec]?
    let placed := sorted.filterMap fun (it, n) => (compOf it n).map fun c => (c, (it, n))
    let byComp := (placed.qsort fun a b => a.1 < b.1).map (·.2)
    let mut refilled : Array (StartupItem × Name) := #[]
    let mut j := 0
    for (it, n) in sorted do
      if (compOf it n).isSome then
        refilled := refilled.push byComp[j]!
        j := j + 1
      else
        refilled := refilled.push (it, n)
    -- The others keep their places, except that a constant goes after the
    -- constants it reads. Compiled to no IR-only declaration, it only builds
    -- a value from literals and other constants (it cannot trace or panic),
    -- but evaluating it evaluates the constants it reads (accessors compute
    -- on demand), which natively come before it (a constant reads constants
    -- declared before it, or its own helpers). Key: the place of the last
    -- constant it reads (transitively), then the length of that chain.
    let mut place : Std.HashMap Name (Nat × Nat) := {}
    for h : i in [:refilled.size] do place := place.insert refilled[i].2 (i, 0)
    let movable := refilled.filter fun (it, n) => (compOf it n).isNone
    let mut changed := true
    let mut rounds := 0
    while changed && rounds < 64 do
      changed := false
      rounds := rounds + 1
      for (_, n) in movable do
        let mut k := place.getD n (0, 0)
        for r in reads.getD n #[] do
          if let some (p, d) := place[r]? then
            if r != n && lexLtNat #[k.1, k.2] #[p, d + 1] then k := (p, d + 1)
        if k != place.getD n (0, 0) then
          place := place.insert n k
          changed := true
    let idxOf : Std.HashMap Name Nat := (refilled.zipIdx.map fun ((_, n), i) => (n, i)).foldl
      (fun m (n, i) => m.insert n i) {}
    let ordered := refilled.qsort fun (_, a) (_, b) =>
      let (ka, kb) := (place.getD a (0, 0), place.getD b (0, 0))
      lexLtNat #[ka.1, ka.2, idxOf.getD a 0] #[kb.1, kb.2, idxOf.getD b 0]
    out := out ++ ordered.map (·.1)
  return out

/-- A startup step with instance names (see `StartupItem`). -/
inductive StartupStep where
  | caf (inst : Name)
  | ioUnit (inst : Name)
  | init (decl inst : Name)
  deriving Inhabited

/-- The IO result type of an instance and its `ok`/`error` variants. -/
def ioResultOf (inst : Name) : LowerM (String × String × String × Option RR.Ty) := do
  let some d := (← read).decls.find? inst | throwError "lean2rr: no declaration {inst}"
  let (_, r) := splitFnType d.type d.params.size
  let .named outTy ← lowerType r | throwError "lean2rr: {inst} does not return an IO result"
  let some info := (← get).typeInfos[outTy]? | throwError "lean2rr: {inst} does not return EST.Out"
  let okV := (info.ctors.find? ``EST.Out.ok).map (·.variant) |>.getD "c_ok"
  let errV := (info.ctors.find? ``EST.Out.error).map (·.variant) |>.getD "c_error"
  let okField := (info.ctors.find? ``EST.Out.ok).bind (·.fields[0]?) |>.join |>.map (·.2)
  return (outTy, okV, errV, okField)

/-- The startup chain is cut into functions of at most this many steps
(and their calls grouped the same way): one chain of nested matches per
program would be as deep as the program has initializers, and rrc's
recursive lowering overflows its stack on a few thousand. Required, not an
optimization (see Opt/Registry.lean). -/
def startupChunk : Nat := 128

/-- The startup chain (see `StartupItem`): the steps `startup` run in order,
cut into functions of at most `startupChunk` steps, and `l2r_init_body`,
which runs them. An error in an initializer is reported like an uncaught
exception of `main` (`errStr` renders it). -/
def startupChain (errStr : Name) (startup : Array StartupStep) : LowerM String := do
  -- Each function returns 0 once its steps succeeded; an error in an
  -- initializer is reported and exits (`l2r_init_failed`), so later
  -- initializers do not run. The chain ends by clearing `IO.initializing`.
  let chunk := startupChunk
  let failed (e : String) := s!"l2r_init_failed({fnName errStr}({e}))"
  let mut initFns := ""
  let mut calls : Array String := #[]
  let mut start := 0
  while start < startup.size do
    let stop := min startup.size (start + chunk)
    -- Build the chunk's chain from its last step outwards.
    let mut code := "0"
    for i in [:stop - start] do
      let j := stop - 1 - i
      match startup[j]! with
      | .caf inst => code := s!"let caf{j} = {fnName inst}();\n" ++ code
      | .ioUnit inst =>
        let (t, ok, err, _) ← ioResultOf inst
        code := s!"match {fnName inst}(L2RUnit::u\{}) \{\n{t}::{ok}(v{j}) => \{\n{code}\n},\n{t}::{err}(e{j}) => \{ {failed s!"e{j}"} }\n}"
      | .init decl inst =>
        let (t, ok, err, field) ← ioResultOf inst
        let some slot := (← get).initSlots.find? decl | throwError "lean2rr: no slot for {decl}"
        let vt := field.getD RR.Ty.unit
        let (st, boxed) ← arrayElemTy vt
        let stored := if boxed then match st with | .named bn => s!"{bn}\{v{j}}" | _ => s!"v{j}" else s!"v{j}"
        code := s!"match {fnName inst}(L2RUnit::u\{}) \{\n{t}::{ok}(v{j}) => \{\nlet s{j} : {st.render} = l2r_once_set<{st.render}>({slot}, {stored});\n{code}\n},\n{t}::{err}(e{j}) => \{ {failed s!"e{j}"} }\n}"
    let name := s!"l2r_init_chunk_{calls.size}"
    initFns := initFns ++ s!"fn {name}() -> u64 \{\n{code}\n}\n\n"
    calls := calls.push s!"let ic{calls.size} : u64 = {name}();"
    start := stop
  -- Many chunks: group their calls the same way.
  let mut level := 0
  while calls.size > chunk do
    let mut next : Array String := #[]
    let mut g := 0
    while g * chunk < calls.size do
      let part := calls.extract (g * chunk) ((g + 1) * chunk)
      let name := s!"l2r_init_group_{level}_{g}"
      initFns := initFns ++ s!"fn {name}() -> u64 \{\n{"\n".intercalate part.toList}\n0\n}\n\n"
      next := next.push s!"let ig{g} : u64 = {name}();"
      g := g + 1
    calls := next
    level := level + 1
  return initFns ++
    s!"fn l2r_init_body() \{\nlet si : u64 = l2r_set_initializing(true);\n{"\n".intercalate calls.toList}\nl2r_init_done()\n}\n\n"

end LeanToReussir
