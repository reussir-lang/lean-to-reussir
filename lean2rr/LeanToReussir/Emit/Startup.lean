import Lean
import LeanToReussir.Lower
import LeanToReussir.CompileRecord

/-!
# Program startup

What runs before `main` (translation plan §5.12): the program's startup
items in Lean's initializer order (`startupItems`, `moduleStartupKeys`), and
the startup chain that runs them (`startupChain`), cut into functions of at
most `startupChunk` steps.
-/

namespace LeanToReussir
open Lean Compiler LCNF

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

/-- For a specialization `f._at_.g.spec_N`, the name after the last `_at_`
(`g.spec_N`): Lean made it while compiling `g`. -/
def specTarget? (n : Name) : Option Name := Id.run do
  let cs := n.components
  let some i := (List.range cs.length).reverse.find? (cs[·]! == `_at_) | return none
  let rest := cs.drop (i + 1)
  if rest.isEmpty then return none
  return some (nameOfComponents rest)

/-- Whether `f` is the function that `initialize c : T ← act` (or
`builtin_initialize`) makes for its action, a hygienic `initFn`: it is
compiled with its constant, unlike the function of a hand-written
`@[init f]`. -/
def isGeneratedInitFn (f : Name) : Bool := f.hasMacroScopes

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
earlier one's) or in a use of a later member. Returns a sort key per
item. -/
partial def moduleStartupKeys (idx : Nat) (items : Array Name) (comp : Std.HashMap Name Nat) :
    CoreM (Std.HashMap Name (Array Nat)) := do
  let env ← getEnv
  let some md := env.header.moduleData[idx]? | return {}
  -- Ranges of the module's declarations, and each `initialize` function's
  -- constant (the function belongs to its constant's position). Only the
  -- functions `initialize` makes (`isGeneratedInitFn`): the function of a
  -- hand-written `@[init f]` is an ordinary declaration of its own.
  let mut ranges : Std.HashMap Name DeclarationRanges := {}
  let mut initOf : Std.HashMap Name Name := {}
  for c in md.constNames do
    if let some r ← findDeclarationRanges? c then ranges := ranges.insert c r
    if let some f := getInitFnNameFor? env c <|> getBuiltinInitFnNameFor? env c then
      if isGeneratedInitFn f then initOf := initOf.insert f c
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
  -- `reach[i]`: the last command (by position) that command `i` shares a
  -- block with.
  let mut reach : Array Nat := Array.range roots.size
  let mut first := 0
  for (ms, _) in groups do
    reach := reach.set! first (first + ms.size - 1)
    first := first + ms.size
  -- Also a command that uses a later command shares a block with it:
  -- outside a `mutual` block a declaration can only use earlier ones. The
  -- uses are those of the declaration's value and of its own auxiliary
  -- declarations (`._unary`, `.match_1`; a `partial` definition's code is
  -- its `._unsafe_rec`).
  let mut rootIdx : Std.HashMap Name Nat := {}
  for h : i in [:roots.size] do rootIdx := rootIdx.insert roots[i] i
  for (c, _) in ranges do
    if initOf.contains c then continue
    let some i := rootIdx[rootOf0 c]? | continue
    let mut todo : Array Name := #[c, c ++ `_unsafe_rec]
    let mut visited : Std.HashSet Name := {}
    while h : todo.size > 0 do
      let d := todo.back
      todo := todo.pop
      if visited.contains d then continue
      visited := visited.insert d
      let some info := env.find? d | continue
      if info matches .thmInfo _ then continue
      let some val := info.value? (allowOpaque := true) | continue
      for u in val.getUsedConstants do
        match vertexOf? u with
        | some w =>
          if w == c && !ranges.contains u then todo := todo.push u
          else if let some j := rootIdx[rootOf0 w]? then
            if j > i && j > reach[i]! then reach := reach.set! i j
        | none => pure ()
  let mut superOf : Std.HashMap Name Name := {}
  let mut superMembers : Std.HashMap Name (List Name) := {}
  let mut start := 0
  while start < roots.size do
    let mut last := reach[start]!
    let mut k := start + 1
    while k ≤ last && k < roots.size do
      last := max last reach[k]!
      k := k + 1
    if last > start then
      let ms := roots.extract start (last + 1)
      for m in ms do superOf := superOf.insert m ms[0]!
      superMembers := superMembers.insert ms[0]! ms.toList
    start := last + 1
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
    -- direct helpers: the last one ends where the member ends, and each
    -- other one starts on the line of the next one (separated by `;`) or at
    -- its column on an earlier line (each `where` declaration on a new line
    -- starts at the first one's column), unless a doc comment or an
    -- attribute, which the ranges leave out, shifts one of them.
    let doc? (v : Name) : Option String := docStringExt.find? (level := .server) env v
    let shifted (v : Name) : Bool := (doc? v).isSome || (Compiler.getInlineAttribute? env v).isSome
    -- The most lines a doc comment and an attribute before `v` can take.
    let shiftLines (v : Name) : Nat :=
      ((doc? v).map fun d => (d.splitOn "\n").length).getD 0 +
        (if (Compiler.getInlineAttribute? env v).isSome then 1 else 0)
    let mut whereHelpers : Std.HashSet Name := {}
    for m in mains do
      let direct := (vs.filter fun v => v != m && memberOf v == (m, 1)).qsort fun a b =>
        lexLtNat (posKey a) (posKey b)
      let some last := direct.back? | continue
      let (some mr, some lr) := (ranges[m]?, ranges[last]?) | continue
      unless lr.range.endPos == mr.range.endPos do continue
      whereHelpers := whereHelpers.insert last
      -- `next`: the one after `v`; `ref`: the start of the nearest unshifted
      -- one after `v`. Without one, `v` must end on the line before `next`
      -- (or before its doc comment and attribute lines).
      let mut next := last
      let mut ref := if shifted last then none else some lr.range.pos
      for i in [:direct.size - 1] do
        let v := direct[direct.size - 2 - i]!
        let (some vr, some nr) := (ranges[v]?, ranges[next]?) | break
        let (p, q) := (vr.range.pos, nr.range.pos)
        let ok := match ref with
          | some r => p.column == r.column && p.line < r.line
          | none => q.line ≤ vr.range.endPos.line + 1 + shiftLines next
        unless ok || p.line == q.line || shifted v do break
        whereHelpers := whereHelpers.insert v
        next := v
        unless shifted v do ref := some p
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

/-- The modules below `idx` (included) in initialization order, added
to `acc` (the modules visited, the order so far): Lean's module initializer first
calls those of the module's imports, in import order, each module once, so
the order is a depth-first post-order walk of the import graph. `meta`
imports are followed only when `followMeta` (see `startupModules`).
Toolchain modules are left out unless `toolchain` (§5.12; they import only
toolchain modules). -/
partial def importPostOrder (env : Environment) (followMeta : Bool) (toolchain : Bool) (idx : Nat)
    (acc : Std.HashSet Nat × Array Nat) : Std.HashSet Nat × Array Nat := Id.run do
  if acc.1.contains idx then return acc
  let mut acc := (acc.1.insert idx, acc.2)
  let some md := env.header.moduleData[idx]? | return acc
  for imp in md.imports do
    if imp.isMeta && !followMeta then continue
    if !toolchain && isToolchainModule imp.module then continue
    let some j := env.getModuleIdx? imp.module | continue
    acc := importPostOrder env followMeta toolchain j.toNat acc
  return (acc.1, acc.2.push idx)

/-- The program modules whose initializers run before `main`, in order, and
whether only their runtime phase runs (translation plan §5.12; with
`toolchain`, the toolchain's modules too). Native
`main` runs the initializer of `main`'s module (`EmitC.emitMainFn`). For a
`module` (module system) that is its runtime-phase initializer
(`emitInitFn (phases := .runtime)`): it calls the runtime-phase
initializers of the module's non-`meta` imports only, then initializes the
module's declarations not marked `meta`. A non-module `main` module runs
the initializers of all its imports, and an imported `module`'s
initializer there (`emitLegacyInitFn`) runs its imports' initializers, then
its runtime-phase declarations, then its `meta` ones. Without `root`'s
module, every program module (with `toolchain`, every module), by index. -/
def startupModules (env : Environment) (root : Name) (toolchain := false) : Array Nat × Bool :=
  match env.getModuleIdxFor? root with
  | some mainIdx =>
    let runtimeOnly := (env.header.moduleData[mainIdx.toNat]?.map (·.isModule)).getD false
    ((importPostOrder env (followMeta := !runtimeOnly) toolchain mainIdx.toNat ({}, #[])).2, runtimeOnly)
  | none =>
    ((Array.range env.header.moduleNames.size).filter fun i =>
      toolchain || !isToolchainModule env.header.moduleNames[i]!, false)

/-- The startup item of declaration `n` if it is an `initialize` declaration
(`initialize do …`: its function; `initialize c : T ← act`: `c`, with the
function of `act`), whose initializer native Lean runs. -/
def initItem? (env : Environment) (n : Name) : Option StartupItem :=
  if isIOUnitInitFn env n then some (.ioUnit n)
  else (getInitFnNameFor? env n).map (.init n)

/-- The startup items of library module `idx` (`isLibraryModule`): its
`initialize` declarations, by source position, for its phases as in
`startupItems` (`runtimeOnly`). They run used or not, at the module's place,
as natively: an initializer is an action, and its effects show
(`IO.stdGenRef` opens and reads `/dev/urandom`, and its failure ends the
program). The library's other constants are not startup items: they are
pure, and evaluating them lazily, on first use, cannot be told from native
Lean's evaluation at startup. Lean 4.34.0's `Init` and `Std` have one
initializer, `IO.stdGenRef` (translation plan §5.12). -/
def libraryModuleItems (idx : Nat) (runtimeOnly : Bool) : CoreM (Array StartupItem) := do
  let env ← getEnv
  let some md := env.header.moduleData[idx]? | return #[]
  let mut its : Array (StartupItem × Name × Array Nat) := #[]
  for n in md.constNames do
    if let some it := initItem? env n then its := its.push (it, n, ← declOrder n)
  let sorted := its.qsort fun (_, n1, k1) (_, n2, k2) =>
    lexLtNat k1 k2 || (k1 == k2 && startupNameLt n1 n2)
  let runtime := sorted.filter fun (_, n, _) => !isMarkedMeta env n
  let phased :=
    if runtimeOnly then runtime
    else if md.isModule then runtime ++ sorted.filter fun (_, n, _) => isMarkedMeta env n
    else sorted
  return phased.map (·.1)

/-- Whether the program uses the `Lean` package (`usesModuleFrom env `Lean`
for `main`'s module): a module of it is among `modules`, the modules whose
initializers run (`startupModules` with the toolchain's). -/
def usesLeanPackage (env : Environment) (modules : Array Nat) : Bool :=
  modules.any fun i => (`Lean).isPrefixOf env.header.moduleNames[i]!

/-- The modules that `lean_initialize()` initializes, in order, and the set
of them: in a program that uses the `Lean` package (`usesLeanPackage`),
`main`'s module initializer calls it before anything else, and it
initializes all of `Init`, then all of `Std` (`initialize_Init`,
`initialize_Std`: every import followed, each module once), then all of
`Lean`, whatever the program imports. lean2rr runs the initializers of the
first two (`Env.loadEnvironment` loads them for such a program) and not the
`Lean` package's (plan §10). -/
def leanInitModules (env : Environment) : Std.HashSet Nat × Array Nat :=
  [`Init, `Std].foldl (init := ({}, #[])) fun acc lib =>
    match env.getModuleIdx? lib with
    | some j => importPostOrder env (followMeta := true) (toolchain := true) j.toNat acc
    | none => acc

/-- The startup items, in order: those of the modules `startupModules`
gives (for `main` = `root`, the toolchain's modules included), each
module's in initialization order and for its phases. A program module
contributes its startup items (`moduleStartupKeys`, `compileOrder`), a
module of `Init` or `Std` its `initialize` declarations
(`libraryModuleItems`), any other toolchain module nothing. Phases: with
`runtimeOnly`, the items not marked `meta`; otherwise, in a `module`, the
items not marked `meta`, then the `meta` ones. An item is marked `meta`
when the declaration native Lean initializes is (`isMarkedMeta`: for
`initialize c : T ← act`, `c`; for `initialize do …`, its function);
declarations the compiler generates (specializations) are not, as natively.
Constants are the module's compiled zero-parameter declarations (as native
Lean's module initializer), so compiler-generated ones such as
specializations with every parameter fixed are included.

Returns first, apart, the items that `lean_initialize()` runs before all
others in a program that uses the `Lean` package (`leanInitModules`; empty
otherwise); its modules are then left out of the walk. -/
def startupItems (root : Name) : CoreM (Array StartupItem × Array StartupItem) := do
  let env ← getEnv
  let (walk, runtimeOnly) := startupModules env root (toolchain := true)
  let (initialized, leanModules) :=
    if usesLeanPackage env walk then leanInitModules env else ({}, #[])
  let mut leanInit := #[]
  for idx in leanModules do
    if isLibraryModule env.header.moduleNames[idx]! then
      leanInit := leanInit ++ (← libraryModuleItems idx (runtimeOnly := false))
  let order := walk.filter (!initialized.contains ·)
  let modules := order.filter fun i => !isToolchainModule env.header.moduleNames[i]!
  let wanted : Std.HashSet Nat := modules.foldl (·.insert ·) {}
  let mut byModule : Std.HashMap Nat (Array (StartupItem × Name)) := {}
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless wanted.contains idx.toNat do continue
    let some item := initItem? env n | continue
    byModule := byModule.insert idx.toNat ((byModule.getD idx.toNat #[]).push (item, n))
  -- The constants each constant reads (see the end).
  let mut reads : Std.HashMap Name (Array Name) := {}
  for idx in modules do
    for d in baseExt.getModuleEntries env idx (level := .private) do
      let n := d.name
      let .code c := d.value | continue
      unless d.params.isEmpty do continue
      if (initItem? env n).isSome then continue
      byModule := byModule.insert idx ((byModule.getD idx #[]).push (.caf n, n))
      reads := reads.insert n (codeConsts c #[])
  -- Ties: by name (`startupNameLt`). Then the items that Lean's recorded
  -- compilation order places (`compileOrder`) are put in that order, in the
  -- places the sort gave them: they include every specialization and
  -- `initialize` action, and nearly every constant that calls a function.
  let mut out := #[]
  for idx in order do
    let m := env.header.moduleNames[idx]!
    if isLibraryModule m then
      out := out ++ (← libraryModuleItems idx runtimeOnly)
      continue
    if isToolchainModule m then continue
    let its := byModule.getD idx #[]
    if its.isEmpty then continue
    let comp ← compileOrder idx
    let keys ← moduleStartupKeys idx (its.map (·.2)) comp
    let sorted := its.qsort fun (_, n1) (_, n2) =>
      let k1 := keys.getD n1 #[]
      let k2 := keys.getD n2 #[]
      lexLtNat k1 k2 || (k1 == k2 && startupNameLt n1 n2)
    -- An item's compiled code: an `initialize` constant's is its action's
    -- (not that of a hand-written `@[init f]`'s `f`, compiled earlier), a
    -- `partial` constant's its `_unsafe_rec`.
    let compOf (it : StartupItem) (n : Name) : Option Nat :=
      comp[n]? <|> (match it with | .init _ f => if isGeneratedInitFn f then comp[f]? else none | _ => none) <|>
        comp[n ++ `_unsafe_rec]?
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
    -- constants it reads: evaluating it evaluates them (accessors compute
    -- on demand), and natively they come before it (a constant reads
    -- constants declared before it, or its own helpers). Key: the place of
    -- the last constant it reads (transitively), then the length of that
    -- chain.
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
    -- The module's phases (see above), each in that order.
    let isMeta (n : Name) : Bool := isMarkedMeta env n
    let runtime := ordered.filter fun (_, n) => !isMeta n
    let phased :=
      if runtimeOnly then runtime
      else if (env.header.moduleData[idx]?.map (·.isModule)).getD false then
        runtime ++ ordered.filter fun (_, n) => isMeta n
      else ordered
    out := out ++ phased.map (·.1)
  return (leanInit, out)

/-- A startup step with instance names (see `StartupItem`). -/
inductive StartupStep where
  | caf (inst : Name)
  | ioUnit (inst : Name)
  | init (decl inst : Name)
  deriving Inhabited

/-- The IO result type of an instance, its `ok`/`error` variants, the type
of its `ok` field (a `Box`: the payload's type is a parameter) and the
payload's own type (from the instance's Lean result type). -/
def ioResultOf (inst : Name) : LowerM (String × String × String × Option RR.Ty × RR.Ty) := do
  let some d := (← read).decls.find? inst | throwError "lean2rr: no declaration {inst}"
  let (_, r) := splitFnType d.type d.params.size
  let .named outTy ← lowerType r | throwError "lean2rr: {inst} does not return an IO result"
  let some info := (← get).typeInfos[outTy]? | throwError "lean2rr: {inst} does not return EST.Out"
  let okV := (info.ctors.find? ``EST.Out.ok).map (·.variant) |>.getD "c_ok"
  let errV := (info.ctors.find? ``EST.Out.error).map (·.variant) |>.getD "c_error"
  let okField := (info.ctors.find? ``EST.Out.ok).bind (·.fields[0]?) |>.join |>.map (·.2)
  return (outTy, okV, errV, okField, ← ioPayloadType r)

/-- `l2r_err_string(e)`: the text of an uncaught `IO.Error` (Lean's
`IO.Error.toString`, instance `errStr`), from the error field `e : errTy`
of an IO result (a `Box`, unboxed here: the raw text of the entry point and
the startup chain calls this function). Generated once. -/
def errStringFn (errStr : Name) (outTy : String) : LowerM String := do
  let name := "l2r_err_string"
  if ← hasFn name then return name
  let some info := (← get).typeInfos[outTy]? | throwError "lean2rr: no IO result type {outTy}"
  let some (some (_, errTy)) := (info.ctors.find? ``EST.Out.error).bind (·.fields[0]?)
    | throwError "lean2rr: IO result {outTy} has no error field"
  let some d := (← read).decls.find? errStr | throwError "lean2rr: no declaration {errStr}"
  let pt ← match d.params[0]? with
    | some p => lowerType p.type
    | none => pure errTy
  let arg ← coerce (.var "e") errTy pt
  let body ← coerce (.call (fnName errStr) #[] #[arg]) (← lowerType (splitFnType d.type d.params.size).2) (.named "LStr")
  modify fun s => { s with fns := s.fns.push (.fn name #[("e", errTy)] (.named "LStr") (.ofExpr body)) }
  return name

/-- `l2r_init_put_<slot>(v)`: store the value `v : vt` (the `ok` field of
the IO result of `initialize` constant `decl`'s action, a `Box`) into the
constant's once-cell `slot`, at the constant's own type, the type its reads
take it at (`Callee.initConst`). A value that may hold a task is walked
first (`persistCall`), as native Lean calls `lean_mark_persistent` on the
result after the initializer (`emitDeclInit`): the walk marks what it
reaches persistent, so a later walk (a closed term's first evaluation,
`Runtime.markPersistent`) does not look into a reference the result holds.
It never waits: before `main` every task has run at once, and no promise
can be made. Generated once per constant. -/
def initPutFn (decl : Name) (slot : Nat) (vt : RR.Ty) : LowerM String := do
  let name := s!"l2r_init_put_{slot}"
  if ← hasFn name then return name
  let t ← lowerType (← toMonoTypeKeep (← getOtherDeclBaseType decl []))
  let (st, boxed) ← cellStorage t
  let v ← coerce (.var "v") vt t
  let (walk, x) ← match ← persistCall t (.var "x") with
    | some p => pure (#[("x", some t, v), ("p", some (RR.Ty.named "u64"), p)], RR.Expr.var "x")
    | none => pure (#[], v)
  let stored := if boxed then match st with | .named bn => RR.Expr.ctor bn none #[x] | _ => x else x
  let body : RR.Block := ⟨walk.push ("s", some st, .call "l2r_once_set" #[st] #[.atom (toString slot), stored]), .atom "0"⟩
  modify fun s => { s with fns := s.fns.push (.fn name #[("v", vt)] (.named "u64") body) }
  return name

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
  let errFn ← match startup.findSome? (fun | .ioUnit i | .init _ i => some i | .caf _ => none) with
    | none => pure (fnName errStr)
    | some inst => errStringFn errStr (← ioResultOf inst).1
  let failed (e : String) := s!"l2r_init_failed({errFn}({e}))"
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
      | .caf inst =>
        -- A constant whose code is one string literal has no function, and
        -- making it has no effect: its first read makes it (`litConsts`).
        unless (← read).litConsts.contains inst do
          code := s!"let caf{j} = {fnName inst}();\n" ++ code
      | .ioUnit inst =>
        let (t, ok, err, _, _) ← ioResultOf inst
        code := s!"match {fnName inst}(L2RUnit::u\{}) \{\n{t}::{ok}(v{j}) => \{\n{code}\n},\n{t}::{err}(e{j}) => \{ {failed s!"e{j}"} }\n}"
      | .init decl inst =>
        let (t, ok, err, field, _) ← ioResultOf inst
        let some slot := (← get).initSlots.find? decl | throwError "lean2rr: no slot for {decl}"
        let put ← initPutFn decl slot (field.getD RR.Ty.unit)
        code := s!"match {fnName inst}(L2RUnit::u\{}) \{\n{t}::{ok}(v{j}) => \{\nlet s{j} : u64 = {put}(v{j});\n{code}\n},\n{t}::{err}(e{j}) => \{ {failed s!"e{j}"} }\n}"
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
