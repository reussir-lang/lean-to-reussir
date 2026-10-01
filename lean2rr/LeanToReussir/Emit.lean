import Lean
import LeanToReussir.Lower
import LeanToReussir.SinkProj
import LeanToReussir.MonoRetype
import LeanToReussir.FloatLits
import LeanToReussir.Outline

/-!
# Program assembly

Lowers all mono declarations and assembles the `.rr` program: the runtime
prelude, generated types (including `Box`), functions, and the entry point
(translation plan §5.11). The entry point calls the translated `main` with
the argument list (if it takes one) and the world `()`, then reproduces
native Lean's process behaviour: exit with the returned code, or report an
uncaught exception and exit with 1.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Roots besides `main` that the entry point needs. -/
def entryRoots : Array Name := #[``IO.Error.toString]

/-- Whether a module belongs to the Lean toolchain (its constants are
evaluated lazily; see translation plan §5.12). -/
def isToolchainModule (m : Name) : Bool :=
  m.getRoot ∈ [`Init, `Std, `Lean, `Lake, `L2RShim]

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

/-- Lean's initializer order for the startup declarations `items` of one
module (translation plan §5.12). Native Lean initializes a module's
declarations in compilation order. A `def`/`instance` command is compiled
after it is elaborated, together with its `where`/`let rec` helpers: the
elaborator lists the helpers (those of later mutual members first, outer
before nested ones) and then the command's declarations, and compiles the
strongly connected components of their reference graph one by one, callees
first (Tarjan over that list, `addPreDefinitions`). The specializations
made while compiling a component come before its members, and an auxiliary
declaration made during elaboration (`c.unsafe_1`, `instInhabitedP.default`)
before the whole command. lean2rr sees the command through declaration
ranges: a helper's range lies inside its parent's, and the kernel's `all`
lists a recursive mutual block. Non-recursive members of a `mutual` block
are not recorded, so they are ordered as separate commands. Returns a sort
key per item. -/
partial def moduleStartupKeys (idx : Nat) (items : Array Name) : CoreM (Std.HashMap Name (Array Nat)) := do
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
  let rootOf (v : Name) : Name := blockOf (memberOf v).1
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
    let order := allOf r
    let blockIdx (v : Name) : Nat := (order.findIdx? (· == v)).getD order.length
    let mains := (vs.filter fun v => (memberOf v).1 == v).qsort fun a b =>
      lexLtNat ((posKey a).push (blockIdx a)) ((posKey b).push (blockIdx b))
    let memberIdx (v : Name) : Nat := (mains.findIdx? (· == (memberOf v).1)).getD 0
    let key (v : Name) : Array Nat :=
      #[mains.size - memberIdx v, (memberOf v).2] ++ posKey v
    let helpers := (vs.filter fun v => (memberOf v).1 != v).qsort fun a b =>
      lexLtNat (key a) (key b) || (key a == key b && natNameLt a b)
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
  for h : idx in [:env.header.moduleNames.size] do
    if isToolchainModule env.header.moduleNames[idx] then continue
    for d in baseExt.getModuleEntries env idx (level := .private) do
      let n := d.name
      unless d.value matches .code _ && d.params.isEmpty do continue
      if isIOUnitInitFn env n || (getInitFnNameFor? env n).isSome then continue
      byModule := byModule.insert idx ((byModule.getD idx #[]).push (.caf n, n))
  -- Ties: by name, numbers by value (`c._unsafe_4` before `c._unsafe_10`,
  -- Lean's order of the auxiliary declarations of one command; see also
  -- `specNo`). Lean's order of specializations depends on how its
  -- specializer recursed, which is not persisted.
  let mut out := #[]
  for idx in (byModule.toArray.map (·.1)).qsort (· < ·) do
    let its := byModule.getD idx #[]
    let keys ← moduleStartupKeys idx (its.map (·.2))
    let sorted := its.qsort fun (_, n1) (_, n2) =>
      let k1 := keys.getD n1 #[]
      let k2 := keys.getD n2 #[]
      lexLtNat k1 k2 || (k1 == k2 && natNameLt n1 n2)
    out := out ++ sorted.map (·.1)
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

/-- The entry point. `mainInst`/`errStr` are instance names; `startup` is
run first, in order (see `StartupItem`); an error in an initializer is
reported like an uncaught exception of `main`. -/
def lowerEntry (mainInst errStr : Name) (startup : Array StartupStep) : LowerM RR.Item := do
  let some mainDecl := (← read).decls.find? mainInst | throwError "lean2rr: no main"
  let (ps, _) := splitFnType mainDecl.type mainDecl.params.size
  let (outTy, okV, errV, okField) ← ioResultOf mainInst
  let exitCode := match okField with
    | some (.named "u32") => "l2r_exit(v)"
    | _ => "l2r_exit(0)"
  let takesArgs := ps.size == 2
  let mut pre := ""
  let mut argExpr := ""
  if takesArgs then
    let listTy ← lowerType ps[0]!
    let .named lt := listTy | throwError "lean2rr: bad main argument type"
    let some linfo := (← get).typeInfos[lt]? | throwError "lean2rr: bad main argument type"
    let nilV := (linfo.ctors.find? ``List.nil).map (·.variant) |>.getD "c_nil"
    let consV := (linfo.ctors.find? ``List.cons).map (·.variant) |>.getD "c_cons"
    pre := s!"fn l2r_mk_args(i : u64, acc : {lt}) -> {lt} \{\n    if i == 0 \{ acc } else \{ l2r_mk_args(i - 1, {lt}::{consV}\{l2r_argv(i - 1), acc}) }\n}\n\n"
    argExpr := s!"l2r_mk_args(l2r_argc(), {lt}::{nilV}\{}), "
  let uncaught (e : String) := s!"l2r_uncaught_exception({fnName errStr}({e}))"
  -- IO tasks are deferred once `main` starts (before, during
  -- initialization, Lean has no task manager and runs them at once). After
  -- `main` returns, whatever its result, the tasks still pending run, as
  -- `lean_finalize_task_manager` waits for them before the exception is
  -- reported or the process exits; they see Lean's shutdown flag (§5.14).
  -- (`l2r_run_pending_tasks` is generated at the end, `taskDispatchFns`.)
  let drain := "let sd : u64 = l2r_task_shutdown();\nlet pt : u64 = l2r_run_pending_tasks();\n"
  let mainCode := s!"let tm : u64 = l2r_task_manager_start();\nlet se : u64 = l2r_std_enter();\nlet r = {fnName mainInst}({argExpr}L2RUnit::u\{});\nlet sl : u64 = l2r_std_leave();\n{drain}match r \{\n{outTy}::{okV}(v) => \{ {exitCode} },\n{outTy}::{errV}(e) => \{ {uncaught "e"} }\n}"
  -- The startup chain, cut into functions of at most `chunk` steps: one
  -- chain of nested matches per program would be as deep as the program
  -- has initializers, and rrc's recursive lowering overflows its stack on
  -- a few thousand. Each function returns 0 once its steps succeeded; an
  -- error in an initializer is reported and exits (`l2r_init_failed`), so
  -- later initializers do not run. The chain ends by clearing
  -- `IO.initializing`.
  let chunk := 128
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
  let body := initFns ++
    s!"fn l2r_init_body() \{\nlet si : u64 = l2r_set_initializing(true);\n{"\n".intercalate calls.toList}\nl2r_init_done()\n}\n\n" ++
    s!"fn l2r_main_body() \{\n{mainCode}\n}\n"
  -- Like Lean's runtime: the module initializers run on the process's main
  -- thread (8 MiB stack) with `IO.initializing` true; then `main` runs on a
  -- thread with a big stack (1 GiB, `LEAN_STACK_SIZE_KB`,
  -- `LEAN_MAIN_USE_THREAD`). A stack overflow is reported as Lean does.
  -- `leanrt::rt::run_main2` implements all of this.
  -- The runtime writes its own diagnostics (index out of bounds, …) with
  -- `l2r_stderr_put` through this trampoline, called from Rust, so that
  -- Reussir sees no call cycle through the stream code.
  let entry := "extern \"C\" trampoline \"l2r_stderr_put_c\" = l2r_stderr_put;\n" ++
    "extern \"C\" trampoline \"l2r_init_body\" = l2r_init_body;\n" ++
    "extern \"C\" trampoline \"l2r_main_body\" = l2r_main_body;\n\n" ++
    "#[ffi(import)]\nfn l2r_init_done() -> unit [{ leanrt::rt::set_initializing(false) }];\n\n" ++
    "#[ffi(import)]\nfn l2r_init_failed(msg : LStr) -> u64 [{ leanrt::uncaught_exception(&msg) }];\n\n" ++
    "#[ffi(import)]\nfn l2r_run_main() [{ {\n" ++
    "    extern \"C\" { fn l2r_init_body(); fn l2r_main_body(); }\n" ++
    "    leanrt::rt::run_main2(|| unsafe { l2r_init_body() }, || unsafe { l2r_main_body() })\n} }];\n\n" ++
    "#[main]\npub fn lean_main_entry() { l2r_run_main() }\n"
  return .raw (pre ++ body ++ "\n" ++ entry)

/-- The externs a program calls: Lean name, C symbol, mono signature, and
type arguments for extern instances (development aid for the runtime). -/
def externReport (decls : Array (Decl .pure)) (keys : NameMap InstKey) : CoreM String := do
  let byName := decls.foldl (fun m d => m.insert d.name d) ({} : NameMap (Decl .pure))
  let mut seen : NameSet := {}
  let mut lines := #[]
  for d in decls do
    let .code c := d.value | continue
    for f in codeConsts c #[] do
      if seen.contains f then continue
      seen := seen.insert f
      let (orig, targs, sig) ← match byName.find? f with
        | some e =>
          match e.value with
          | .extern _ =>
            let k := keys.find? f
            pure (some ((k.map (·.decl)).getD f), (k.map (·.typeArgs)).getD #[], e.type)
          | _ => pure (none, #[], default)
        | none =>
          if (← getEnv).isConstructor f then pure (none, #[], default)
          else match ← getMonoDecl? f with
            | some e => pure (some f, #[], e.type)
            | none => pure (none, #[], default)
      if let some o := orig then
        let sym := (getExternNameFor (← getEnv) `c o).getD "?"
        let targsStr := if targs.isEmpty then "" else s!" @[{", ".intercalate (targs.toList.map toString)}]"
        lines := lines.push s!"{o}{targsStr}  [{sym}]  : {sig}"
  return "\n".intercalate (lines.qsort (· < ·)).toList ++ "\n"

/-- The generic functions of the prelude that are plain Reussir code over
values: not FFI imports, and no type application in their signature (a
parameter `RVec<T>` makes `T` an array storage type, as for
`lean_array_push<T>`). lean2rr instantiates them at the value types of the
extern's type arguments (see `lowerExternCall`). Name ↦ number of type
parameters. -/
def valueGenericPreludeFns (prelude : String) : Std.HashMap String Nat := Id.run do
  let mut out : Std.HashMap String Nat := {}
  let mut prev := ""
  for line in prelude.splitOn "\n" do
    if line.startsWith "fn " && prev != "#[ffi(import)]" then
      let rest := (line.drop 3).toString
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      let after := (rest.drop name.length).toString
      if after.startsWith "<" then
        let gens := ((after.drop 1).takeWhile (· != '>')).toString
        let sig := ((after.drop (gens.length + 2)).takeWhile (· != '{')).toString
        unless sig.contains '<' || sig.contains '[' do
          out := out.insert name (gens.splitOn ",").length
    unless line.all Char.isWhitespace do prev := line
  return out

/-- For the prelude functions of `valueGenericPreludeFns`: which parameters
are Reussir closures (a function value passed there is converted). -/
def valueGenericClosureParams (prelude : String) : Std.HashMap String (Array Bool) := Id.run do
  let mut out : Std.HashMap String (Array Bool) := {}
  for line in prelude.splitOn "\n" do
    if line.startsWith "fn " then
      let rest := (line.drop 3).toString
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      let params := ((rest.dropWhile (· != '(')).drop 1 |>.takeWhile (· != ')')).toString
      let ps := if params.trim.isEmpty then [] else params.splitOn ","
      out := out.insert name (ps.map (·.contains '-')).toArray
  return out

/-- Lower a whole program. -/
def lowerProgram (prelude : String) (mainInst errStr : Name) (startup : Array StartupStep) (decls : Array (Decl .pure))
    (keys : NameMap InstKey) : CoreM String := do
  let table ← programRelevance decls
  let roots := #[mainInst, errStr] ++ startup.map fun
    | .caf i | .ioUnit i | .init _ i => i
  let (decls, keys) ← retypeMono table decls keys roots
  -- Float literals become bit patterns (translation plan §5.12).
  let decls := foldFloatLitsDecls keys decls
  -- Function names the prelude defines (`fn NAME`).
  let preludeFns := (prelude.splitOn "fn ").foldl (init := ({} : Std.HashSet String)) fun acc chunk =>
    let name := chunk.takeWhile fun c => c.isAlphanum || c == '_'
    if name.isEmpty then acc else acc.insert name.toString
  -- Result types from the prelude's one-line signatures (`fn f(…) -> T …`).
  let preludeRets := prelude.splitOn "\n" |>.foldl (init := ({} : Std.HashMap String RR.Ty)) fun acc line =>
    let line := line.trimLeft
    let line := if line.startsWith "pub fn " then (line.drop 4).toString else line
    if !line.startsWith "fn " then acc else
    let name := ((line.drop 3).takeWhile fun c => c.isAlphanum || c == '_').toString
    match line.splitOn ") -> " with
    | _ :: rest@(_ :: _) =>
      let r := rest.getLast!
      let r := ((r.splitOn " [{").head!.splitOn " {").head!.trim
      match RR.parseTy r with
      | some t => acc.insert name t
      | none => acc
    | _ => acc
  -- Parameter types of the non-generic prelude functions (`fn f(a : T, …)`).
  let preludeParams := prelude.splitOn "\n" |>.foldl (init := ({} : Std.HashMap String (Array RR.Ty))) fun acc line =>
    let line := line.trimLeft
    let line := if line.startsWith "pub fn " then (line.drop 4).toString else line
    if !line.startsWith "fn " then acc else
    let rest := (line.drop 3).toString
    let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
    let rest := (rest.drop name.length).toString
    if !rest.startsWith "(" then acc else
    let inner := ((rest.drop 1).takeWhile (· != ')')).toString
    let parts := if inner.trim.isEmpty then [] else inner.splitOn ","
    match parts.mapM (fun p => match p.splitOn ":" with | [_, t] => RR.parseTy t | _ => none) with
    | some tys => acc.insert name tys.toArray
    | none => acc
  -- The `IO.Error` builders' instances (monomorphic, so keyed by declaration).
  let byDecl : NameMap Name := keys.foldl (init := {}) fun m inst k =>
    if k.typeArgs.isEmpty && k.dicts.isEmpty then m.insert k.decl inst else m
  let exports ← (exportMap.run' {config := {}} : CoreM _)
  let ioErrorBuilders := ioErrorBuilderSyms.map fun sym => (exports.get? sym).bind byDecl.find?
  let valueGenericFns := valueGenericPreludeFns prelude
  let valueGenericCls := valueGenericClosureParams prelude
  -- Closed terms referenced once, from a constant (the steps of an array
  -- literal: `_closed_k := push _closed_(k-1) e_k`).
  let mut uses : NameMap Nat := {}
  let mut fromFunction : NameSet := {}
  for d in decls do
    let .code c := d.value | continue
    for n in codeConsts c #[] do
      uses := uses.insert n (uses.getD n 0 + 1)
      unless d.params.isEmpty do fromFunction := fromFunction.insert n
  let isClosed (n : Name) : Bool := match n with
    | .str _ s => s.startsWith "_closed"
    | _ => false
  let chainConsts := decls.foldl (init := ({} : NameSet)) fun acc d =>
    if d.params.isEmpty && isClosed d.name && uses.getD d.name 0 == 1 && !fromFunction.contains d.name
      && !roots.contains d.name then acc.insert d.name else acc
  let ctx : LowerCtx := { table, decls := decls.foldl (fun m d => m.insert d.name d) {}, keys, preludeFns,
                          preludeRets, preludeParams, ioErrorBuilders, valueGenericFns, valueGenericCls,
                          chainConsts }
  let act : LowerM (Array RR.Item) := do
    -- `Box` always exists (with at least the unit variant, `box(0)`): types
    -- may mention it even when nothing is ever boxed.
    let _ ← boxVariant .unit
    -- Once-cells of `initialize` constants (read by `calleeOf`).
    for st in startup do
      if let .init decl _ := st then
        modify fun s => { s with initSlots := s.initSlots.insert decl s.cafSlots, cafSlots := s.cafSlots + 1 }
    for d in decls do lowerDecl d
    let entry ← lowerEntry mainInst errStr startup
    modify fun s => { s with fns := s.fns.push entry }
    -- Converters and application functions can need each other.
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    -- Only now is every use of the standard streams lowered (function
    -- values' targets included), so the diagnostics writer and the stream
    -- contexts know whether the program has stream cells.
    let put ← stderrPutFn
    modify fun s => { s with fns := s.fns.push put }
    let ctxFns ← stdContextFns
    modify fun s => { s with fns := s.fns ++ ctxFns }
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    -- Every task type is known now: the functions running queued tasks.
    let disp ← taskDispatchFns
    modify fun s => { s with fns := s.fns ++ disp }
    repeat
      finishUnboxFns
      unless ← finishFnValues do break
    return ← fnTypeItems
  let (fnItems, st) ← (act.run ctx).run {}
  let boxItem := RR.Item.enum boxName false (st.boxVariants.map fun (t, v) => (v, #[t]))
  -- Deep and long tail paths become chains of functions (rrc's analyses
  -- are superlinear in them; see `Outline`).
  let variants := Outline.variantTable (st.typeItems ++ fnItems |>.push boxItem) prelude
  let taken := st.fns.foldl (init := preludeFns) fun acc it => match it with
    | .fn n .. => acc.insert n
    | .raw t => (t.splitOn "fn ").foldl (init := acc) fun acc chunk =>
      let name := chunk.takeWhile fun c => c.isAlphanum || c == '_'
      if name.isEmpty then acc else acc.insert name.toString
    | _ => acc
  -- Projections sunk into the branches that use them (`SinkProj`), then
  -- oversized tail paths outlined (`Outline`).
  let fns := Outline.outlineFns {} variants taken (st.fns.map (·.sinkProj))
  let mut out := prelude ++ "\n// ---- generated types ----\n\n"
  for it in st.typeItems do out := out ++ it.render ++ "\n"
  for it in fnItems do out := out ++ it.render ++ "\n"
  out := out ++ boxItem.render ++ "\n"
  out := out ++ "// ---- generated functions ----\n\n"
  for f in fns do out := out ++ f.render ++ "\n"
  unless st.strLits.isEmpty do out := out ++ strLitTable st.strLits
  return out

end LeanToReussir
