import LeanToReussir

open Lean Compiler LCNF LeanToReussir

structure CliOptions where
  module : Option Name := none
  root : Name := `main
  emit : Option String := none
  stats : Bool := false
  check : Bool := true
  prelude : Option System.FilePath := none
  output : Option System.FilePath := none
  /-- Optimizations turned off (`--disable-opt`) or on (`--enable-opt`). -/
  disabled : Array String := #[]
  enabled : Array String := #[]
  listOpts : Bool := false

def usage : String :=
  "usage: lean2rr <Module> [--root NAME] [--stats] [--emit base|inst|mono|externs|retyped|rr] [--prelude FILE]\n" ++
  "               [--no-check] [--disable-opt NAME]... [--enable-opt NAME]... [-o FILE]\n" ++
  "       lean2rr --list-opts\n" ++
  "  Modules are found via LEAN_PATH; run inside `lake env` for Lake projects. A module name\n" ++
  "  may contain non-identifier characters (`rbtree-zipper`) or be written `«rbtree-zipper»`."

/-- A module name as given on the command line: components separated by
dots, each written as is (any characters but `.`: the module that
`lean -o rbtree-zipper.olean rbtree-zipper.lean` makes is `rbtree-zipper`)
or between `«` and `»`, as Lean prints names (`«rbtree-zipper»`, which may
contain dots). -/
def parseModuleName (s : String) : Except String Name := do
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut quoted := false
  for c in s.toList do
    if quoted then
      if c == '»' then quoted := false else cur := cur.push c
    else if c == '«' then quoted := true
    else if c == '.' then
      parts := parts.push cur
      cur := ""
    else cur := cur.push c
  if quoted then throw s!"unterminated « in module name '{s}'"
  parts := parts.push cur
  if parts.any (·.isEmpty) then throw s!"bad module name '{s}'"
  return parts.foldl Name.mkStr .anonymous

partial def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => .ok o
  | "--root" :: r :: rest, o => parseArgs rest { o with root := r.toName }
  | "--emit" :: e :: rest, o =>
    if e ∈ ["base", "inst", "mono", "externs", "retyped", "rr"] then parseArgs rest { o with emit := some e }
    else .error s!"unknown --emit stage '{e}' (supported: base, inst, mono, externs, retyped, rr)"
  | "--prelude" :: f :: rest, o => parseArgs rest { o with prelude := some f }
  | "--no-check" :: rest, o => parseArgs rest { o with check := false }
  | "--stats" :: rest, o => parseArgs rest { o with stats := true }
  | "--disable-opt" :: n :: rest, o => parseArgs rest { o with disabled := o.disabled.push n }
  | "--enable-opt" :: n :: rest, o => parseArgs rest { o with enabled := o.enabled.push n }
  | "--list-opts" :: rest, o => parseArgs rest { o with listOpts := true }
  | "-o" :: f :: rest, o => parseArgs rest { o with output := some f }
  | a :: rest, o =>
    -- An option that takes an argument gets here only without one.
    if a ∈ ["--root", "--emit", "--prelude", "--disable-opt", "--enable-opt", "-o"] then
      .error s!"option '{a}' needs an argument"
    else if a.startsWith "-" then .error s!"unknown option '{a}'"
    else if o.module.isSome then .error s!"unexpected argument '{a}'"
    else do
      let m ← parseModuleName a
      parseArgs rest { o with module := some m }

/-- Pretty-print every reachable declaration as base-phase LCNF. -/
def emitBase (prog : Program) : CoreM String := do
  let mut out := ""
  for decl in prog.decls ++ prog.externs do
    out := out ++ toString (← ppDecl' decl .base) ++ "\n"
  return out

/-- Mono declarations, one per line (`--emit inst|mono|retyped`). -/
def dumpDecls (header : String) (decls : Array (Decl .pure)) : String :=
  decls.foldl (init := header) fun out d => out ++ fmtDecl d ++ "\n"

/-- The pipeline (translation plan §1), stopping after the stage that
`--emit stage` prints. -/
def pipeline (opts : CliOptions) (cfg : PassConfig) (stage : String) : CoreM String := do
  let prelude ← match opts.prelude with
    | some p => IO.FS.readFile p
    | none => pure ""
  -- Stage 1: monomorphize from `main`, the entry point's roots and the
  -- startup items (the program's constants and `initialize` actions, and
  -- the `initialize` declarations of Lean's library, in Lean's module
  -- order). The prelude's functions tell which symbols lean2rr's runtime
  -- implements (the message of a refused extern, `Mono.computeExternRoute`).
  let (leanInit, items) ← startupItems opts.root
  let (rootInsts, st) ← monomorphize (programRoots opts.root leanInit items)
    { preludeFns := ← preludeFnDeclsM prelude }
  -- The externs of the program that run their Lean definition (natively
  -- their C code runs): a note of the build, on lean2rr's stderr (the
  -- program's output is not affected).
  unless st.externBodies.isEmpty do
    let lines := st.externBodies.map fun (sym, d) =>
      let native := match st.externBodiesOfRuntime.find? d with
        | some what => s!" (natively {what})"
        | none => ""
      s!"  {sym}  (extern of {d}){native}"
    IO.eprintln s!"lean2rr: note: {st.externBodies.size} extern(s) of the program run their Lean \
      definition, not their C code (lean2rr compiles Lean code, plus Lean's runtime library):\n\
      {"\n".intercalate lines.toList}"
  -- Of those, the ones whose C symbol natively runs a function lean2rr has
  -- (an `@[export]` definition, a function of Lean's runtime), but whose
  -- binding fails: a stub definition then differs from native.
  for (d, whys) in st.externBindingWarnings do
    IO.eprintln s!"lean2rr: warning: {d} runs its Lean definition, where native Lean calls the \
      function its C symbol is linked to: {"; ".intercalate whys.toList}"
  let header := s!"-- root instances: {rootInsts}; instances: {st.decls.size}, extern instances: {st.externs.size}, lcAny type arguments: {st.uniformArgs}\n"
  if stage == "inst" then return dumpDecls header (st.externs ++ st.decls)
  -- A parameter of type `lcErased` that receives data (a join point after a
  -- `match` whose arms give a type or proof and data: a Lean compiler bug,
  -- plan §10) gets the type `lcAny`, before `toMono` erases the arguments
  -- at such parameters of declarations (`ErasedData`).
  let insts := retypeErasedData st.decls
  -- Stage 2: Lean's own mono pipeline, with the registry's edits.
  let decls ← runStage2 cfg.stage2 insts st.externs st.keys opts.check
  -- Again on Stage 2's output: a join point Lean's mono passes made.
  let decls := retypeErasedData decls
  if stage == "externs" then return ← externReport decls st.keys
  if stage == "mono" then return dumpDecls header decls
  -- Stage 3: the types mono lost, recovered from the code the entry point
  -- reaches (`main`, the error printer, the startup steps).
  let mainInst := rootInsts[0]!
  let errStr := rootInsts[1]!
  let startup ← startupSteps leanInit items rootInsts st
  let roots := entryCallees mainInst errStr startup
  let table ← programRelevance decls
  let decls ← retypeMono table decls st.keys roots
  let keys := st.keys
  if stage == "retyped" then return dumpDecls header decls
  -- The registry's passes over mono LCNF (`Opt/FloatLits`).
  let decls := cfg.monoPasses.foldl (fun ds pass => pass keys ds) decls
  -- Stage 4: lowering, with the registry's lowering hooks.
  let prog ← lowerProgram cfg prelude mainInst errStr startup roots decls keys
    (st.externRoutes.foldl (init := {}) fun m f r => match r with
      | .refused why => m.insert f why
      | _ => m)
  -- `Outline` (core; first, so that the passes after it see bounded
  -- functions), the registry's passes over the generated functions, and
  -- the program text. `L2R_NO_OUTLINE` and
  -- `L2R_NO_INLINE_ANCHORS` turn the two build-time workarounds off, for
  -- the repros of Reussir issues 16, 17 and 20, costs
  -- (reussir-bugs/repros/run.sh).
  let prog := if (← IO.getEnv "L2R_NO_OUTLINE").isSome then prog else prog.outline
  let prog := if (← IO.getEnv "L2R_NO_INLINE_ANCHORS").isSome then { prog with anchored := {} } else prog
  return prog.runRRPasses cfg |>.render

def run (opts : CliOptions) (cfg : PassConfig) (module : Name) : IO UInt32 := do
  let env ← loadEnvironment #[module]
  let text ← runCoreM env do
    let mut text := ""
    -- What `main` reaches, for `--emit base` and `--stats` only.
    let prog? ← if opts.emit == some "base" || opts.stats then some <$> collect opts.root else pure none
    match opts.emit, prog? with
    | some "base", some prog => text := ← emitBase prog
    | some stage, _ => text := ← pipeline opts cfg stage
    | none, _ => pure ()
    if let (true, some prog) := (opts.stats, prog?) then text := text ++ (← statsReport prog)
    return text
  match opts.output with
  | some path => IO.FS.writeFile path text
  | none => IO.print text
  return 0

/-- The stack size of the threads Lean's runtime creates from now on
(`Lean.Internal.setThreadStackSize`). -/
@[extern "lean_internal_set_thread_stack_size"]
opaque setThreadStackSize (sz : USize) : BaseIO Unit

/-- The stack of the threads Lean's runtime starts besides the one running
`main` (its task workers): `LEAN_STACK_SIZE_KB` (which the driver sets to
1 GiB, for Lean's passes on deep terms) sizes every thread Lean's runtime
creates, and such reservations add up against an address-space limit
(`ulimit -v`). lean2rr runs everything on its main thread; the workers only serve
the library's own tasks. -/
def workerStackSize : USize := 64 * 1024 * 1024

def main (args : List String) : IO UInt32 := do
  setThreadStackSize workerStackSize
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"lean2rr: {e}\n{usage}"
    return 2
  | .ok opts =>
    -- The registry's passes, minus `--disable-opt`, plus `--enable-opt`
    -- (the names are checked first, also for `--list-opts`).
    let cfg ← match Opt.config opts.disabled opts.enabled with
      | .ok cfg => pure cfg
      | .error e =>
        IO.eprintln s!"lean2rr: {e}"
        return 2
    if opts.listOpts then
      IO.print Opt.listing
      return 0
    let some module := opts.module
      | IO.eprintln usage
        return 2
    try run opts cfg module
    catch e =>
      IO.eprintln s!"lean2rr: {e}"
      return 1
