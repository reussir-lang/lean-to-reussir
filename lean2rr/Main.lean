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
  -- Stage 1: monomorphize from `main`, the entry point's roots and the
  -- startup items (constants, `initialize` actions).
  let items ← startupItems
  let (rootInsts, st) ← monomorphize (programRoots opts.root items)
  let header := s!"-- root instances: {rootInsts}; instances: {st.decls.size}, extern instances: {st.externs.size}, lcAny type arguments: {st.uniformArgs}\n"
  if stage == "inst" then return dumpDecls header (st.externs ++ st.decls)
  -- Stage 2: Lean's own mono pipeline, with the registry's edits.
  let decls ← runStage2 cfg.stage2 st.decls st.externs opts.check
  if stage == "externs" then return ← externReport decls st.keys
  if stage == "mono" then return dumpDecls header decls
  -- Stage 3: the types mono lost, recovered from the code the entry point
  -- reaches (`main`, the error printer, the startup steps).
  let mainInst := rootInsts[0]!
  let errStr := rootInsts[1]!
  let startup ← startupSteps items rootInsts st
  let roots := entryCallees mainInst errStr startup
  let table ← programRelevance decls
  let (decls, keys) ← retypeMono cfg.stage2 cfg.stage3 table decls st.keys roots
  if stage == "retyped" then return dumpDecls header decls
  -- The registry's passes over mono LCNF (`Opt/FloatLits`).
  let decls := cfg.monoPasses.foldl (fun ds pass => pass keys ds) decls
  -- Stage 4: lowering, with the registry's lowering hooks.
  let prelude ← match opts.prelude with
    | some p => IO.FS.readFile p
    | none => pure ""
  let prog ← lowerProgram cfg prelude table mainInst errStr startup roots decls keys
  -- The registry's passes over the generated functions, then `Outline`
  -- (core), and the program text.
  return prog.runRRPasses cfg |>.outline |>.render

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
