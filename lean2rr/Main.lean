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
  "usage: lean2rr <Module> [--root NAME] [--stats] [--emit base|inst|mono|retyped|rr] [--prelude FILE] [--no-check]\n" ++
  "               [--disable-opt NAME]... [--enable-opt NAME]... [-o FILE]\n" ++
  "       lean2rr --list-opts\n" ++
  "  Modules are found via LEAN_PATH; run inside `lake env` for Lake projects."

partial def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => .ok o
  | "--root" :: r :: rest, o => parseArgs rest { o with root := r.toName }
  | "--emit" :: e :: rest, o =>
    if e ∈ ["base", "inst", "mono", "retyped", "rr", "externs"] then parseArgs rest { o with emit := some e }
    else .error s!"unknown --emit stage '{e}' (supported: base, inst, mono, retyped, rr)"
  | "--prelude" :: f :: rest, o => parseArgs rest { o with prelude := some f }
  | "--no-check" :: rest, o => parseArgs rest { o with check := false }
  | "--stats" :: rest, o => parseArgs rest { o with stats := true }
  | "--disable-opt" :: n :: rest, o => parseArgs rest { o with disabled := o.disabled.push n }
  | "--enable-opt" :: n :: rest, o => parseArgs rest { o with enabled := o.enabled.push n }
  | "--list-opts" :: rest, o => parseArgs rest { o with listOpts := true }
  | "-o" :: f :: rest, o => parseArgs rest { o with output := some f }
  | a :: rest, o =>
    if a.startsWith "-" then .error s!"unknown option '{a}'"
    else if o.module.isSome then .error s!"unexpected argument '{a}'"
    else parseArgs rest { o with module := some a.toName }

/-- Pretty-print every reachable declaration as base-phase LCNF. -/
def emitBase (prog : Program) : CoreM String := do
  let mut out := ""
  for decl in prog.decls ++ prog.externs do
    out := out ++ toString (← ppDecl' decl .base) ++ "\n"
  return out

/-- Mono declarations, one per line (`--emit inst|mono|retyped`). -/
def dumpDecls (header : String) (decls : Array (Decl .pure)) : String :=
  decls.foldl (init := header) fun out d => out ++ fmtDecl d ++ "\n"

/-- Stages 1–4 (translation plan §1), stopping after the stage that `--emit
stage` prints. -/
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
  if stage == "retyped" then
    -- Stage 3 alone (`lowerProgram` runs it itself).
    let (decls, _) ← retypeMono cfg.stage2 (← programRelevance decls) decls st.keys rootInsts
    return dumpDecls header decls
  -- Stages 3 and 4: retyping, the registry's optional passes, lowering, and
  -- the program text (prelude, types, functions, startup chain, entry point).
  let prelude ← match opts.prelude with
    | some p => IO.FS.readFile p
    | none => pure ""
  let startup ← startupSteps items rootInsts st
  lowerProgram cfg prelude rootInsts[0]! rootInsts[1]! startup decls st.keys

def run (opts : CliOptions) (cfg : PassConfig) (module : Name) : IO UInt32 := do
  let env ← loadEnvironment #[module]
  let text ← runCoreM env do
    -- What `main` reaches (`--emit base`, `--stats`).
    let prog ← collect opts.root
    let mut text := ""
    match opts.emit with
    | some "base" => text := ← emitBase prog
    | some stage => text := ← pipeline opts cfg stage
    | none => pure ()
    if opts.stats then text := text ++ (← statsReport prog)
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
4 GiB, for Lean's passes on deep terms) sizes every thread Lean's runtime
creates, and four such reservations do not fit an address-space limit of
16 GB. lean2rr runs everything on its main thread; the workers only serve
the library's own tasks. -/
def workerStackSize : USize := 64 * 1024 * 1024

def main (args : List String) : IO UInt32 := do
  setThreadStackSize workerStackSize
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"lean2rr: {e}\n{usage}"
    return 2
  | .ok opts =>
    if opts.listOpts then
      IO.print Opt.listing
      return 0
    let some module := opts.module
      | IO.eprintln usage
        return 2
    -- The registry's passes, minus `--disable-opt`, plus `--enable-opt`.
    let cfg ← match Opt.config opts.disabled opts.enabled with
      | .ok cfg => pure cfg
      | .error e =>
        IO.eprintln s!"lean2rr: {e}"
        return 2
    try run opts cfg module
    catch e =>
      IO.eprintln s!"lean2rr: {e}"
      return 1
