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

def usage : String :=
  "usage: lean2rr <Module> [--root NAME] [--stats] [--emit base|inst|mono|rr] [--prelude FILE] [--no-check] [-o FILE]\n" ++
  "  Modules are found via LEAN_PATH; run inside `lake env` for Lake projects."

partial def parseArgs : List String → CliOptions → Except String CliOptions
  | [], o => .ok o
  | "--root" :: r :: rest, o => parseArgs rest { o with root := r.toName }
  | "--emit" :: e :: rest, o =>
    if e ∈ ["base", "inst", "mono", "rr", "externs"] then parseArgs rest { o with emit := some e }
    else .error s!"unknown --emit stage '{e}' (supported: base, inst, mono, rr)"
  | "--prelude" :: f :: rest, o => parseArgs rest { o with prelude := some f }
  | "--no-check" :: rest, o => parseArgs rest { o with check := false }
  | "--stats" :: rest, o => parseArgs rest { o with stats := true }
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

def run (opts : CliOptions) (module : Name) : IO UInt32 := do
  let env ← loadEnvironment #[module]
  let text ← runCoreM env do
    let prog ← collect opts.root
    let mut text := ""
    if opts.emit == some "base" then text := text ++ (← emitBase prog)
    if opts.emit == some "inst" || opts.emit == some "mono" || opts.emit == some "rr" || opts.emit == some "externs" then
      let (rootInsts, st) ← monomorphize (#[opts.root] ++ entryRoots)
      let header := s!"-- root instances: {rootInsts}; instances: {st.decls.size}, extern instances: {st.externs.size}, lcAny type arguments: {st.uniformArgs}\n"
      if opts.emit == some "inst" then
        text := text ++ header
        for d in st.externs ++ st.decls do text := text ++ fmtDecl d ++ "\n"
      else
        let decls ← runStage2 st.decls st.externs opts.check
        if opts.emit == some "externs" then
          text := text ++ (← externReport decls st.keys)
        else if opts.emit == some "mono" then
          text := text ++ header
          for d in decls do text := text ++ fmtDecl d ++ "\n"
        else
          let prelude ← match opts.prelude with
            | some p => IO.FS.readFile p
            | none => pure ""
          text := text ++ (← lowerProgram prelude rootInsts[0]! rootInsts[1]! decls st.keys)
    if opts.stats then text := text ++ (← statsReport prog)
    return text
  match opts.output with
  | some path => IO.FS.writeFile path text
  | none => IO.print text
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"lean2rr: {e}\n{usage}"
    return 2
  | .ok { module := none, .. } =>
    IO.eprintln usage
    return 2
  | .ok opts@{ module := some module, .. } =>
    try run opts module
    catch e =>
      IO.eprintln s!"lean2rr: {e}"
      return 1
