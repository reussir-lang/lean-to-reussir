import Lean
open Lean Meta

/-!
Checks that every `@[export]` definition of lean2rr's shim (`L2RShim`) has
the type of the `@[extern]` declaration of the same C symbol: Lean pairs them by name only, and lean2rr compiles the definition
in place of the extern (`Mono.redirectTarget`). Run by `shim-types.sh`.
-/

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Lean}, {module := `Std}, {module := `L2RShim}] {}
    (loadExts := true) (level := .private)
  let check : MetaM UInt32 := do
    let mut exports : Std.HashMap String Name := {}
    for (n, _) in env.constants.toList do
      if let some s := getExportNameFor? env n then
        if (`L2RShim).isPrefixOf n then exports := exports.insert s.toString n
    let mut bad := 0
    let mut checked := 0
    for (n, ci) in env.constants.toList do
      unless isExtern env n do continue
      let some sym := getExternNameFor env `c n | continue
      let some d := exports[sym]? | continue
      let di ← getConstInfo d
      -- `@&` annotations are metadata in the types.
      let strip (t : Expr) := t.replace fun e => if e.isMData then some e.mdataExpr! else none
      let ok ← if ci.levelParams.length != di.levelParams.length then pure false else
        isDefEq (strip ci.type) ((strip di.type).instantiateLevelParams di.levelParams (ci.levelParams.map mkLevelParam))
      checked := checked + 1
      unless ok do
        bad := bad + 1
        IO.println s!"MISMATCH {sym}: extern {n} : {ci.type}\n  export {d} : {di.type}"
    IO.println s!"{checked} externs implemented by the shim checked, {bad} mismatches"
    return if bad == 0 then 0 else 1
  let (r, _) ← (check.run' {} {}).toIO { fileName := "<shim-types>", fileMap := default } { env }
  return r
