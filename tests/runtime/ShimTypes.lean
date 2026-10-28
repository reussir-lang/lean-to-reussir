import Lean
open Lean Meta

/-!
Checks that every `@[export]` definition of lean2rr's shim (`L2RShim`) has
the type of the `@[extern]` declaration of the same C symbol: Lean pairs them by name only, and lean2rr compiles the definition
in place of the extern (`Mono.redirectTarget`). The same for the shim's
overrides (`l2r_override_<f mangled>`, compiled in place of every call of `f`):
each has `f`'s type. Run by `shim-types.sh`.
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
    -- The shim's overrides: `@[export l2r_override_<f mangled>]` is compiled
    -- in place of every call of `f` (`Mono.redirectTarget`, `overrideMap`),
    -- so it must have `f`'s type too.
    let overrideSyms := exports.toList.filter (·.1.startsWith "l2r_override_")
    let mut overrides := 0
    if !overrideSyms.isEmpty then
      for (n, ci) in env.constants.toList do
        let sym := n.mangle "l2r_override_"
        let some d := exports[sym]? | continue
        let di ← getConstInfo d
        let strip (t : Expr) := t.replace fun e => if e.isMData then some e.mdataExpr! else none
        let ok ← if ci.levelParams.length != di.levelParams.length then pure false else
          isDefEq (strip ci.type) ((strip di.type).instantiateLevelParams di.levelParams (ci.levelParams.map mkLevelParam))
        overrides := overrides + 1
        unless ok do
          bad := bad + 1
          IO.println s!"MISMATCH {sym}: {n} : {ci.type}\n  override {d} : {di.type}"
      if overrideSyms.length != overrides then
        bad := bad + 1
        IO.println s!"{overrideSyms.length - overrides} override(s) of the shim name no declaration"
    IO.println s!"{checked} externs implemented by the shim and {overrides} overrides checked, {bad} mismatches"
    return if bad == 0 then 0 else 1
  let (r, _) ← (check.run' {} {}).toIO { fileName := "<shim-types>", fileMap := default } { env }
  return r
