import Lean
import LeanToReussir.Collect
import LeanToReussir.Relevance
import LeanToReussir.Specialize

/-!
# Feasibility statistics (`--stats`)

M0 asks one question of every program: can the typed translation handle it
without falling back to the uniform `Box`? The signals that matter, per
reachable declaration:

* type parameters, and among them higher-kinded ones (`m : Type → Type`) —
  these must be instantiated by lean2rr's own specializer;
* instance parameters — dictionaries, which must be constant-folded when the
  class has polymorphic methods (`Monad`, `ForIn`, …);
* applications of a local variable to type arguments — calls of polymorphic
  methods projected out of a dictionary, or of polymorphic closures; these
  only become first-order if the dictionary is statically known;
* `lcAny` in a relevant position of a type — a value whose type Lean itself
  could not express (existentials, `unsafeCast`, types computed from values);
  `lcAny` in phantom positions (`EST.Out ε lcAny α`) is harmless.

The dry-run specializer then instantiates everything reachable from the root
and counts what survives instantiation: this is the real feasibility signal.
-/

namespace LeanToReussir
open Lean Compiler LCNF

structure DeclInfo where
  name : Name
  params : Nat
  typeParams : Nat
  hktParams : Nat
  /-- Classes of the instance parameters. -/
  instClasses : Array Name
  /-- Number of `.fvar f args` applications with at least one type argument. -/
  polyFVarApps : Nat
  usesAny : Bool
  size : Nat

/-- Number of local-variable applications that pass a type argument. -/
partial def countPolyFVarApps : Code .pure → Nat
  | .let d k =>
    let here := match d.value with
      | .fvar _ args => if args.any (· matches .type ..) then 1 else 0
      | _ => 0
    here + countPolyFVarApps k
  | .fun d k _ | .jp d k => countPolyFVarApps d.value + countPolyFVarApps k
  | .cases c => c.alts.foldl (fun n alt => n + countPolyFVarApps alt.getCode) 0
  | _ => 0

def analyzeDecl (table : RelevanceTable) (decl : Decl .pure) : CoreM DeclInfo := do
  let typeParams := decl.params.filter (isTypeFormerType ·.type)
  let hktParams := typeParams.filter fun p => p.type.headBeta.isForall
  let mut instClasses := #[]
  for p in decl.params do
    if let some cls ← isClass? p.type then
      instClasses := instClasses.push cls
  let polyFVarApps := match decl.value with
    | .code c => countPolyFVarApps c
    | .extern _ => 0
  return {
    name := decl.name
    params := decl.params.size
    typeParams := typeParams.size
    hktParams := hktParams.size
    instClasses, polyFVarApps
    usesAny := foldDeclTypes (fun e b => b || hasRelevantAny table e) decl false
    size := decl.size
  }

private def section_ (title : String) (items : Array String) : String :=
  if items.isEmpty then s!"{title}: none\n"
  else s!"{title} ({items.size}):\n" ++ String.join (items.toList.map (s!"  {·}\n"))

/-- Human-readable feasibility report for a collected program. -/
def statsReport (prog : Program) : CoreM String := do
  let (table, existential) ← Meta.MetaM.run' <| computeRelevance prog.inductives.toArray
  let infos ← prog.decls.mapM (analyzeDecl table)
  let cafs := infos.filter (·.params == 0)
  let poly := infos.filter (·.typeParams > 0)
  let hkt := infos.filter (·.hktParams > 0)
  let withInst := infos.filter (!·.instClasses.isEmpty)
  let polyApps := infos.filter (·.polyFVarApps > 0)
  let anyDecls := infos.filter (·.usesAny)
  let classes := withInst.foldl (fun s i => i.instClasses.foldl NameSet.insert s) {}
  let totalSize := infos.foldl (· + ·.size) 0
  let mut out := s!"root: {prog.root}\n"
  out := out ++ s!"reachable code decls: {infos.size} (total LCNF size {totalSize}), CAFs (0 params): {cafs.size}\n"
  out := out ++ s!"externs: {prog.externs.size}, constructors: {prog.ctors.size}, inductive types: {prog.inductives.size}\n"
  out := out ++ s!"polymorphic decls: {poly.size}, higher-kinded: {hkt.size}, with instance params: {withInst.size}\n"
  out := out ++ s!"decls with polymorphic local applications: {polyApps.size} ({polyApps.foldl (· + ·.polyFVarApps) 0} sites)\n"
  out := out ++ s!"decls with lcAny in a relevant position: {anyDecls.size}\n"
  out := out ++ s!"inductives with existential fields: {existential.size}\n"
  out := out ++ s!"missing: {prog.missing.size}\n"
  let spec ← specializeDryRun prog table
  let byDecl := spec.instances.foldl (init := ({} : NameMap Nat)) fun m i => m.insert i.decl ((m.getD i.decl 0) + 1)
  let multi := byDecl.foldl (init := #[]) fun acc n c => if c > 1 then acc.push (n, c) else acc
  let multi := multi.qsort (fun a b => a.2 > b.2)
  out := out ++ s!"\n== specialization (dry run)\n"
  out := out ++ s!"instances: {spec.instances.size} of {byDecl.size} decls{if spec.truncated then " (TRUNCATED: instance cap hit)" else ""}\n"
  out := out ++ s!"extern instances: {spec.externInstances.size}\n"
  out := out ++ s!"polymorphic local functions: {spec.polyLocalFuns}\n"
  out := out ++ s!"dictionary method calls: {spec.dictCalls} (statically unresolved: {spec.dynamicDictCalls.size})\n"
  out := out ++ s!"non-ground sites: {spec.nonGround.size}, relevant-lcAny sites: {spec.anySites.size}\n\n"
  out := out ++ section_ "decls with several instances" (multi.map fun (n, c) => s!"{n}: {c}")
  out := out ++ section_ "unresolved dictionary calls" spec.dynamicDictCalls
  out := out ++ section_ "non-ground sites" spec.nonGround
  out := out ++ section_ "relevant-lcAny sites" spec.anySites
  out := out ++ section_ "extern instances" (spec.externInstances.map (·.describe))
  out := out ++ section_ "inductives with existential fields" (existential.toArray.map toString)
  out := out ++ "\n"
  out := out ++ section_ "higher-kinded decls" (hkt.map fun i => s!"{i.name} (type params {i.typeParams}, hkt {i.hktParams})")
  out := out ++ section_ "instance classes taken as params" (classes.toArray.map toString)
  out := out ++ section_ "polymorphic local applications" (polyApps.map fun i => s!"{i.name}: {i.polyFVarApps}")
  out := out ++ section_ "relevant-lcAny decls" (anyDecls.map (toString ·.name))
  out := out ++ section_ "missing" (prog.missing.map fun (n, src) => s!"{n} (from {src})")
  out := out ++ section_ "externs" (prog.externs.map (toString ·.name))
  out := out ++ section_ "inductive types" (prog.inductives.toArray.map toString)
  return out

end LeanToReussir
