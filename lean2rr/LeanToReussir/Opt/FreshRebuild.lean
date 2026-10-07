import Lean
import LeanToReussir.PassConfig

/-!
# Returned matched values rebuilt (optimization `fresh-rebuild`)

Lean's `simp` replaces a constructor rebuilt from a match's fields by the
matched value itself: `match r with | .error e => .error e | .ok a => …`
becomes `| .error _ => r`. That is the error arm of every `ExceptT`,
`Option` and `EStateM` bind. lean2rr returns the value itself, as native
Lean does (translation plan §5.5): a shared value rebuilt is a copy
(allocated; a value that a lookup returns would be copied at every call).
But the matched value then stays live across the match, so Reussir cannot
reuse its cell for what the other arms build: each bind's success path
allocates the new result and frees the old one (the classic
MonadicInterp: 12% of its time).

Where no copy is likely, the arm returns the constructor rebuilt from its
fields, an equal value (identity and sharing, which alone tell the two
apart, are not preserved: plan §9), so every arm consumes the matched
cell and Reussir reuses it (for the rebuilt one too: the same cell comes
back when it was unique). Only:
- when the matched value is freshly built: bound in the same function to a
  constructor application, or to a full call of a declaration all of whose
  results are freshly built (`freshDecls`: each return is such a value,
  also through join points; computed once per program, recursion assumed
  fresh until shown otherwise). A parameter, a field, a constant, an
  extern's or a function value's result (a node that a lookup returns, an
  array element) is returned itself;
- when the arm binds every field and uses the matched value only by
  returning it (`onlyReturned`), in an enum matched at its own type.

Without the pass every such arm returns the matched value itself.

Example: `eval` of an interpreter in `ExceptT String (StateM σ)` matches
the result `r` of a recursive call; `eval`'s results are all constructor
applications or such results, so `| .error _ => r` returns
`ok{Prod{error{e}, s}}` rebuilt, and the `ok` arm reuses `r`'s cells.
-/

namespace LeanToReussir
open Lean Compiler LCNF

namespace Opt.FreshRebuild

/-- Whether `x` occurs in `c` only as a returned value (`return x`). -/
partial def onlyReturned (x : FVarId) (c : Code .pure) : Bool :=
  let inArg : Arg .pure → Bool := fun | .fvar y => y == x | _ => false
  let inValue : LetValue .pure → Bool := fun
    | .fvar f args => f == x || args.any inArg
    | .const _ _ args _ => args.any inArg
    | .proj _ _ y _ => y == x
    | _ => false
  match c with
  | .let d k => !inValue d.value && onlyReturned x k
  | .fun d k _ | .jp d k => onlyReturned x d.value && onlyReturned x k
  | .jmp _ args => !args.any inArg
  | .cases cs => cs.discr != x && cs.alts.all (onlyReturned x ·.getCode)
  | .return _ | .unreach _ => true

/-- What a declaration's results are made of: its variables bound to an
application of a constant (the constant, the number of arguments), its
jumps, its join points' parameters, its returned variables, and the
constants it applies. A local function's returns are its own, not the
declaration's. -/
structure BodyFacts where
  apps : Std.HashMap FVarId (Name × Nat) := {}
  jumps : Array (FVarId × Array (Arg .pure)) := #[]
  jpParams : Std.HashMap FVarId (Array FVarId) := {}
  returns : Array FVarId := #[]
  calls : Std.HashSet Name := {}

partial def collect (c : Code .pure) (f : BodyFacts) : BodyFacts :=
  match c with
  | .let d k =>
    let f := match d.value with
      | .const g _ args _ =>
        { f with apps := if args.isEmpty then f.apps else f.apps.insert d.fvarId (g, args.size),
                 calls := f.calls.insert g }
      | _ => f
    collect k f
  | .jp d k => collect k (collect d.value { f with jpParams := f.jpParams.insert d.fvarId (d.params.map (·.fvarId)) })
  | .fun _ k _ => collect k f
  | .jmp j args => { f with jumps := f.jumps.push (j, args) }
  | .cases cs => cs.alts.foldl (fun f a => collect a.getCode f) f
  | .return x => { f with returns := f.returns.push x }
  | .unreach _ => f

def isCtor (env : Environment) (keys : NameMap InstKey) (g : Name) : Bool :=
  match env.find? ((keys.find? g).map (·.decl) |>.getD g) with
  | some (.ctorInfo _) => true
  | _ => false

/-- Whether an application of constant `g` to `n` arguments builds a fresh
value, given the declarations `fresh` assumed to return fresh values. -/
def freshApp (env : Environment) (keys : NameMap InstKey) (decls : NameMap (Decl .pure))
    (fresh : Std.HashSet Name) (g : Name) (n : Nat) : Bool :=
  isCtor env keys g || (fresh.contains g && (decls.find? g).any (·.params.size == n))

/-- Whether every return of a body is a fresh value (join points'
parameters: fresh unless a jump passes another value). -/
def bodyFresh (env : Environment) (keys : NameMap InstKey) (decls : NameMap (Decl .pure))
    (fresh : Std.HashSet Name) (f : BodyFacts) : Bool := Id.run do
  let params : Std.HashSet FVarId := f.jpParams.fold (init := {}) fun s _ ps => ps.foldl (·.insert ·) s
  let mut bad : Std.HashSet FVarId := {}
  let isFresh (bad : Std.HashSet FVarId) (x : FVarId) : Bool :=
    match f.apps[x]? with
    | some (g, n) => freshApp env keys decls fresh g n
    | none => params.contains x && !bad.contains x
  let mut changed := true
  while changed do
    changed := false
    for (j, args) in f.jumps do
      let some ps := f.jpParams[j]? | continue
      for (p, a) in ps.zip args do
        let ok := match a with | .fvar x => isFresh bad x | _ => true
        if !ok && !bad.contains p then
          bad := bad.insert p
          changed := true
  return f.returns.all (isFresh bad)

/-- The declarations all of whose results are freshly built (see the
module comment): every declaration with code is assumed so, and those with
a return that is not are taken out, rechecking their callers. -/
def freshDecls (env : Environment) (keys : NameMap InstKey) (decls : NameMap (Decl .pure)) :
    Std.HashSet Name := Id.run do
  let mut facts : Std.HashMap Name BodyFacts := {}
  let mut callers : Std.HashMap Name (Array Name) := {}
  let mut fresh : Std.HashSet Name := {}
  for (n, d) in decls.toList do
    if let .code c := d.value then
      let f := collect c {}
      facts := facts.insert n f
      fresh := fresh.insert n
      for g in f.calls do
        callers := callers.insert g ((callers.getD g #[]).push n)
  let mut work := fresh.toList
  while true do
    let w :: rest := work | break
    work := rest
    if fresh.contains w then
      if let some f := facts[w]? then
        if !bodyFresh env keys decls fresh f then
          fresh := fresh.erase w
          work := (callers.getD w #[]).toList ++ work
  return fresh

/-- `freshDecls` of the program, computed on first use. -/
structure FreshDecls where
  decls : Std.HashSet Name

deriving instance TypeName for FreshDecls

def key : Name := `freshRebuild

def freshDeclsCached : LowerM (Std.HashSet Name) := do
  if let some d := ((← get).ext.find? key).bind (·.get? FreshDecls) then return d.decls
  let ctx ← read
  let r := freshDecls (← getEnv) ctx.keys ctx.decls
  modify fun s => { s with ext := s.ext.insert key (.mk ({ decls := r } : FreshDecls)) }
  return r

/-- The fields of an enum alternative (`LowerHooks.enumFields`): when the
alternative only returns the freshly built matched value, every field
stays bound and the value is returned rebuilt from them
(`CodeCtx.rebuild`). -/
def enumFields (prev : CodeCtx → CasesArm → Array (Option String) →
      LowerM (Array (Option String) × CodeCtx))
    (ctx : CodeCtx) (arm : CasesArm) (binders : Array (Option String)) :
    LowerM (Array (Option String) × CodeCtx) := do
  if !arm.view && arm.shared &&
      !binders.isEmpty && binders.all Option.isSome then
    if let some (g, n) := ctx.letCalls[arm.discr]? then
      if onlyReturned arm.discr arm.code then
        let lctx ← read
        if freshApp (← getEnv) lctx.keys lctx.decls (← freshDeclsCached) g n then
          let e := RR.Expr.ctor arm.ty (some arm.layout.variant) (binders.map fun b => .var b.get!)
          -- The rebuilt value reads the binders themselves, which `vars`
          -- no longer names once a field is converted to its parameter's
          -- own type (`bindField`): a join point outlined in this
          -- alternative that returns the value captures them, so they are
          -- names in scope, at their types in the record (`CodeCtx.captured`).
          let scope := arm.layout.fields.foldl (init := ctx.captured) fun m f => match f with
            | some (j, ft) => match binders[j]? with
              | some (some b) => m.insert b ft
              | _ => m
            | none => m
          return (binders, { ctx with rebuild := ctx.rebuild.insert arm.discr (e, .named arm.ty),
                                      captured := scope })
  prev ctx arm binders

end Opt.FreshRebuild

/-- Registry entry point. -/
def Opt.FreshRebuild.install (c : PassConfig) : PassConfig :=
  { c with lower := { c.lower with enumFields := Opt.FreshRebuild.enumFields c.lower.enumFields } }

end LeanToReussir
