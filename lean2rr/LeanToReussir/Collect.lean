import Lean

/-!
# Whole-program collection

Starting from a root declaration (usually `main`), walk base-phase LCNF bodies
and collect everything the program can reach:

* declarations with an LCNF body — these are translated;
* `@[extern]` declarations — these must be provided by the runtime;
* constructors, and the inductive types they belong to;
* constants referenced from code that are none of the above — reported as
  missing, since they would otherwise surface as a late translation failure.

Types are walked too, and the set of inductive types is closed under
constructor field types, so type mapping sees every inductive a value can
have. Discovery follows code references only: a declaration that is merely
mentioned in a type is not code the program runs.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- The reachable part of a program. Arrays are in discovery order. -/
structure Program where
  root : Name
  decls : Array (Decl .pure) := #[]
  externs : Array (Decl .pure) := #[]
  ctors : NameSet := {}
  inductives : NameSet := {}
  /-- `(constant, first declaration referencing it)`. -/
  missing : Array (Name × Name) := #[]

/-- Fold `f` over the type arguments of an application. -/
def foldArgTypes (f : Expr → σ → σ) (args : Array (Arg .pure)) (s : σ) : σ :=
  args.foldl (init := s) fun s arg =>
    match arg with
    | .type e _ => f e s
    | _ => s

/-- Fold `f` over every type occurring in `code`: binder types, type
arguments of applications, `cases` result types, and `unreach` types. -/
partial def foldCodeTypes (f : Expr → σ → σ) : Code .pure → σ → σ
  | .let d k, s =>
    let s := f d.type s
    let s := match d.value with
      | .const _ _ args _ | .fvar _ args => foldArgTypes f args s
      | _ => s
    foldCodeTypes f k s
  | .fun d k _, s | .jp d k, s =>
    let s := d.params.foldl (fun s p => f p.type s) (f d.type s)
    foldCodeTypes f k (foldCodeTypes f d.value s)
  | .cases c, s =>
    c.alts.foldl (init := f c.resultType s) fun s alt =>
      foldCodeTypes f alt.getCode (alt.getParams.foldl (fun s p => f p.type s) s)
  | .unreach ty, s => f ty s
  | _, s => s

/-- Fold `f` over every type in a declaration: its signature and its body. -/
def foldDeclTypes (f : Expr → σ → σ) (decl : Decl .pure) (s : σ) : σ :=
  let s := decl.params.foldl (fun s p => f p.type s) (f decl.type s)
  match decl.value with
  | .code c => foldCodeTypes f c s
  | .extern _ => s

/-- Constants applied by `let` values in `code`, in order of appearance
(duplicates included; the caller deduplicates). -/
partial def codeConsts : Code .pure → Array Name → Array Name
  | .let d k, acc =>
    codeConsts k (match d.value with | .const n _ _ _ => acc.push n | _ => acc)
  | .fun d k _, acc | .jp d k, acc => codeConsts k (codeConsts d.value acc)
  | .cases c, acc => c.alts.foldl (fun acc alt => codeConsts alt.getCode acc) acc
  | _, acc => acc

/-- Whether an inductive type lives in `Prop` (its values are erased). -/
def isPropInductive (ival : InductiveVal) : Bool :=
  go ival.type
where
  go : Expr → Bool
    | .forallE _ _ b _ => go b
    | .sort .zero => true
    | _ => false

/-- Add the non-`Prop` inductive types mentioned in `e`. -/
def addInductives (env : Environment) (e : Expr) (s : NameSet) : NameSet :=
  e.foldConsts s fun c s =>
    match env.find? c with
    | some (.inductInfo ival) => if isPropInductive ival then s else s.insert c
    | _ => s

/-- Close a set of inductive types under constructor field types. -/
partial def closeInductives (env : Environment) (s : NameSet) : NameSet :=
  let s' := s.foldl (init := s) fun acc ind =>
    match env.find? ind with
    | some (.inductInfo ival) =>
      ival.ctors.foldl (init := acc) fun acc ctor =>
        match env.find? ctor with
        | some ci => addInductives env ci.type acc
        | none => acc
    | _ => acc
  if s'.size == s.size then s else closeInductives env s'

/-- Collect the program reachable from `root`. -/
def collect (root : Name) : CoreM Program := do
  let env ← getEnv
  let mut prog : Program := { root }
  let mut inductives : NameSet := {}
  let mut seen : NameSet := {}
  let mut stack : Array (Name × Name) := #[(root, root)]
  while h : stack.size > 0 do
    let (name, src) := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    if let some decl ← getBaseDecl? name then
      inductives := foldDeclTypes (addInductives env) decl inductives
      match decl.value with
      | .extern _ =>
        prog := { prog with externs := prog.externs.push decl }
      | .code code =>
        prog := { prog with decls := prog.decls.push decl }
        -- Push in reverse so that the depth-first walk visits callees in
        -- source order, which keeps dumps readable.
        for callee in (codeConsts code #[]).reverse do
          unless seen.contains callee do
            stack := stack.push (callee, name)
    else
      match env.find? name with
      | some (.ctorInfo ci) =>
        prog := { prog with ctors := prog.ctors.insert name }
        inductives := inductives.insert ci.induct
      | _ =>
        prog := { prog with missing := prog.missing.push (name, src) }
  return { prog with inductives := closeInductives env inductives }

end LeanToReussir
