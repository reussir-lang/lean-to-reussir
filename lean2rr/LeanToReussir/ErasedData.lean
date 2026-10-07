import Lean

/-!
# Data passed to an erased parameter (a Lean compiler bug not reproduced)

Lean 4.34.0's `toLCNF` gives a `match` the join of its arms' types
(`ToLCNF.visitCases`, `resultType := joinTypes altType resultType`), and
`joinTypes` gives `◾` when one side is `◾` (`Types.lean`, `joinTypes?`). So a
`match` whose one arm gives a type or a proof and whose other arm gives data
gets the type `◾`, and the join point after it a parameter of type
`lcErased`, which the jump from the data arm passes the data to:

```
def f2 (b : Bool) (n : Nat) : Nat :=
  let v : T b := match b with      -- T true = Nat → Prop, T false = Nat
    | true  => fun _ => True
    | false => n
  match b, v with
  | false, v => (show Nat from v) + 1
  | true,  _ => 0
```

becomes `jp _jp (_y : lcErased) := … Nat.add _y 1 …` with `jmp _jp n`. Native
Lean drops the parameter (`toImpure`) and computes with `◾`, the boxed 0:
`f2 false 41` is 1, where the kernel gives 42. lean2rr's rule 4 removes
erased parameters too, so it gave 1 as well. Lean's specializer copies the
parameter's type to the declaration it makes for a lambda over the value
(`List.map (fun x => x + v.1)` gives `List.mapTR.loop._at_.….spec_0 (_y :
lcErased) …`), and `toMono` then replaces the argument of every call at that
position by `◾`.

This pass finds the parameters of type `lcErased` that receive data at some
jump or call, and gives them the type `lcAny`: a boxed data parameter. A
jump or call that passes `◾` there passes `box(0)` (rule 4e), as natively.
It runs on Stage 1's instances (before `toMono` erases the arguments at the
specializer's declarations) and again on Stage 2's output (a join point that
Lean's mono passes made over such a `match`).

- *Targets*: join-point parameters, parameters of local functions (applied
  directly) and of the program's declarations with code (called directly,
  also partially), whose type is exactly `lcErased` (Stage 1's instances
  type their type parameters so too). A parameter of a sort type is not a
  target.
- *Data*: an argument is data if it is a variable that is not bound to `◾`
  and whose type is not `lcErased` and not a type former type (a sort, or a
  function type that ends in a sort). Proofs and types have the type
  `lcErased` (or a type former type) in LCNF, so a genuine type or proof
  parameter never receives data, and is never retyped.
- *Propagation*: a retyped parameter holds data, so passing it on makes the
  next parameter a target too (the declaration the specializer made). The
  pass repeats until no parameter changes; each round only retypes, so it
  ends after at most as many rounds as there are erased parameters.

Not covered: a `let` of type `◾`, which Lean's `simp` replaces, value and
all, by `◾` (`Simp/Main.lean`, `decl.type.isErased`): such a value is gone
before lean2rr sees the code. And a value that reaches an erased domain
through a closure applied elsewhere (not a direct call).
-/

namespace LeanToReussir
open Lean Compiler LCNF

namespace ErasedData

/-- Whether a parameter of type `t` is a target: its type is `lcErased`. -/
def erasedParamTy (t : Expr) : Bool := t.consumeMData.isErased

/-- Whether a variable of type `t` holds data: `t` is not `lcErased` and not
a type former type. -/
def dataTy (t : Expr) : Bool :=
  let t := t.consumeMData
  !t.isErased && !isTypeFormerType t

/-- Function type `t` with the domain at position `i` replaced by `d`. -/
def setDomain : Expr → Nat → Expr → Expr
  | .forallE n _ b bi, 0, d => .forallE n d b bi
  | .forallE n a b bi, i + 1, d => .forallE n a (setDomain b i d) bi
  | .mdata m e, i, d => .mdata m (setDomain e i d)
  | t, _, _ => t

/-- Parameters `ps` (of function type `ty`) with those that `retype` selects
given the type `lcAny`. -/
def retypeParams (ps : Array (Param .pure)) (ty : Expr) (retype : Nat → Param .pure → Bool) :
    Array (Param .pure) × Expr := Id.run do
  let mut ps := ps
  let mut ty := ty
  for i in [:ps.size] do
    let p := ps[i]!
    if retype i p then
      ps := ps.set! i { p with type := anyExpr }
      ty := setDomain ty i anyExpr
  return (ps, ty)

structure ScanState where
  /-- The types of the declaration's binders (variables are unique within
  a declaration). -/
  types : Std.HashMap FVarId Expr := {}
  /-- The variables bound to `◾`. -/
  placeholders : Std.HashSet FVarId := {}
  /-- The parameters of the join points and local functions. -/
  locals : Std.HashMap FVarId (Array (Param .pure)) := {}
  /-- The declaration's local parameters that receive data. -/
  newLocals : Std.HashSet FVarId := {}
  /-- The declaration parameters (declaration, position) that receive data. -/
  newParams : Std.HashSet (Name × Nat) := {}

abbrev ScanM := StateM ScanState

def isData (a : Arg .pure) : ScanM Bool := do
  let .fvar x := a | return false
  let s ← get
  if s.placeholders.contains x then return false
  return (s.types[x]?.map dataTy).getD false

def addParams (ps : Array (Param .pure)) : ScanM Unit :=
  modify fun s => { s with types := ps.foldl (fun m p => m.insert p.fvarId p.type) s.types }

/-- Record the local parameters among `ps` that receive data from `args`. -/
def checkLocal (ps : Array (Param .pure)) (args : Array (Arg .pure)) : ScanM Unit := do
  for i in [:min ps.size args.size] do
    let p := ps[i]!
    if erasedParamTy p.type then
      if ← isData args[i]! then
        modify fun s => { s with newLocals := s.newLocals.insert p.fvarId }

/-- Find the targets that receive data in code `c` (`declParams`: the
parameters of the program's declarations with code). -/
partial def scan (declParams : Std.HashMap Name (Array (Param .pure))) (c : Code .pure) : ScanM Unit := do
  match c with
  | .let d k =>
    match d.value with
    | .fvar f args =>
      if let some ps := (← get).locals[f]? then checkLocal ps args
    | .const g _ args _ =>
      if let some ps := declParams[g]? then
        for i in [:min ps.size args.size] do
          if erasedParamTy ps[i]!.type then
            if ← isData args[i]! then
              modify fun s => { s with newParams := s.newParams.insert (g, i) }
    | _ => pure ()
    modify fun s => { s with
      types := s.types.insert d.fvarId d.type
      placeholders := if d.value matches .erased then s.placeholders.insert d.fvarId else s.placeholders }
    scan declParams k
  | .fun d k _ =>
    addParams d.params
    scan declParams d.value
    modify fun s => { s with types := s.types.insert d.fvarId d.type, locals := s.locals.insert d.fvarId d.params }
    scan declParams k
  | .jp d k =>
    addParams d.params
    modify fun s => { s with locals := s.locals.insert d.fvarId d.params }
    scan declParams d.value
    scan declParams k
  | .jmp j args =>
    if let some ps := (← get).locals[j]? then checkLocal ps args
  | .cases cs =>
    for alt in cs.alts do
      match alt with
      | .alt _ ps code _ =>
        addParams ps
        scan declParams code
      | .default code => scan declParams code
      | _ => pure ()
  | _ => pure ()

/-- Code `c` with the local parameters `marks` of type `lcAny`. -/
partial def rewrite (marks : Std.HashSet FVarId) (c : Code .pure) : Code .pure :=
  let fn (d : FunDecl .pure) : FunDecl .pure :=
    let (ps, ty) := retypeParams d.params d.type fun _ p => marks.contains p.fvarId
    FunDecl.mk d.fvarId d.binderName ps ty (rewrite marks d.value)
  match c with
  | .let d k => .let d (rewrite marks k)
  | .fun d k _ => .fun (fn d) (rewrite marks k)
  | .jp d k => .jp (fn d) (rewrite marks k)
  | .cases cs =>
    .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (rewrite marks code)
      | .default code => .default (rewrite marks code)
      | other => other⟩
  | c => c

end ErasedData

open ErasedData in
/-- The program `decls` with every parameter of type `lcErased` that receives
data (see the module comment) of type `lcAny`. Phase-independent: it runs
on Stage 1's instances and on Stage 2's output. -/
def retypeErasedData (decls : Array (Decl .pure)) : Array (Decl .pure) := Id.run do
  let mut decls := decls
  -- Each round retypes at least one parameter of type `lcErased`.
  repeat
    let declParams : Std.HashMap Name (Array (Param .pure)) := decls.foldl (init := {}) fun m d =>
      if d.value matches .code _ then m.insert d.name d.params else m
    let mut newParams : Std.HashSet (Name × Nat) := {}
    let mut changed := false
    let cur := decls
    for h : i in [:cur.size] do
      let d := cur[i]
      let .code c := d.value | continue
      let init : ScanState := { types := d.params.foldl (fun m p => m.insert p.fvarId p.type) {} }
      let ((), s) := (scan declParams c).run init
      newParams := s.newParams.fold (·.insert ·) newParams
      unless s.newLocals.isEmpty do
        decls := decls.set! i { d with value := .code (rewrite s.newLocals c) }
        changed := true
    unless newParams.isEmpty do
      decls := decls.map fun d =>
        let (ps, ty) := retypeParams d.params d.type fun j _ => newParams.contains (d.name, j)
        if ps == d.params then d else { d with params := ps, type := ty }
      changed := true
    unless changed do break
  return decls

end LeanToReussir
