import Lean
import LeanToReussir.PassConfig

/-!
# Bit tests and float conversions by rcgmp (optimization `prelude-int-ops`)

Three Lean definitions over `Nat` and `Int` have a direct counterpart in
Reussir's integers, which the prelude uses:

| Lean definition | Lean's code | prelude function |
|---|---|---|
| `Nat.testBit m i` | `1 &&& (m >>> i) != 0` | `l2r_nat_test_bit` (`testbiti`) |
| `Float.ofNat n` (`Nat.toFloat`) | `Float.ofScientific n false 0` | `l2r_float_of_nat` (`sitofp`) |
| `Float.ofInt i` (`Int.toFloat`) | `Float.ofNat` of `i.natAbs`, negated | `l2r_float_of_int` (`sitofp`) |

`m >>> i` makes a new number for a big `m` (a regex's bit matrix, Z03b);
`testbiti` reads the bit in place. From 2^53 on, `Float.ofScientific` goes
through `Float.Model` (bignum arithmetic, time quadratic in the number's
bits); `sitofp` rounds in one pass, with the same bits (the nearest double,
ties to even, an infinity of the sign past the largest finite one: judged
for Lean 4.34, see the prelude's comment). `Nat.toFloat` and `Int.toFloat`
are abbreviations: they reach the mono code as calls of `Float.ofNat` and
`Float.ofInt`.

What reaches the pass. None of the three is `@[inline]` and none is small
(LCNF inlines a definition without the attribute only when its code has at
most `compiler.small` = 1 binding; these have 3 to 5): every use is a call
of the definition's instance, or the instance itself as a function value.
So the pass rewrites, in the mono code after Stage 3 (after `float-lits`,
which folds `Float.ofNat` of a literal to its bits):
- each full call `let x := D a b` of an instance of definition `D` to
  `let x := L2R… a b` (the extern of `D`'s prelude function);
- the instance's own code to that one call (`Nat.testBit._l2r.0 m n :=
  L2RNat.testBit m n`), so that a partial application or a function value of
  `D`, which calls the instance, runs the prelude function too; and so does
  `Float.ofInt`'s code, whose `Float.ofNat` calls would otherwise be
  rewritten one by one.
The externs (`L2RNat.testBit`, `L2RFloat.ofNat`, `L2RFloat.ofInt`) are
added as `Opt/ModPow2` adds its own: a definition in the environment whose
value is the Lean definition itself (never an axiom: `programCasts` reads
one as a possible cast), with `@[extern]` naming the prelude function, and
an extern declaration of the program.

`L2R_DEBUG=1` prints how many calls and instances were rewritten. Without
the pass, Lean's definitions are translated like any other code.
-/

namespace LeanToReussir.Opt.PreludeIntOps
open Lean Compiler LCNF

/-- One rewrite: calls of the Lean definition `orig` become calls of the
extern `name` (C symbol `sym`, the prelude's function), whose parameters
and result have the Lean types `params` and `result`. -/
structure Op where
  orig : Name
  name : Name
  sym : String
  params : Array (Name × Expr)
  result : Expr

def testBit : Op :=
  { orig := ``Nat.testBit, name := `L2RNat.testBit, sym := "l2r_nat_test_bit",
    params := #[(`m, mkConst ``Nat), (`n, mkConst ``Nat)], result := mkConst ``Bool }

def floatOfNat : Op :=
  { orig := ``Float.ofNat, name := `L2RFloat.ofNat, sym := "l2r_float_of_nat",
    params := #[(`n, mkConst ``Nat)], result := mkConst ``Float }

def floatOfInt : Op :=
  { orig := ``Float.ofInt, name := `L2RFloat.ofInt, sym := "l2r_float_of_int",
    params := #[(`i, mkConst ``Int)], result := mkConst ``Float }

/-- The rewrites. -/
def ops : Array Op := #[testBit, floatOfNat, floatOfInt]

/-- The extern's Lean type. -/
def Op.type (o : Op) : Expr :=
  o.params.foldr (fun (n, t) b => mkForall n .default t b) o.result

/-- The rewrite for a full call of `f` (an instance name, mapped to its
definition by `keys`) with `n` arguments. -/
def opFor? (os : Array Op) (keys : NameMap InstKey) (f : Name) (n : Nat) : Option Op :=
  let d := ((keys.find? f).map (·.decl)).getD f
  os.find? fun o => o.orig == d && o.params.size == n

/-- How many calls or instances were rewritten, per extern name. -/
abbrev Counts := Std.HashMap Name Nat

def Counts.bump (m : Counts) (n : Name) (k : Nat := 1) : Counts :=
  m.insert n (m.getD n 0 + k)

/-- `c` with the full calls of the rewritten definitions replaced (every
argument a variable: a `Nat`, `Int` argument is never erased); the state
counts the calls replaced. -/
partial def rewrite (os : Array Op) (keys : NameMap InstKey) (c : Code .pure) :
    StateM Counts (Code .pure) := do
  match c with
  | .let d k =>
    if let .const f _ args _ := d.value then
      if let some o := (opFor? os keys f args.size).filter fun _ => args.all (· matches .fvar _) then
        modify (·.bump o.name)
        return .let { d with value := .const o.name [] args } (← rewrite os keys k)
    return .let d (← rewrite os keys k)
  | .fun d k =>
    let v ← rewrite os keys d.value
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← rewrite os keys k)
  | .jp d k =>
    let v ← rewrite os keys d.value
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← rewrite os keys k)
  | .cases cs =>
    let alts ← cs.alts.mapM fun alt => match alt with
      | .alt ctor ps code _ => return .alt ctor ps (← rewrite os keys code)
      | .default code => return .default (← rewrite os keys code)
      | other => return other
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c

/-- The rewrite whose definition declaration `d` is an instance of, with
its parameters at the extern's types: its code becomes one call of the
extern. -/
def instanceOp? (os : Array Op) (keys : NameMap InstKey) (d : Decl .pure) : Option Op :=
  (opFor? os keys d.name d.params.size).filter fun o =>
    (d.params.zip o.params).all fun (p, (_, t)) => p.type == t

/-- The extern `o` in the environment (the lowering reads its type and its
extern symbol) and as a declaration of the program, as `ModPow2.truncDecl`
does: in the environment a definition whose value is `o.orig` itself. The
`L2R*` namespaces are lean2rr's: an `o.name` already in the environment
must be that extern at that type; another one is an internal error. -/
def externDecl (o : Op) : CoreM (Decl .pure) := do
  let ty := o.type
  let env ← getEnv
  if let some info := env.find? o.name then
    unless getExternNameFor env `c o.name == some o.sym && info.type == ty do
      let src := match env.getModuleIdxFor? o.name with
        | some idx => s!" (declared in module {moduleNameAt env idx})"
        | none => ""
      throwError "lean2rr: prelude-int-ops: {o.name}{src} is not the extern {o.sym} : {ty} \
        that the pass adds; the L2R* namespaces are lean2rr's (internal error)"
  else
    let n := o.params.size
    let body := o.params.foldr (fun (x, t) b => mkLambda x .default t b)
      (mkAppN (mkConst o.orig) ((List.range n).toArray.map fun i => .bvar (n - 1 - i)))
    addDecl (.defnDecl { name := o.name, levelParams := [], type := ty, value := body,
                         hints := .opaque, safety := .safe })
    match externAttr.setParam (← getEnv) o.name { entries := [.standard `all o.sym] } with
    | .ok env => setEnv env
    | .error e => throwError "lean2rr: prelude-int-ops: {e} (internal error)"
  let ps := o.params.map fun (x, t) =>
    ({ fvarId := ⟨o.name ++ x⟩, binderName := x, type := t, borrow := false } : Param .pure)
  return { name := o.name, levelParams := [], type := ty, params := ps,
           value := .extern { entries := [.standard `all o.sym] }, inlineAttr? := none }

/-- The pass: every declaration with code (an instance of a rewritten
definition becomes one call of its extern), then the externs it calls. -/
def run (os : Array Op) (keys : NameMap InstKey) (decls : Array (Decl .pure)) :
    CoreM (Array (Decl .pure)) := do
  if os.isEmpty then return decls
  let mut out := #[]
  let mut calls : Counts := {}
  let mut insts : Counts := {}
  for d in decls do
    match d.value with
    | .code c =>
      if let some o := instanceOp? os keys d then
        -- A fresh binder (binders are unique; the old code's go).
        let r : FVarId := ⟨d.name ++ `l2r_r⟩
        let call := .let { fvarId := r, binderName := `r, type := o.result,
                           value := .const o.name [] (d.params.map (.fvar ·.fvarId)) } (.return r)
        insts := insts.bump o.name
        out := out.push { d with value := .code call }
      else
        let (c', m) := (rewrite os keys c).run {}
        if m.isEmpty then out := out.push d
        else
          out := out.push { d with value := .code c' }
          calls := m.fold (init := calls) fun acc n k => acc.bump n k
    | _ => out := out.push d
  if (← IO.getEnv "L2R_DEBUG").isSome then
    for o in os do
      IO.eprintln s!"lean2rr: prelude-int-ops: {o.orig}: {calls.getD o.name 0} call(s) and \
        {insts.getD o.name 0} instance(s) rewritten to {o.sym}"
  for o in os do
    if calls.contains o.name || insts.contains o.name then
      -- Also when the program has the declaration: `externDecl` checks it.
      let ed ← externDecl o
      unless decls.any (·.name == o.name) do out := out.push ed
  return out

end LeanToReussir.Opt.PreludeIntOps

namespace LeanToReussir

/-- Registry entry point (the rewrites `PreludeIntOps.ops`). -/
def Opt.PreludeIntOps.install (c : PassConfig) : PassConfig :=
  { c with monoPassesCore := c.monoPassesCore.push (Opt.PreludeIntOps.run Opt.PreludeIntOps.ops) }

end LeanToReussir
