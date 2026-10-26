import Lean
import LeanToReussir.PassConfig
import LeanToReussir.Opt.ModPow2

/-!
# `p + c.utf8Size` with a branch of its own for ASCII (optimization `utf8-size-add`)

A position plus a character, `p + c : String.Pos.Raw` (`String.Pos.Raw`
has one field, so its mono code is the `Nat` byte index), is
`p.byteIdx + c.utf8Size`: `String.map`'s step (`Pos.pastModify`,
`Pos.pastSet`), the legacy string functions, a program's own `p + c`.
`Char.utf8Size` is Lean's chain of tests
(`if c ≤ 127 then 1 else if c ≤ 2047 then 2 else if c ≤ 65535 then 3
else 4`), and its results are literals, which rcgmp makes immediates in
line: once rrc inlines it, LLVM turns the chain into selects and the
next position waits for them. In a loop whose next position depends on
the character just read or written (`String.map`: the size of the new
character), the position then waits per character for the loads, the
mapping and the selects (L17: about 17 cycles per character, against 5.6
before rcgmp made the literals constants; its three `String.mapAux`
loops 3 times slower than under the old representation).

The pass rewrites, in the mono code after Stage 3, each `Nat.add p s`
or `Nat.add s p` whose `s` is bound in the same declaration to a call
`Char.utf8Size c` to `L2RNat.addUtf8Size p c`, an extern (the prelude's
`l2r_nat_add_utf8_size`: `p + 1` when `c ≤ 127`, in a branch of its own,
else `p` plus 2, 3 or 4 by the same tests). The ASCII case is then a
predicted branch whose next position is one add on `p`. The `let` of
`s` goes when nothing else uses it.

Soundness: the prelude's function repeats Lean's rule, so the pass
rewrites only the calls of an instance of `Char.utf8Size` whose own mono
code is exactly that rule (`isLeanRule`: the three tests `UInt32.decLe c
k` of the literals 127, 2047 and 65535, with the results 1, 2, 3 and 4);
the calls of any other instance stay (`L2R_DEBUG=1` names it).

`L2RNat.addUtf8Size` is added as `Opt/ModPow2` adds its extern: a
definition in the environment whose value is the rule
(`fun p c => p + c.utf8Size`, never an axiom: `programCasts` reads one as
a possible cast), with `@[extern]` naming the prelude function, and an
extern declaration of the program at the mono types (`Nat → UInt32 →
Nat`: mono code passes a `Char` as its `UInt32`). Other uses of
`Char.utf8Size` (a comparison, `p - c.utf8Size`, a size stored) stay calls.
Without the pass, the call and the addition are translated as any other
code.
-/

namespace LeanToReussir.Opt.Utf8SizeAdd
open Lean Compiler LCNF

/-- The declaration the rewritten code calls (an extern the pass adds). -/
def addName : Name := `L2RNat.addUtf8Size

/-- Its C symbol: the prelude's function. -/
def addSym : String := "l2r_nat_add_utf8_size"

/-- Lean's rule: the bounds of `Char.utf8Size`'s tests with the result of
each, then the result past the last. -/
def ruleBounds : List (Nat × Nat) := [(127, 1), (2047, 2), (65535, 3)]
def ruleLast : Nat := 4

/-- The literal that code `c` returns when it is `let n := lit; return n`. -/
def litReturn? (c : Code .pure) : Option Nat :=
  match c with
  | .let { fvarId, value := .lit (.nat n), .. } (.return r) => if r == fvarId then some n else none
  | _ => none

/-- Whether code `c` computes, from the `UInt32` variable `x`, the tests
`bounds` and then `last`: for each bound `(k, v)`,
`let b := k; let t := UInt32.decLe x b; cases t` with the `true`
alternative returning the literal `v` and the `false` one the rest. -/
partial def isChain (declOf : Name → Name) (x : FVarId) : List (Nat × Nat) → Nat → Code .pure → Bool
  | [], last, c => litReturn? c == some last
  | (k, v) :: rest, last, c =>
    match c with
    | .let { fvarId := kv, value := .lit (.uint32 k'), .. }
        (.let { fvarId := t, value := .const f _ #[.fvar x', .fvar kv'] _, .. } (.cases cs)) =>
      let alt (ctor : Name) : Option (Code .pure) := cs.alts.findSome? fun
        | .alt c' #[] code _ => if c' == ctor then some code else none
        | _ => none
      k'.toNat == k && x' == x && kv' == kv && declOf f == ``UInt32.decLe && cs.discr == t &&
        cs.typeName == ``Bool && cs.alts.size == 2 &&
        ((alt ``Bool.true).bind litReturn? == some v) &&
        ((alt ``Bool.false).map (isChain declOf x rest last ·) == some true)
    | _ => false

/-- Whether declaration `d` (an instance of `Char.utf8Size`) has Lean's
rule as its code (`ruleBounds`, `ruleLast`). -/
def isLeanRule (declOf : Name → Name) (d : Decl .pure) : Bool :=
  match d.params, d.value with
  | #[p], .code c => isChain declOf p.fvarId ruleBounds ruleLast c
  | _, _ => false

structure St where
  /-- Additions rewritten. -/
  rewritten : Nat := 0
  /-- The sizes the rewritten additions read: their `let`s go when unused. -/
  sizes : FVarIdHashSet := {}

/-- `c` with its additions of a `Char.utf8Size` call rewritten; `sizes`
holds the variables bound so far to a call of an instance in `rule`, with
the character (binders are unique, so a fact is never shadowed). -/
partial def rewrite (keys : NameMap InstKey) (rule : NameSet) (c : Code .pure)
    (sizes : Std.HashMap FVarId FVarId) : StateM St (Code .pure) := do
  let declOf (f : Name) : Name := ((keys.find? f).map (·.decl)).getD f
  match c with
  | .let d k =>
    let sizes := match d.value with
      | .const f _ #[.fvar ch] _ => if rule.contains f then sizes.insert d.fvarId ch else sizes
      | _ => sizes
    if let .const f _ #[.fvar a, .fvar b] _ := d.value then
      if declOf f == ``Nat.add then
        let pick := match sizes[b]?, sizes[a]? with
          | some ch, _ => some (a, b, ch)
          | none, some ch => some (b, a, ch)
          | none, none => none
        if let some (p, s, ch) := pick then
          modify fun st => { st with rewritten := st.rewritten + 1, sizes := st.sizes.insert s }
          return .let { d with value := .const addName [] #[.fvar p, .fvar ch] } (← rewrite keys rule k sizes)
    return .let d (← rewrite keys rule k sizes)
  | .fun d k =>
    let v ← rewrite keys rule d.value sizes
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← rewrite keys rule k sizes)
  | .jp d k =>
    let v ← rewrite keys rule d.value sizes
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← rewrite keys rule k sizes)
  | .cases cs =>
    let alts ← cs.alts.mapM fun alt => match alt with
      | .alt ctor ps code _ => return .alt ctor ps (← rewrite keys rule code sizes)
      | .default code => return .default (← rewrite keys rule code sizes)
      | other => return other
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c

/-- The rule on one declaration's code: the code, and the number of
additions rewritten. The sizes' `let`s that nothing else uses go. -/
def rewriteCode (keys : NameMap InstKey) (rule : NameSet) (c : Code .pure) : Code .pure × Nat :=
  let (c, st) := (rewrite keys rule c {}).run {}
  if st.rewritten == 0 then (c, 0) else
  ((ModPow2.dropUnused st.sizes c.collectUsed c).1, st.rewritten)

/-- The extern `L2RNat.addUtf8Size`, in the environment (the lowering
reads its extern symbol) and as a declaration of the program, as
`ModPow2.truncDecl` does: in the environment a definition at
`Nat → Char → Nat` whose value is the rule itself, the declaration at the
mono types `Nat → UInt32 → Nat` (the lowering reads those). The `L2R*`
namespaces are lean2rr's: an `L2RNat.addUtf8Size` already in the
environment must be that extern at that type; another one is an internal
error. -/
def addDecl' : CoreM (Decl .pure) := do
  let nat := mkConst ``Nat
  let ty := mkForall `p .default nat (mkForall `c .default (mkConst ``Char) nat)
  let env ← getEnv
  if let some info := env.find? addName then
    unless getExternNameFor env `c addName == some addSym && info.type == ty do
      let src := match env.getModuleIdxFor? addName with
        | some idx => s!" (declared in module {moduleNameAt env idx})"
        | none => ""
      throwError "lean2rr: utf8-size-add: {addName}{src} is not the extern {addSym} : Nat → Char → Nat \
        that the pass adds; the L2R* namespaces are lean2rr's (internal error)"
  else
    let body := mkLambda `p .default nat (mkLambda `c .default (mkConst ``Char)
      (mkApp2 (mkConst ``Nat.add) (.bvar 1) (mkApp (mkConst ``Char.utf8Size) (.bvar 0))))
    addDecl (.defnDecl { name := addName, levelParams := [], type := ty, value := body,
                         hints := .opaque, safety := .safe })
    match externAttr.setParam (← getEnv) addName { entries := [.standard `all addSym] } with
    | .ok env => setEnv env
    | .error e => throwError "lean2rr: utf8-size-add: {e} (internal error)"
  let u32 := mkConst ``UInt32
  let param (n : Name) (t : Expr) : Param .pure :=
    { fvarId := ⟨addName ++ n⟩, binderName := n, type := t, borrow := false }
  return { name := addName, levelParams := [], type := mkForall `p .default nat (mkForall `c .default u32 nat),
           params := #[param `p nat, param `c u32],
           value := .extern { entries := [.standard `all addSym] }, inlineAttr? := none }

/-- The pass: the instances of `Char.utf8Size` whose code is Lean's rule,
then every declaration with code, then the extern if an addition was
rewritten. -/
def run (keys : NameMap InstKey) (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let declOf (f : Name) : Name := ((keys.find? f).map (·.decl)).getD f
  let debug := (← IO.getEnv "L2R_DEBUG").isSome
  let mut rule : NameSet := {}
  for d in decls do
    if declOf d.name == ``Char.utf8Size then
      if isLeanRule declOf d then rule := rule.insert d.name
      else if debug then
        IO.eprintln s!"lean2rr: utf8-size-add: {d.name}'s code is not Lean's Char.utf8Size rule; its additions are not rewritten"
  if rule.isEmpty then return decls
  let mut out := #[]
  let mut n := 0
  for d in decls do
    match d.value with
    | .code c =>
      let (c, k) := rewriteCode keys rule c
      n := n + k
      out := out.push (if k == 0 then d else { d with value := .code c })
    | _ => out := out.push d
  if debug then
    IO.eprintln s!"lean2rr: utf8-size-add: {n} addition(s) of Char.utf8Size rewritten to {addSym}"
  if n == 0 then return out
  -- Also when the program has the declaration: `addDecl'` checks it.
  let ad ← addDecl'
  if decls.any (·.name == addName) then return out
  return out.push ad

end LeanToReussir.Opt.Utf8SizeAdd

namespace LeanToReussir

/-- Registry entry point. -/
def Opt.Utf8SizeAdd.install (c : PassConfig) : PassConfig :=
  { c with monoPassesCore := c.monoPassesCore.push Opt.Utf8SizeAdd.run }

end LeanToReussir
