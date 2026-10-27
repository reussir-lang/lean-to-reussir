import Lean
import LeanToReussir.PassConfig

/-!
# `x % 2^w` as the low `w` bits of `x` (optimization `mod-pow2`)

`BitVec.ofNat w x` is `x % 2 ^ w` (`Fin.Internal.ofNat (2 ^ w)`), and every
`BitVec` operation that can leave the range (`+`, `*`, `<<<`, `#`) ends
with it: its mono code is `let p := Nat.pow 2 w; Nat.mod x p`. For a wide
vector, `Nat.pow 2 w` makes a number of `w / 64 + 1` limbs (zeroed, then
the top bit) on every operation, and the division then compares it with
`x`; natively GMP does the same (`mpz_pow_ui`). lean-regex's backtracker
(`b ||| (1#w <<< i)` on a vector of states times positions) spent 42% of
its instructions zeroing these powers.

The pass rewrites, in the mono code after Stage 3, each `Nat.mod x p`
whose divisor is bound in the same declaration to
- `Nat.pow b w` with `b` the literal 2, or `Nat.shiftLeft o w` with `o`
  the literal 1: `L2RNat.truncateBits.0 x w`;
- the literal `2^k`, `k ≥ 61` (`minLitExp`), or a read of a constant
  whose code is that literal (Lean folds `2 ^ 64` to a literal, which
  Stage 2 extracts as a closed term): `L2RNat.truncateBits.0 x k`, with a
  `let` of the literal `k`.
`L2RNat.truncateBits.0` is an extern (`l2r_nat_truncate_bits`) that the pass
adds to the environment (a definition whose value is the rule, never an
axiom: `programCasts` would read one as a possible cast) and to the
declarations; the prelude computes it (rcgmp's `floormod2expi`, which
keeps immediates in line and reads the low limb of a big `x` for `w` below
62). The `let` of `p`, and of the literal 2 or 1 it took, goes when nothing
else uses it.

The value is `x % 2 ^ w` for every `x` and `w`. Natively, and in lean2rr
before this pass, `2 ^ w` ends the process where it cannot be made
(natively from `w = 2^32`: `Nat.pow exponent is too big`; in lean2rr above
`l2r_nat_max_bits` bits); the truncation needs no power, so it gives the
value there too (lean2rr lifts such limits where the result can be
computed: LB-11, plan §10). `L2R_DEBUG=1` prints how many `Nat.mod` calls
it rewrote. Without this pass, the power is made and divided by, as
natively.
-/

namespace LeanToReussir.Opt.ModPow2
open Lean Compiler LCNF

/-- The declaration the rewritten code calls (an extern the pass adds),
`L2RNat.truncateBits.0`. Its last part is a number, which no identifier has
(a hygienic name's number follows `_hyg`), so no declaration of the program
has the name: a program's own `L2RNat.truncateBits` is another declaration
(test `RtModPow2Reserved`; before, lean2rr refused it). -/
def truncName : Name := .num `L2RNat.truncateBits 0

/-- Its C symbol: the prelude's function. -/
def truncSym : String := "l2r_nat_truncate_bits"

/-- What a variable is bound to, as far as the rule looks. -/
inductive Def where
  /-- A `Nat` literal. -/
  | lit (n : Nat)
  /-- `2 ^ w` (`Nat.pow 2 w`, `Nat.shiftLeft 1 w`). -/
  | pow2 (w : FVarId)
  /-- `2 ^ e`, a read of a constant whose code is that literal. -/
  | pow2lit (e : Nat)
  deriving Inhabited

/-- `k` when `n = 2^k`. -/
def log2Exact? (n : Nat) : Option Nat :=
  if n != 0 && n &&& (n - 1) == 0 then some n.log2 else none

/-- The smallest exponent of a literal divisor the rule takes: below it
the divisor is small (`natSmallBits`, 61), and its `%` is computed in
line. -/
def minLitExp : Nat := natSmallBits

structure St where
  /-- `Nat.mod` calls rewritten. -/
  rewritten : Nat := 0
  /-- The divisors of the rewritten calls: their `let`s go when unused. -/
  divisors : FVarIdHashSet := {}

/-- `c` with its `Nat.mod x (2 ^ w)` calls rewritten; `defs` holds the
variables bound so far (binders are unique, so a fact is never shadowed).
`pows` are the constants whose code is the literal `2^k`, `k ≥ minExp`
(`minLitExp`). -/
partial def rewrite (minExp : Nat) (keys : NameMap InstKey) (pows : NameMap Nat) (c : Code .pure)
    (defs : Std.HashMap FVarId Def) : StateM St (Code .pure) := do
  let declOf (f : Name) : Name := ((keys.find? f).map (·.decl)).getD f
  match c with
  | .let d k =>
    let lit? (x : FVarId) : Option Nat := match defs[x]? with
      | some (.lit n) => some n
      | _ => none
    let defs := match d.value with
      | .lit (.nat n) => defs.insert d.fvarId (.lit n)
      | .const f _ #[.fvar b, .fvar w] _ =>
        if (declOf f == ``Nat.pow && lit? b == some 2) || (declOf f == ``Nat.shiftLeft && lit? b == some 1) then
          defs.insert d.fvarId (.pow2 w)
        else defs
      | .const f _ #[] _ =>
        match pows.find? f with
        | some e => defs.insert d.fvarId (.pow2lit e)
        | none => defs
      | _ => defs
    if let .const f _ #[.fvar x, .fvar p] _ := d.value then
      if declOf f == ``Nat.mod then
        match (defs[p]? : Option Def) with
        | some (.pow2 w) =>
          modify fun s => { s with rewritten := s.rewritten + 1, divisors := s.divisors.insert p }
          return .let { d with value := .const truncName [] #[.fvar x, .fvar w] } (← rewrite minExp keys pows k defs)
        | some df =>
          let e? := match df with
            | .lit n => (log2Exact? n).filter (· ≥ minExp)
            | .pow2lit e => some e
            | .pow2 _ => none
          if let some e := e? then
            modify fun s => { s with rewritten := s.rewritten + 1, divisors := s.divisors.insert p }
            -- A fresh binder for the exponent (binders are unique, so a
            -- suffix of this one is).
            let w : FVarId := ⟨d.fvarId.name ++ `l2r_w⟩
            return .let { fvarId := w, binderName := `w, type := mkConst ``Nat, value := .lit (.nat e) }
              (.let { d with value := .const truncName [] #[.fvar x, .fvar w] } (← rewrite minExp keys pows k defs))
        | none => pure ()
    return .let d (← rewrite minExp keys pows k defs)
  | .fun d k =>
    let v ← rewrite minExp keys pows d.value defs
    return .fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← rewrite minExp keys pows k defs)
  | .jp d k =>
    let v ← rewrite minExp keys pows d.value defs
    return .jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) (← rewrite minExp keys pows k defs)
  | .cases cs =>
    let alts ← cs.alts.mapM fun alt => match alt with
      | .alt ctor ps code _ => return .alt ctor ps (← rewrite minExp keys pows code defs)
      | .default code => return .default (← rewrite minExp keys pows code defs)
      | other => return other
    return .cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩
  | c => return c

/-- `c` without the `let`s of `drop` that `used` does not name; also
returns the variables those `let`s used. -/
partial def dropUnused (drop : FVarIdHashSet) (used : FVarIdHashSet) (c : Code .pure) :
    Code .pure × Array FVarId :=
  match c with
  | .let d k =>
    let (k, fed) := dropUnused drop used k
    if drop.contains d.fvarId && !used.contains d.fvarId then
      let args := match d.value with
        | .const _ _ as _ => as.filterMap fun | .fvar y => some y | _ => none
        | _ => #[]
      (k, fed ++ args)
    else (.let d k, fed)
  | .fun d k =>
    let (v, f1) := dropUnused drop used d.value
    let (k, f2) := dropUnused drop used k
    (.fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) k, f1 ++ f2)
  | .jp d k =>
    let (v, f1) := dropUnused drop used d.value
    let (k, f2) := dropUnused drop used k
    (.jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) k, f1 ++ f2)
  | .cases cs =>
    let (alts, fed) := cs.alts.foldl (init := (#[], #[])) fun (alts, fed) alt =>
      match alt with
      | .alt ctor ps code _ =>
        let (code, f) := dropUnused drop used code
        (alts.push (.alt ctor ps code), fed ++ f)
      | .default code =>
        let (code, f) := dropUnused drop used code
        (alts.push (.default code), fed ++ f)
      | other => (alts.push other, fed)
    (.cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩, fed)
  | c => (c, #[])

/-- The rule on one declaration's code: the code, and the number of calls
rewritten. The divisors' `let`s that nothing else uses go, then the
literals they took that nothing else uses. -/
def rewriteCode (minExp : Nat) (keys : NameMap InstKey) (pows : NameMap Nat) (c : Code .pure) :
    Code .pure × Nat :=
  let (c, st) := (rewrite minExp keys pows c {}).run {}
  if st.rewritten == 0 then (c, 0) else
  let (c, fed) := dropUnused st.divisors c.collectUsed c
  let fed := fed.foldl (·.insert ·) ({} : FVarIdHashSet)
  let (c, _) := dropUnused fed c.collectUsed c
  (c, st.rewritten)

/-- The constants whose code is one `Nat` literal `2^k` with `k ≥ minExp`, and
their `k`. -/
def literalPows (minExp : Nat) (decls : Array (Decl .pure)) : NameMap Nat :=
  decls.foldl (init := {}) fun m d =>
    match d.params.isEmpty, d.value with
    | true, .code (.let { fvarId := x, value := .lit (.nat n), .. } (.return r)) =>
      match log2Exact? n with
      | some e => if x == r && e ≥ minExp then m.insert d.name e else m
      | none => m
    | _, _ => m

/-- The extern `L2RNat.truncateBits.0 : Nat → Nat → Nat`
(`@[extern "l2r_nat_truncate_bits"]`), in the environment (the lowering
reads its type and its extern symbol) and as a declaration of the program.
In the environment it is a definition whose value is the rule itself,
`fun x w => Nat.mod x (Nat.pow 2 w)`, not an axiom: the whole-program
check `programCasts` reads an axiom of the program as a possible cast
(Cedar, Z06g, then got 701 conversion functions instead of 26 and ran 1%
more instructions). No program declares the name (`truncName`): one
already in the environment must be that extern at that type (the
rewritten calls go to the prelude's function through it); another one is
an internal error, never called in its place. -/
def truncDecl : CoreM (Decl .pure) := do
  let nat := mkConst ``Nat
  let ty := mkForall `x .default nat (mkForall `w .default nat nat)
  let env ← getEnv
  if let some info := env.find? truncName then
    unless getExternNameFor env `c truncName == some truncSym && info.type == ty do
      let src := match env.getModuleIdxFor? truncName with
        | some idx => s!" (declared in module {moduleNameAt env idx})"
        | none => ""
      throwError "lean2rr: mod-pow2: {truncName}{src} is not the extern {truncSym} : Nat → Nat → Nat \
        that the pass adds (internal error)"
  else
    let body := mkLambda `x .default nat (mkLambda `w .default nat
      (mkApp2 (mkConst ``Nat.mod) (.bvar 1) (mkApp2 (mkConst ``Nat.pow) (mkRawNatLit 2) (.bvar 0))))
    addDecl (.defnDecl { name := truncName, levelParams := [], type := ty, value := body,
                         hints := .opaque, safety := .safe })
    match externAttr.setParam (← getEnv) truncName { entries := [.standard `all truncSym] } with
    | .ok env => setEnv env
    | .error e => throwError "lean2rr: mod-pow2: {e} (internal error)"
  let param (n : Name) : Param .pure :=
    { fvarId := ⟨truncName ++ n⟩, binderName := n, type := nat, borrow := false }
  return { name := truncName, levelParams := [], type := ty, params := #[param `x, param `w],
           value := .extern { entries := [.standard `all truncSym] }, inlineAttr? := none }

/-- The pass: every declaration with code, then the extern if a call was
rewritten. -/
def run (minExp : Nat) (keys : NameMap InstKey) (decls : Array (Decl .pure)) : CoreM (Array (Decl .pure)) := do
  let pows := literalPows minExp decls
  let mut out := #[]
  let mut n := 0
  for d in decls do
    match d.value with
    | .code c =>
      let (c, k) := rewriteCode minExp keys pows c
      n := n + k
      out := out.push (if k == 0 then d else { d with value := .code c })
    | _ => out := out.push d
  if (← IO.getEnv "L2R_DEBUG").isSome then
    IO.eprintln s!"lean2rr: mod-pow2: {n} Nat.mod call(s) by a power of two rewritten"
  if n == 0 then return out
  -- Also when the program has the declaration: `truncDecl` checks it.
  let td ← truncDecl
  if decls.any (·.name == truncName) then return out
  return out.push td

end LeanToReussir.Opt.ModPow2

namespace LeanToReussir

/-- Registry entry point (the smallest literal exponent: `minLitExp`). -/
def Opt.ModPow2.install (c : PassConfig) : PassConfig :=
  { c with monoPassesCore := c.monoPassesCore.push (Opt.ModPow2.run Opt.ModPow2.minLitExp) }

end LeanToReussir
