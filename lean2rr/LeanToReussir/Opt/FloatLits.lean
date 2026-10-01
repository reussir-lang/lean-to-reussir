import Lean
import LeanToReussir.PassConfig

/-!
# Float literals (optimization `float-lits`)

A `Float` or `Float32` literal reaches the mono code as a call
`Float.ofScientific m s e` (or `Float.ofNat n`, `Float32.…`) on literal
arguments. These are Lean functions, not C: on the slow path (`m ≥ 2^53` or
`e > 22`) they go through `Float.Model` with bignum arithmetic, and even the
fast path reads a table and divides. Natively the value is computed once
(`lean_float_once`); lean2rr evaluates the call itself, with the same Lean
functions (compiled into lean2rr from the same `Init` code), and replaces it
by `Float.ofBits` of the resulting bit pattern, a cheap constant that
Opt/CheapConsts recomputes at each use (translation plan §5.12). The
functions are pure, total and do not trace, so evaluating them early is
unobservable.

Without this pass the translated program runs those Lean functions itself
when the constant holding the literal is evaluated (the same bits), and
caches the constant rather than recomputing it.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Literal arguments seen so far in a declaration's code. -/
inductive LitArg where
  | nat (n : Nat)
  | bool (b : Bool)

/-- Bounds on the arguments evaluated at translation time: beyond them the
result is `0` or infinity anyway, but `Float.Model` would compute `10^e`. -/
def floatLitMaxExp : Nat := 2000
def floatLitMaxBits : Nat := 4096

/-- The bit pattern of `f` applied to literal arguments, if `f` is one of
the float literal functions: `(bits, is32)`. -/
def floatLitBits? (f : Name) (args : Array (Option LitArg)) : Option (UInt64 × Bool) :=
  match f, args with
  | ``Float.ofScientific, #[some (.nat m), some (.bool s), some (.nat e)] =>
    if e ≤ floatLitMaxExp && m.log2 < floatLitMaxBits then some ((Float.ofScientific m s e).toBits, false) else none
  | ``Float32.ofScientific, #[some (.nat m), some (.bool s), some (.nat e)] =>
    if e ≤ floatLitMaxExp && m.log2 < floatLitMaxBits then some ((Float32.ofScientific m s e).toBits.toUInt64, true) else none
  | ``Float.ofNat, #[some (.nat n)] =>
    if n.log2 < floatLitMaxBits then some ((Float.ofNat n).toBits, false) else none
  | ``Float32.ofNat, #[some (.nat n)] =>
    if n.log2 < floatLitMaxBits then some ((Float32.ofNat n).toBits.toUInt64, true) else none
  | _, _ => none

/-- Replace float literal calls in `c` by `Float.ofBits`/`Float32.ofBits` of
their bit pattern. `keys` maps instance names to their declarations. -/
partial def foldFloatLits (keys : NameMap InstKey) (c : Code .pure)
    (lits : Std.HashMap FVarId LitArg := {}) : Code .pure :=
  match c with
  | .let d k =>
    match d.value with
    | .lit (.nat n) => .let d (foldFloatLits keys k (lits.insert d.fvarId (.nat n)))
    | .const ``Bool.true _ #[] _ => .let d (foldFloatLits keys k (lits.insert d.fvarId (.bool true)))
    | .const ``Bool.false _ #[] _ => .let d (foldFloatLits keys k (lits.insert d.fvarId (.bool false)))
    | .const f _ args _ =>
      let decl := ((keys.find? f).map (·.decl)).getD f
      let argVals := args.map fun | .fvar x => lits[x]? | _ => none
      match floatLitBits? decl argVals with
      | some (bits, is32) =>
        -- A fresh binder for the bit pattern (binders are unique, so a
        -- suffix of this one is).
        let b : FVarId := ⟨d.fvarId.name ++ `l2r_bits⟩
        let (lit, ty, ofBits) :=
          if is32 then (LitValue.uint32 bits.toUInt32, mkConst ``UInt32, ``Float32.ofBits)
          else (LitValue.uint64 bits, mkConst ``UInt64, ``Float.ofBits)
        .let { fvarId := b, binderName := `bits, type := ty, value := .lit lit }
          (.let { d with value := .const ofBits [] #[.fvar b] } (foldFloatLits keys k lits))
      | none => .let d (foldFloatLits keys k lits)
    | _ => .let d (foldFloatLits keys k lits)
  | .fun d k _ =>
    .fun (FunDecl.mk d.fvarId d.binderName d.params d.type (foldFloatLits keys d.value lits)) (foldFloatLits keys k lits)
  | .jp d k =>
    .jp (FunDecl.mk d.fvarId d.binderName d.params d.type (foldFloatLits keys d.value lits)) (foldFloatLits keys k lits)
  | .cases cs =>
    .cases ⟨cs.typeName, cs.resultType, cs.discr, cs.alts.map fun
      | .alt ctor ps code _ => .alt ctor ps (foldFloatLits keys code lits)
      | .default code => .default (foldFloatLits keys code lits)
      | other => other⟩
  | c => c

/-- `foldFloatLits` on every declaration with code. -/
def foldFloatLitsDecls (keys : NameMap InstKey) (decls : Array (Decl .pure)) : Array (Decl .pure) :=
  decls.map fun d => match d.value with
    | .code c => { d with value := .code (foldFloatLits keys c) }
    | _ => d

/-- Registry entry point: the fold runs on the checked mono program, before
lowering. -/
def Opt.FloatLits.install (c : PassConfig) : PassConfig :=
  { c with monoPasses := c.monoPasses.push foldFloatLitsDecls }

end LeanToReussir
