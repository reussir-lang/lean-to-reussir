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
by `Float.ofBits` of the resulting bit pattern, a total conversion of a
`UInt64` literal (translation plan §5.12). The functions are pure, total
and do not trace, so evaluating them early is unobservable.

Without this pass the translated program runs those Lean functions itself
when the constant holding the literal is evaluated (the same bits).
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Literal arguments seen so far in a declaration's code. -/
inductive LitArg where
  | nat (n : Nat)
  | bool (b : Bool)
  deriving BEq

/-- For each join point, what its jumps seen so far pass at each parameter:
the literal that every one of them passes there, or `none`. -/
abbrev JumpLits := Std.HashMap FVarId (Array (Option LitArg))

/-- The facts of the jumps of `a` and of `b` together: at each parameter,
the literal both pass, else `none`. A join point without a jump in one of
them keeps the other's facts. -/
def JumpLits.meet (a b : JumpLits) : JumpLits :=
  b.fold (init := a) fun acc jp args =>
    acc.insert jp <| match acc[jp]? with
      | some xs => xs.zipWith (fun x y => if x == y then x else none) args
      | none => args

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

/-- The value of the discriminant of the `Bool` `cases` `cs` inside its
alternative `alt`: `true` in the alternative `Bool.true`, `false` in
`Bool.false`, and in a `.default` alternative the constructor that the other
alternatives do not name. Lean's simp replaces a constructor written inside
an alternative by the discriminant when they are equal there
(`Simp.simpCtorDiscr?`): in the alternative `Bool.true` of `cases b`, the
flag of `1.0` (`Float.ofScientific 10 true 1`) becomes `b`. -/
def boolOfAlt? (cs : Cases .pure) (alt : Alt .pure) : Option Bool :=
  if cs.typeName != ``Bool then none else
  match alt with
  | .alt ``Bool.true .. => some true
  | .alt ``Bool.false .. => some false
  | .default _ =>
    let named := cs.getCtorNames
    match named.contains ``Bool.true, named.contains ``Bool.false with
    | true, false => some false
    | false, true => some true
    | _, _ => none
  | _ => none

/-- Replace float literal calls in `c` by `Float.ofBits`/`Float32.ofBits` of
their bit pattern. `keys` maps instance names to their declarations. Also
returns the facts of the jumps in `c` (`JumpLits`).

`lits` holds the variables whose value is a known literal: a `let` of a
literal; the discriminant of a `Bool` `cases` inside an alternative
(`boolOfAlt?`); a parameter of a join point to which every jump passes the
same literal. The last rule finds the flag that simp replaced in an
alternative after `Simp.simpJpCases?` moves the alternative into a join
point of its own: the discriminant becomes that join point's parameter. -/
partial def foldFloatLitsCore (keys : NameMap InstKey) (c : Code .pure)
    (lits : Std.HashMap FVarId LitArg) : Code .pure × JumpLits :=
  match c with
  | .let d k =>
    match d.value with
    | .lit (.nat n) => let (k, j) := foldFloatLitsCore keys k (lits.insert d.fvarId (.nat n)); (.let d k, j)
    | .const ``Bool.true _ #[] _ => let (k, j) := foldFloatLitsCore keys k (lits.insert d.fvarId (.bool true)); (.let d k, j)
    | .const ``Bool.false _ #[] _ => let (k, j) := foldFloatLitsCore keys k (lits.insert d.fvarId (.bool false)); (.let d k, j)
    | .const f _ args _ =>
      let decl := ((keys.find? f).map (·.decl)).getD f
      let argVals := args.map fun | .fvar x => lits[x]? | _ => none
      let (k, j) := foldFloatLitsCore keys k lits
      match floatLitBits? decl argVals with
      | some (bits, is32) =>
        -- A fresh binder for the bit pattern (binders are unique, so a
        -- suffix of this one is).
        let b : FVarId := ⟨d.fvarId.name ++ `l2r_bits⟩
        let (lit, ty, ofBits) :=
          if is32 then (LitValue.uint32 bits.toUInt32, mkConst ``UInt32, ``Float32.ofBits)
          else (LitValue.uint64 bits, mkConst ``UInt64, ``Float.ofBits)
        (.let { fvarId := b, binderName := `bits, type := ty, value := .lit lit }
          (.let { d with value := .const ofBits [] #[.fvar b] } k), j)
      | none => (.let d k, j)
    | _ => let (k, j) := foldFloatLitsCore keys k lits; (.let d k, j)
  | .fun d k =>
    let (v, jv) := foldFloatLitsCore keys d.value lits
    let (k, jk) := foldFloatLitsCore keys k lits
    -- A jump does not leave a function (LCNF's checker), so `jv` names no
    -- join point outside it; meeting it in anyway only loses facts.
    (.fun (FunDecl.mk d.fvarId d.binderName d.params d.type v) k, JumpLits.meet jk jv)
  | .jp d k =>
    -- A join point is not recursive: every jump to it is in `k` (LCNF's
    -- checker puts it in scope only there). Fold `k` first.
    let (k, jk) := foldFloatLitsCore keys k lits
    -- A parameter whose fact is unknown drops any earlier fact of its
    -- name (binders are unique, so there is none; this keeps it so).
    let inBody := match jk[d.fvarId]? with
      | some args => (d.params.zip args).foldl (init := lits) fun m (p, a) =>
        match a with
        | some l => m.insert p.fvarId l
        | none => m.erase p.fvarId
      | none => d.params.foldl (init := lits) fun m p => m.erase p.fvarId
    let (v, jv) := foldFloatLitsCore keys d.value inBody
    (.jp (FunDecl.mk d.fvarId d.binderName d.params d.type v) k, JumpLits.meet (jk.erase d.fvarId) jv)
  | .cases cs =>
    -- Inside an alternative of a `Bool` `cases`, the discriminant is a
    -- literal (`boolOfAlt?`).
    let inAlt (alt : Alt .pure) := match boolOfAlt? cs alt with
      | some b => lits.insert cs.discr (.bool b)
      | none => lits
    let (alts, j) := cs.alts.foldl (init := (#[], {})) fun (alts, j) alt =>
      match alt with
      | .alt ctor ps code _ =>
        let (code, ja) := foldFloatLitsCore keys code (inAlt alt)
        (alts.push (.alt ctor ps code), JumpLits.meet j ja)
      | .default code =>
        let (code, ja) := foldFloatLitsCore keys code (inAlt alt)
        (alts.push (.default code), JumpLits.meet j ja)
      | other => (alts.push other, j)
    (.cases ⟨cs.typeName, cs.resultType, cs.discr, alts⟩, j)
  | .jmp jp args => (c, ({} : JumpLits).insert jp (args.map fun | .fvar x => lits[x]? | _ => none))
  | c => (c, {})

/-- `foldFloatLitsCore` without the facts of the jumps. -/
def foldFloatLits (keys : NameMap InstKey) (c : Code .pure) : Code .pure :=
  (foldFloatLitsCore keys c {}).1

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
