import Lean

/-!
# Stage 4: matches on Reussir's built-in integers

With the optimization `int-match` (Opt/IntMatch) a case split on a `Nat`
or `Int` is one Reussir `match` on the built-in integer, which Reussir
compiles to one `rcgmp.match` over integer intervals. This file finds the
arms of that `match` in the mono code; the lowering (`lowerIntMatch`,
Lower/Code) lowers them. The arms come from:

* a `cases` on a `Nat` (Stage 2 keeps it, `toMonoK`'s `keepIntCases`):
  `Nat.zero` is the literal arm `0`, `Nat.succ p` the arm `Nat::Succ(p)`,
  whose binder Reussir computes in the selection (an immediate's tagged
  bits minus 4), where Lean's `toMono` tests `Nat.decEq n 0` and computes
  `Nat.sub n 1`;
* a `cases` on an `Int`: `Int::OfNat(m)`, `Int::NegSucc(m)`;
* a `cases` on such a field whose only use it is, nested in the arm
  (Lean's `match n with | 0 => … | 1 => … | n+2 => …`): its arms join the
  outer `match`, as literals (`1`; `-1` below `Int::NegSucc`) or inside
  the outer constructors (`Nat::Succ(Nat::Succ(q))`,
  `Int::OfNat(Nat::Succ(k))`, `Nat::Succ(_)` for its default);
* a chain of tests of one `Nat` or `Int` against literals (`Nat.decEq n
  k`, `Nat.beq n k`, `Int.decEq i k`, each test used only by its `cases`;
  Lean compiles `match n with | 0 => … | 5 => … | _ => …` to it): an arm
  per literal, then the rest of the chain's last `false` branch, which may
  be a `cases` on the same variable (its arms join).

Arms keep the order of Lean's tests, and Reussir's first matching arm
wins, so a literal tested first goes to its arm also when a later
`Nat::Succ` arm covers it. A literal arm that an earlier arm already
covers is left out (Reussir warns about an arm no value reaches), and so is
a default whose position the arms before it cover. The `let`s of literals
between the fused tests and `cases` go into each later arm that uses them.
Where the arms do not cover every integer (a `cases` whose unreachable
alternatives Lean removed, without a default), the lowering adds
`_ => l2r_unreachable`.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Where the `cases` on a `Nat` being fused sits in the `match` on the
scrutinee: the scrutinee itself (a `Nat`), or the field of its `Int::OfNat`
or `Int::NegSucc`, below `depth` more `Nat::Succ`s. -/
structure IntPos where
  /-- The constructor around the position: none (a `Nat` scrutinee),
  `Int::OfNat` or `Int::NegSucc`. -/
  outer : Array (String × String) := #[]
  /-- The `Nat::Succ`s between that constructor and the position. -/
  depth : Nat := 0
  /-- Below `Int::NegSucc`. -/
  neg : Bool := false

/-- The value of the scrutinee where the position's `Nat` is zero: `depth`,
or `-(depth + 1)` below `Int::NegSucc`. -/
def IntPos.zero (p : IntPos) : Int := if p.neg then -((p.depth : Int) + 1) else p.depth

/-- The constructors around a pattern at the position, outermost first. -/
def IntPos.wraps (p : IntPos) : Array (String × String) :=
  p.outer ++ Array.replicate p.depth ("Nat", "Succ")

/-- The position of the field of a `Nat::Succ` at `p`. -/
def IntPos.succ (p : IntPos) : IntPos := { p with depth := p.depth + 1 }

/-- The pattern of an arm of a `match` on a `Nat` or `Int`. -/
inductive IntPat where
  /-- The scrutinee equal to `v`. -/
  | lit (v : Int)
  /-- `wraps(ty::ctor(p))`: a `Nat::Succ`, `Int::OfNat` or `Int::NegSucc`
  binding its field to parameter `p`. -/
  | bind (wraps : Array (String × String)) (ty ctor : String) (p : Param .pure)
  /-- `wraps(_)`: what the arms before leave at a position (`_` at the top). -/
  | wild (wraps : Array (String × String))

/-- An arm of a `match` on a `Nat` or `Int`: its pattern, the `let`s of
literals of the fused tests and `cases` above it (its code may use them),
and its code. -/
structure IntArm where
  pat : IntPat
  lets : Array (LetDecl .pure) := #[]
  code : Code .pure

/-- The arms of a `match` on a `Nat` or `Int`, and whether they cover
every value of the scrutinee. -/
structure IntArms where
  arms : Array IntArm := #[]
  exhaustive : Bool := false
  /-- The literals of the arms so far (a later literal arm with one of
  them is left out: an earlier arm takes its value). -/
  seen : Std.HashSet Int := {}

/-- What the matches need of a declaration's code: its `let`s of `Nat`
and `Int` literals (`litValue?`: also reads of a constant that is one,
since Lean extracts a `Nat` literal from 2^63 on and every `Int` literal
but those it computes with `Int.ofNat` in place as a closed term), and how
many times its code names each variable. -/
structure IntMatchInfo where
  natLits : Std.HashMap FVarId Nat := {}
  intLits : Std.HashMap FVarId Int := {}
  uses : Std.HashMap FVarId Nat := {}
  deriving Inhabited

/-- The literal that let value `v` computes, with `vals` the literals of
the variables it reads: a `Nat` literal (`true`), or an `Int` (`false`)
made by `Int.ofNat`, `Int.negSucc` or `Int.neg` of literals; `const` gives
the value of a constant read (`litConst?`). -/
def litValue? (vals : FVarId → Option (Bool × Int)) (const : Name → Option (Bool × Int))
    (v : LetValue .pure) : Option (Bool × Int) :=
  match v with
  | .lit (.nat k) => some (true, k)
  | .const f _ #[] _ => const f
  | .const f _ #[.fvar x] _ =>
    match vals x with
    | some (true, k) =>
      if f == ``Int.ofNat then some (false, k)
      else if f == ``Int.negSucc then some (false, -(k + 1))
      else none
    | some (false, i) => if f == ``Int.neg then some (false, -i) else none
    | none => none
  | _ => none

/-- The value of declaration `d` if it is a constant whose code computes a
literal (`litValue?`: a closed term Lean extracted, such as `2^64` or
`Int.neg (Int.ofNat 7)`), reading other such constants up to `fuel`
deep. -/
partial def litConst? (decls : NameMap (Decl .pure)) (d : Decl .pure) (fuel : Nat := 8) : Option (Bool × Int) := do
  guard (d.params.isEmpty && fuel > 0)
  let .code c := d.value | none
  let rec go (vals : Std.HashMap FVarId (Bool × Int)) : Code .pure → Option (Bool × Int)
    | .let x k => do
      let v ← litValue? (vals[·]?) (fun f => (decls.find? f).bind (litConst? decls · (fuel - 1))) x.value
      go (vals.insert x.fvarId v) k
    | .return y => vals[y]?
    | _ => none
  go {} c

/-- `IntMatchInfo` of code `c` (`decls`: the program's declarations, for
reads of literal constants), added to `info`. -/
partial def intMatchInfo (decls : NameMap (Decl .pure)) (c : Code .pure) (info : IntMatchInfo := {}) :
    IntMatchInfo :=
  let use (i : IntMatchInfo) (x : FVarId) : IntMatchInfo := { i with uses := i.uses.insert x (i.uses.getD x 0 + 1) }
  let useArgs (i : IntMatchInfo) (as : Array (Arg .pure)) : IntMatchInfo :=
    as.foldl (fun i a => match a with | .fvar y => use i y | _ => i) i
  match c with
  | .let d k =>
    let vals (x : FVarId) : Option (Bool × Int) :=
      match info.natLits[x]?, info.intLits[x]? with
      | some n, _ => some (true, n)
      | none, some i => some (false, i)
      | none, none => none
    let info := match litValue? vals (fun f => (decls.find? f).bind (litConst? decls ·)) d.value with
      | some (true, n) => { info with natLits := info.natLits.insert d.fvarId n.toNat }
      | some (false, i) => { info with intLits := info.intLits.insert d.fvarId i }
      | none => info
    let info := match d.value with
      | .fvar f as => useArgs (use info f) as
      | .const _ _ as _ => useArgs info as
      | .proj _ _ y _ => use info y
      | _ => info
    intMatchInfo decls k info
  | .fun d k _ | .jp d k => intMatchInfo decls k (intMatchInfo decls d.value info)
  | .jmp _ as => useArgs info as
  | .cases cs => cs.alts.foldl (fun i alt => intMatchInfo decls alt.getCode i) (use info cs.discr)
  | .return y => use info y
  | .unreach _ => info

/-- Whether `let` `d` binds a literal (`.lit _`: of a number, also of a
string or another scalar) or computes a number from literals (`litValue?`):
it reads no other value and has no effect, so it may move into the arms
that use it, or go where none does (a run makes it at most once either
way). A number allocates nothing that stays (Reussir's integer literals
are immediates or read-only objects). A string literal is pure: made in
the arm that uses it, or not made, it gives the same results. -/
def IntMatchInfo.litLet (info : IntMatchInfo) (d : LetDecl .pure) : Bool :=
  match d.value with
  | .lit _ => true
  | _ => info.natLits.contains d.fvarId || info.intLits.contains d.fvarId

/-- The `let`s of literals that start `c` (`IntMatchInfo.litLet`), and the
code after them. -/
def splitLitLets (info : IntMatchInfo) (c : Code .pure) : Array (LetDecl .pure) × Code .pure := Id.run do
  let mut ls := #[]
  let mut c := c
  repeat
    let .let d k := c | break
    unless info.litLet d do break
    ls := ls.push d
    c := k
  return (ls, c)

/-- A test of a `Nat` or `Int` against a literal: `Nat.decEq n z`,
`Nat.beq n z` or `Int.decEq i z` (either order), `z` a literal
(`IntMatchInfo`); the variable, the literal, and whether it is an `Int`
test. -/
def litEqTest? (info : IntMatchInfo) (v : LetValue .pure) : Option (FVarId × Int × Bool) :=
  match v with
  | .const f _ #[.fvar a, .fvar b] _ =>
    if f == ``Nat.decEq || f == ``Nat.beq then
      match info.natLits[b]?, info.natLits[a]? with
      | some k, _ => some (a, k, false)
      | none, some k => some (b, k, false)
      | none, none => none
    else if f == ``Int.decEq then
      match info.intLits[b]?, info.intLits[a]? with
      | some k, _ => some (a, k, true)
      | none, some k => some (b, k, true)
      | none, none => none
    else none
  | _ => none

/-- `c` as a test of variable `n` (any variable when `n` is none) against
a literal, used only by its `cases`: `let b := Nat.decEq n z; cases b`;
the variable, the literal, whether it is an `Int` test, and the code where
it holds and where it does not. Both branches must be there (an
alternative or the default). -/
def litTest? (info : IntMatchInfo) (n : Option FVarId) (c : Code .pure) :
    Option (FVarId × Int × Bool × Code .pure × Code .pure) := do
  let .let d (.cases cs) := c | none
  let (x, k, isInt) ← litEqTest? info d.value
  guard (n.all (· == x))
  guard (cs.discr == d.fvarId && cs.typeName == ``Bool && info.uses.getD d.fvarId 0 == 1)
  let branch (ctor : Name) : Option (Code .pure) := cs.alts.findSome? fun
    | .alt c _ k _ => if c == ctor then some k else none
    | _ => none
  let dflt : Option (Code .pure) := cs.alts.findSome? fun
    | .default k => some k
    | _ => none
  let t ← (branch ``Bool.true).orElse fun _ => dflt
  let f ← (branch ``Bool.false).orElse fun _ => dflt
  return (x, k, isInt, t, f)

/-- `c` as `let`s of literals, then a `cases` on `Nat` variable `x` that is
its only use: the `let`s and the `cases`. -/
def natCasesOn? (info : IntMatchInfo) (x : FVarId) (c : Code .pure) :
    Option (Array (LetDecl .pure) × Cases .pure) := do
  let (ls, c) := splitLitLets info c
  let .cases cs := c | none
  guard (cs.discr == x && cs.typeName == ``Nat && info.uses.getD x 0 == 1)
  return (ls, cs)

/-- The arms of `cases` `cs` on the `Nat` at position `pos`, below the
`let`s `lets`, appended to `acc`. The position is covered when its zero
and its `Nat.succ` are (or a default takes the rest). -/
partial def natArms (info : IntMatchInfo) (pos : IntPos) (cs : Cases .pure) (lets : Array (LetDecl .pure))
    (acc : IntArms) : IntArms := Id.run do
  let mut acc := acc
  let mut zero := false
  let mut succ := false
  for alt in cs.alts do
    match alt with
    | .alt c ps k _ =>
      if c == ``Nat.zero then
        zero := true
        unless acc.seen.contains pos.zero do
          acc := { acc with arms := acc.arms.push { pat := .lit pos.zero, lets, code := k },
                            seen := acc.seen.insert pos.zero }
      else if c == ``Nat.succ then
        let some p := ps[0]? | continue
        match natCasesOn? info p.fvarId k with
        | some (ls, cs') =>
          let inner := natArms info pos.succ cs' (lets ++ ls) { acc with exhaustive := false }
          succ := inner.exhaustive
          acc := { inner with exhaustive := acc.exhaustive }
        | none =>
          succ := true
          acc := { acc with arms := acc.arms.push { pat := .bind pos.wraps "Nat" "Succ" p, lets, code := k } }
    | _ => pure ()
  let covered := (zero || acc.seen.contains pos.zero) && succ
  if covered then return { acc with exhaustive := true }
  match cs.alts.findSome? (fun | .default k => some k | _ => none) with
  | some k => return { acc with arms := acc.arms.push { pat := .wild pos.wraps, lets, code := k }, exhaustive := true }
  | none => return { acc with exhaustive := false }

/-- The arms of `cases` `cs` on an `Int` scrutinee, below the `let`s
`lets`, appended to `acc`. -/
def intArms (info : IntMatchInfo) (cs : Cases .pure) (lets : Array (LetDecl .pure) := #[])
    (acc : IntArms := {}) : IntArms := Id.run do
  let mut acc := acc
  let mut covered := true
  for (ctor, name, neg) in [(``Int.ofNat, "OfNat", false), (``Int.negSucc, "NegSucc", true)] do
    let alt? := cs.alts.findSome? fun
      | .alt c ps k _ => if c == ctor then some (ps, k) else none
      | _ => none
    match alt? with
    | some (ps, k) =>
      let some p := ps[0]? | covered := false; continue
      match natCasesOn? info p.fvarId k with
      | some (ls, cs') =>
        let inner := natArms info { outer := #[("Int", name)], neg } cs' (lets ++ ls) { acc with exhaustive := false }
        covered := covered && inner.exhaustive
        acc := inner
      | none => acc := { acc with arms := acc.arms.push { pat := .bind #[] "Int" name p, lets, code := k } }
    | none => covered := false
  if covered then return { acc with exhaustive := true }
  match cs.alts.findSome? (fun | .default k => some k | _ => none) with
  | some k => return { acc with arms := acc.arms.push { pat := .wild #[], lets, code := k }, exhaustive := true }
  | none => return { acc with exhaustive := false }

/-- The arms of a chain of tests of variable `n` (a `Nat`, or an `Int`
when `isInt`) against literals that starts at `c` (`litTest?`): an arm per
literal, then the last `false` branch: the arms of a `cases` on `n` there,
or a default. -/
def chainArms (info : IntMatchInfo) (n : FVarId) (isInt : Bool) (c : Code .pure) : IntArms := Id.run do
  let ty := if isInt then ``Int else ``Nat
  let mut acc : IntArms := {}
  let mut lets : Array (LetDecl .pure) := #[]
  let mut c := c
  repeat
    let some (_, k, _, t, f) := litTest? info (some n) c | break
    -- A literal tested again is never true there: the chain stops, and the
    -- test stays in the default.
    if acc.seen.contains k then break
    acc := { acc with arms := acc.arms.push { pat := .lit k, lets, code := t }, seen := acc.seen.insert k }
    let (ls, f') := splitLitLets info f
    let next := (litTest? info (some n) f').isSome || (match f' with
      | .cases cs => cs.discr == n && cs.typeName == ty
      | _ => false)
    if next then
      lets := lets ++ ls
      c := f'
    else
      c := f
      break
  match c with
  | .cases cs =>
    if cs.discr == n && cs.typeName == ty then
      return if isInt then intArms info cs lets acc else natArms info {} cs lets acc
  | _ => pure ()
  return { acc with arms := acc.arms.push { pat := .wild #[], lets, code := c }, exhaustive := true }

/-- The code of arm `a`: the `let`s of literals it uses, and those these
read in turn, then its code. -/
def IntArm.fullCode (a : IntArm) : Code .pure :=
  if a.lets.isEmpty then a.code else
  -- A kept `let` keeps the `let`s its value reads (`Int.neg` of
  -- `Int.ofNat` of a literal, computed in place where Lean extracted no
  -- closed term).
  let reads (v : LetValue .pure) : Array FVarId :=
    let args (as : Array (Arg .pure)) := as.filterMap fun | .fvar y => some y | _ => none
    match v with
    | .fvar f as => (args as).push f
    | .const _ _ as _ => args as
    | .proj _ _ y _ => #[y]
    | _ => #[]
  let (_, code) := a.lets.foldr (init := ((intMatchInfo {} a.code).uses, a.code)) fun d (used, k) =>
    if used.contains d.fvarId then ((reads d.value).foldl (fun u y => u.insert y 1) used, .let d k)
    else (used, k)
  code

end LeanToReussir
