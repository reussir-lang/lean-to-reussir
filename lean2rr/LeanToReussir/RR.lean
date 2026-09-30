/-!
# RR: the subset of Reussir source that lean2rr emits

A small syntax tree for the `.rr` code generated in Stage 4, and its
printer. The printer is the only place that knows Reussir's concrete
syntax, including its quirks: there is no `else if` (nested `if`s go in an
`else { … }` block), and match arms take no trailing comma.
-/

namespace LeanToReussir.RR

/-- Reussir types. -/
inductive Ty where
  /-- A primitive or declared type used by name, e.g. `u64`, `bool`, `unit`,
  a generated nominal type, or a runtime type from the prelude. -/
  | named (name : String)
  /-- A generic type applied to arguments, e.g. `RVec<u32>`. -/
  | app (name : String) (args : Array Ty)
  /-- A (curried, single-argument) closure type `A -> B`. -/
  | fn (dom : Ty) (cod : Ty)
  deriving BEq, Hashable, Inhabited, Repr

partial def Ty.render : Ty → String
  | .named n => n
  | .app n args => s!"{n}<{", ".intercalate (args.toList.map Ty.render)}>"
  -- The arrow is right-associative; parenthesize a function domain.
  | .fn d c => (match d with | .fn .. => s!"({d.render})" | _ => d.render) ++ " -> " ++ c.render

/-- Reussir's `unit` has no value representation (it is result-only), so
lean2rr represents unit-like values (erased values, `PUnit`, the IO world)
with a one-variant value enum from the prelude. -/
def Ty.unit : Ty := .named "L2RUnit"
def Ty.bool : Ty := .named "bool"

mutual
  /-- Expressions. Generated code is close to A-normal form, so most
  operands are variables. -/
  inductive Expr where
    | var (name : String)
    /-- Literal or other atom, printed verbatim (`42`, `true`, `()`). -/
    | atom (text : String)
    /-- Call of a named function; `tyArgs` are explicit generic arguments. -/
    | call (fn : String) (tyArgs : Array Ty) (args : Array Expr)
    /-- Application of a closure value to one argument: `f(a)`. -/
    | apply (fn : Expr) (arg : Expr)
    /-- `T::v{args}` (enum variant, `variant = some v`) or `T{args}` (struct). -/
    | ctor (ty : String) (variant : Option String) (args : Array Expr)
    /-- Positional field access `e.i`. -/
    | field (e : Expr) (idx : Nat)
    /-- Single-parameter lambda `|x : T| body`. -/
    | lam (param : String) (ty : Ty) (body : Block)
    | ite (cond : Expr) (thenB : Block) (elseB : Block)
    /-- `match scrut { arms }`; each arm is `pattern => block`. -/
    | mtch (scrut : Expr) (arms : Array Arm)
    | block (b : Block)

  /-- One match arm: a constructor pattern with field binders
  (`none` binds `_`), or a wildcard when `ctor = none`. -/
  structure Arm where
    ty : String
    ctor : Option String
    binders : Array (Option String)
    body : Block

  /-- `{ let x : T = e; … result }`. -/
  structure Block where
    lets : Array (String × Option Ty × Expr)
    result : Expr
end

/-- The unit value. -/
def Expr.unitVal : Expr := .ctor "L2RUnit" (some "u") #[]

instance : Inhabited Expr := ⟨.unitVal⟩
instance : Inhabited Block := ⟨⟨#[], .unitVal⟩⟩

def Block.ofExpr (e : Expr) : Block := ⟨#[], e⟩

/-- A top-level item. -/
inductive Item where
  /-- `enum [value]? Name { v1(T, …), v2, … }` -/
  | enum (name : String) (value : Bool) (variants : Array (String × Array Ty))
  /-- `struct [value]? Name(T, …);` -/
  | struct (name : String) (value : Bool) (fields : Array Ty)
  /-- `fn name(p : T, …) -> R { body }` -/
  | fn (name : String) (params : Array (String × Ty)) (ret : Ty) (body : Block)
  /-- Verbatim source (the runtime prelude, the entry point). -/
  | raw (text : String)

private def indent (n : Nat) : String := "".pushn ' ' (4 * n)

mutual
  partial def Expr.render (d : Nat) : Expr → String
    | .var n => n
    | .atom t => t
    | .call f tys args =>
      let tyArgs := if tys.isEmpty then "" else s!"<{", ".intercalate (tys.toList.map Ty.render)}>"
      s!"{f}{tyArgs}({", ".intercalate (args.toList.map (Expr.render d))})"
    | .apply f a =>
      let fs := match f with
        | .var _ | .apply .. | .call .. => f.render d
        | _ => s!"({f.render d})"
      s!"{fs}({a.render d})"
    | .ctor ty v args =>
      let head := match v with | some v => s!"{ty}::{v}" | none => ty
      if args.isEmpty then head ++ "{}" else s!"{head}\{{", ".intercalate (args.toList.map (Expr.render d))}}"
    | .field e i => s!"{e.render d}.{i}"
    | .lam x ty body => s!"|{x} : {ty.render}| {Block.render d body}"
    | .ite c t e =>
      -- No `else if` in Reussir: an `if` in the else branch stays inside braces.
      s!"if {c.render d} {Block.render d t} else {Block.render d e}"
    | .mtch s arms =>
      let armTexts := arms.toList.map (Arm.render (d + 1))
      s!"match {s.render d} \{\n{",\n".intercalate armTexts}\n{indent d}}"
    | .block b => Block.render d b

  partial def Arm.render (d : Nat) (a : Arm) : String :=
    let pat := match a.ctor with
      | none => "_"
      | some c =>
        let bs := a.binders.toList.map fun | some b => b | none => "_"
        if bs.isEmpty then s!"{a.ty}::{c}" else s!"{a.ty}::{c}({", ".intercalate bs})"
    s!"{indent d}{pat} => {Block.render d a.body}"

  partial def Block.render (d : Nat) (b : Block) : String :=
    if b.lets.isEmpty then
      match b.result with
      | .mtch .. | .ite .. | .block .. => s!"\{\n{indent (d + 1)}{b.result.render (d + 1)}\n{indent d}}"
      | _ => s!"\{ {b.result.render d} }"
    else
      let lets := b.lets.toList.map fun (x, ty, e) =>
        let ann := match ty with | some t => s!" : {t.render}" | none => ""
        s!"{indent (d + 1)}let {x}{ann} = {e.render (d + 1)};\n"
      s!"\{\n{String.join lets}{indent (d + 1)}{b.result.render (d + 1)}\n{indent d}}"
end

def Item.render : Item → String
  | .enum n value vs =>
    let cap := if value then "[value] " else ""
    let variants := vs.toList.map fun (v, fields) =>
      if fields.isEmpty then s!"    {v}" else s!"    {v}({", ".intercalate (fields.toList.map Ty.render)})"
    s!"enum {cap}{n} \{\n{",\n".intercalate variants}\n}\n"
  | .struct n value fields =>
    let cap := if value then "[value] " else ""
    s!"struct {cap}{n}({", ".intercalate (fields.toList.map Ty.render)})\n"
  | .fn n ps ret body =>
    let params := ", ".intercalate (ps.toList.map fun (x, t) => s!"{x} : {t.render}")
    s!"fn {n}({params}) -> {ret.render} {Block.render 0 body}\n"
  | .raw t => t

end LeanToReussir.RR
