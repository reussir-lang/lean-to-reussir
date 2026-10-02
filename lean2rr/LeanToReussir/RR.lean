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
  /-- A Lean function value `A → B` (curried). It is a generated shared enum
  (`fnTypeName`), not a Reussir closure; see Lower's "Function values". -/
  | fn (dom : Ty) (cod : Ty)
  /-- A Reussir closure type `A -> B`: callbacks passed to prelude helpers,
  and the `raw` variant of a function value. -/
  | cls (dom : Ty) (cod : Ty)
  deriving BEq, Hashable, Inhabited, Repr

/-- An injective encoding of a type as identifier characters (a prefix
code: lengths before names, argument counts before arguments). -/
partial def Ty.enc : Ty → String
  | .named n => s!"{n.length}n{n}"
  | .app n args => s!"{n.length}a{n}{args.size}_" ++ String.join (args.toList.map Ty.enc)
  | .fn d c => "F" ++ d.enc ++ c.enc
  | .cls d c => "C" ++ d.enc ++ c.enc

/-- The generated enum representing Lean function values of type `t`. -/
def fnTypeName (t : Ty) : String := "L2RFn_" ++ t.enc

partial def Ty.render : Ty → String
  | .named n => n
  -- An enumeration stored in an array as its index (Lower's
  -- `arrayStorage`): the index type, `L2RIx<u8, T>` renders as `u8`.
  | .app "L2RIx" #[w, _] => w.render
  | .app n args => s!"{n}<{", ".intercalate (args.toList.map Ty.render)}>"
  | t@(.fn ..) => fnTypeName t
  -- The arrow is right-associative; parenthesize a function domain.
  | .cls d c => (match d with | .cls .. => s!"({d.render})" | _ => d.render) ++ " -> " ++ c.render

/-- Every type occurring in `t` (itself included), innermost first. -/
partial def Ty.subterms (t : Ty) (acc : Array Ty := #[]) : Array Ty :=
  let acc := match t with
    | .named _ => acc
    | .app _ args => args.foldl (fun a (x : Ty) => x.subterms a) acc
    | .fn d c | .cls d c => c.subterms (d.subterms acc)
  acc.push t

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
    /-- Numeric conversion `(e as T)`. -/
    | cast (e : Expr) (ty : Ty)
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

/-- Parse a type as written in the prelude: `name` or `name<T, …>`. -/
partial def parseTy (s : String) : Option Ty :=
  let s := s.trim
  if s.isEmpty then none else
  match s.splitOn "<" with
  | [n] => if n.all (fun c => c.isAlphanum || c == '_') then some (.named n) else none
  | n :: _ =>
    if !s.endsWith ">" then none else
    let inner := ((s.drop (n.length + 1)).dropRight 1).toString
    -- Split at top-level commas.
    let (parts, cur, _) := inner.foldl (init := (#[], "", 0)) fun (ps, cur, depth) c =>
      if c == ',' && depth == 0 then (ps.push cur, "", depth)
      else (ps, cur.push c, if c == '<' then depth + 1 else if c == '>' then depth - 1 else depth)
    let parts := parts.push cur
    match parts.mapM parseTy with
    | some args => some (.app n.trim args)
    | none => none
  | [] => none

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

mutual
  /-- The types written in an expression (annotations, lambda parameters,
  explicit type arguments). -/
  partial def Expr.tys : Expr → Array Ty → Array Ty
    | .var _, acc | .atom _, acc => acc
    | .call _ tys args, acc => args.foldl (fun a e => e.tys a) (acc ++ tys)
    | .apply f a, acc => a.tys (f.tys acc)
    | .ctor _ _ args, acc => args.foldl (fun a e => e.tys a) acc
    | .field e _, acc => e.tys acc
    | .cast e t, acc => (e.tys acc).push t
    | .lam _ t b, acc => Block.tys b (acc.push t)
    | .ite c t e, acc => Block.tys e (Block.tys t (c.tys acc))
    | .mtch s arms, acc => arms.foldl (fun a arm => Block.tys arm.body a) (s.tys acc)
    | .block b, acc => Block.tys b acc
  partial def Block.tys (b : Block) (acc : Array Ty) : Array Ty :=
    b.result.tys (b.lets.foldl (fun a (_, t, e) => e.tys (match t with | some t => a.push t | none => a)) acc)
end

/-- The types an item mentions. -/
def Item.tys : Item → Array Ty
  | .enum _ _ vs => vs.foldl (fun a (_, fs) => a ++ fs) #[]
  | .struct _ _ fs => fs
  | .fn _ ps ret body => Block.tys body (ps.map (·.2) |>.push ret)
  | .raw _ => #[]

/-! The printer appends to one string, so rendering is linear in the size
of the output: each piece of text is written once, where building every
nested block's text and concatenating it into its parent's would copy it
once per nesting level. -/

/-- `out` followed by `items`, each written by `f`, separated by `sep`. -/
@[inline] def joinTo {α : Type} (out : String) (items : Array α) (sep : String) (f : α → String → String) : String :=
  Id.run do
    let mut out := out
    for h : i in [:items.size] do
      if i > 0 then out := out ++ sep
      out := f items[i] out
    return out

mutual
  partial def Expr.renderTo (d : Nat) (e : Expr) (out : String) : String :=
    match e with
    | .var n => out ++ n
    | .atom t => out ++ t
    | .call f tys args =>
      let out := out ++ f
      let out := if tys.isEmpty then out
        else joinTo (out ++ "<") tys ", " (fun t o => o ++ t.render) ++ ">"
      joinTo (out ++ "(") args ", " (Expr.renderTo d) ++ ")"
    | .apply f a =>
      let out := match f with
        | .var _ | .apply .. | .call .. => f.renderTo d out
        | _ => f.renderTo d (out ++ "(") ++ ")"
      a.renderTo d (out ++ "(") ++ ")"
    | .ctor ty v args =>
      let out := match v with | some v => out ++ ty ++ "::" ++ v | none => out ++ ty
      if args.isEmpty then out ++ "{}" else joinTo (out ++ "{") args ", " (Expr.renderTo d) ++ "}"
    | .field e i => e.renderTo d out ++ "." ++ toString i
    | .cast e t => e.renderTo d (out ++ "(") ++ " as " ++ t.render ++ ")"
    | .lam x ty body => Block.renderTo d body (out ++ "|" ++ x ++ " : " ++ ty.render ++ "| ")
    | .ite c t e =>
      -- No `else if` in Reussir: an `if` in the else branch stays inside braces.
      let out := Expr.renderHead d c (out ++ "if ") ++ " "
      Block.renderTo d e (Block.renderTo d t out ++ " else ")
    | .mtch s arms =>
      let out := Expr.renderHead d s (out ++ "match ") ++ " {\n"
      (joinTo out arms ",\n" (Arm.renderTo (d + 1)) ++ "\n").pushn ' ' (4 * d) ++ "}"
    | .block b => Block.renderTo d b out

  /-- The scrutinee of a `match` or the condition of an `if`, which a `{`
  follows: in parentheses when it ends with a brace of its own (a
  constructor, a block, a `match`, an `if`, a lambda), which Reussir's
  parser would take for the start of the body (`match T::c{x} {` is a parse
  error, as in Rust). -/
  partial def Expr.renderHead (d : Nat) (e : Expr) (out : String) : String :=
    match e with
    | .ctor .. | .block .. | .mtch .. | .ite .. | .lam .. => e.renderTo d (out ++ "(") ++ ")"
    | _ => e.renderTo d out

  partial def Arm.renderTo (d : Nat) (a : Arm) (out : String) : String :=
    let out := out.pushn ' ' (4 * d)
    let out := match a.ctor with
      | none => out ++ "_"
      | some c =>
        let out := out ++ a.ty ++ "::" ++ c
        if a.binders.isEmpty then out
        else joinTo (out ++ "(") a.binders ", " (fun b o => o ++ (match b with | some b => b | none => "_")) ++ ")"
    Block.renderTo d a.body (out ++ " => ")

  partial def Block.renderTo (d : Nat) (b : Block) (out : String) : String :=
    if b.lets.isEmpty then
      match b.result with
      | .mtch .. | .ite .. | .block .. =>
        ((b.result.renderTo (d + 1) ((out ++ "{\n").pushn ' ' (4 * (d + 1)))) ++ "\n").pushn ' ' (4 * d) ++ "}"
      | _ => b.result.renderTo d (out ++ "{ ") ++ " }"
    else Id.run do
      let mut out := out ++ "{\n"
      for (x, ty, e) in b.lets do
        out := out.pushn ' ' (4 * (d + 1)) ++ "let " ++ x
        if let some t := ty then out := out ++ " : " ++ t.render
        out := e.renderTo (d + 1) (out ++ " = ") ++ ";\n"
      out := b.result.renderTo (d + 1) (out.pushn ' ' (4 * (d + 1)))
      return (out ++ "\n").pushn ' ' (4 * d) ++ "}"
end

def Expr.render (d : Nat) (e : Expr) : String := e.renderTo d ""
def Arm.render (d : Nat) (a : Arm) : String := a.renderTo d ""
def Block.render (d : Nat) (b : Block) : String := b.renderTo d ""

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
    let out := joinTo s!"fn {n}(" ps ", " (fun (x, t) o => o ++ x ++ " : " ++ t.render)
    Block.renderTo 0 body (out ++ ") -> " ++ ret.render ++ " ") ++ "\n"
  | .raw t => t

end LeanToReussir.RR
