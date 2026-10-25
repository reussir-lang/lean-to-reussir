import Lean
import LeanToReussir.Emit.Program

/-!
# The check of `--int-backend rcgmp` without `--rcgmp-type-args`

Under `--int-backend rcgmp` a `Nat` and an `Int` are Reussir's built-in
integers. At a type argument of a generic FFI function (a texture of the
prelude, `#[ffi(import)] fn f<T>(…)`), Reussir renders such a value as the
raw rcgmp handle and releases it after the call (its `rcgmp_handle` comes
from the substituted parameter type): a function that keeps its `T` (a
once-cell's value, an array's element, a box's payload) would keep a
handle that the caller releases. Reussir's local patch R2 passes an owned
handle there instead (`--rcgmp-type-args`). Without it the lowering keeps
`Nat` and `Int` out of those positions (`isFfiTypeArgTy`: an `ElemBox`
around the value; `natIntBoxFns?`: the boxes' own functions; the typed
arrays of `Nat` and `Int` off, `compactArrayKinds`).

This check makes sure none is left: it walks the finished program (the
generated items after `Outline` and the passes over them, and the
prelude's text after the backend's blocks are chosen) and stops lean2rr
with an internal error at
- a call of a generic FFI function of the prelude whose type argument
  mentions `Nat` or `Int` (`mentionsNatInt`: `Nat`, `RVec<Int>`; not a
  record of the program that holds one, which crosses as its own handle),
  also through a plain generic function of the prelude that passes that
  type parameter on to one (`ffiTypeParams`);
- a type `RVec<…>`, `LRef<…>` or `LCell<…>` of a `Nat` or `Int` anywhere
  (an array or cell of the runtime holds its elements through those FFI
  functions).

What: an automatic soundness check of a representation choice
(translation plan §5.1). Why: rcgmp's FFI glue at type arguments
(clean-integration step D, gap 1). Remove only if: the lowering without
`--rcgmp-type-args` is dropped (with Reussir's patch R2, which
scripts/l2r.py requires for rcgmp, the type arguments are owned handles),
or `rcgmp` is.
-/

namespace LeanToReussir
open Lean

/-- The characters of `cs` from position `i` up to the `>` that closes
the `<` before `i`: the text in between; `none` if it is not closed. -/
private def angleArgs (cs : Array Char) (i : Nat) : Option String := Id.run do
  let mut depth := 1
  for j in [i:cs.size] do
    let c := cs[j]!
    if c == '<' then depth := depth + 1
    else if c == '>' then
      depth := depth - 1
      if depth == 0 then return some (String.ofList (cs.extract i j).toList)
  return none

/-- The arguments of a type-argument list (the text between `<` and `>`),
split at its top-level commas. -/
private def splitTypeArgs (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth : Int := 0
  for c in s.toList do
    if c == ',' && depth == 0 then
      out := out.push cur.trimAscii.toString
      cur := ""
    else
      if c == '<' then depth := depth + 1
      if c == '>' then depth := depth - 1
      cur := cur.push c
  return out.push cur.trimAscii.toString

/-- The explicit generic calls and types in Reussir text `s`: each
identifier written right before `<…>`, with its type arguments (the
calls `f<A, B>(…)` and the applied types `RVec<A>`). Line comments (`//`
to the end of the line) are left out. -/
private def genericUses (s : String) : Array (String × Array String) := Id.run do
  let isId (c : Char) : Bool := c.isAlphanum || c == '_'
  let code := "\n".intercalate (s.splitOn "\n" |>.map fun l => (l.splitOn "//").head!)
  let cs := code.toList.toArray
  let mut out : Array (String × Array String) := #[]
  let mut start : Option Nat := none
  for i in [:cs.size] do
    let c := cs[i]!
    if isId c then
      if start.isNone then start := some i
    else
      if c == '<' then
        if let some st := start then
          if let some inner := angleArgs cs (i + 1) then
            out := out.push (String.ofList (cs.extract st i).toList, splitTypeArgs inner)
      start := none
  return out

/-- The prelude's generic functions whose type parameters Reussir's FFI
instantiates, with the indices of those parameters: every type parameter
of an `#[ffi(import)]` function, and those type parameters of a plain
generic function of the prelude that it passes on in an explicit type
argument to such a position (`l2r_rc_set_ref<T, R>` calls
`l2r_release_value_then<T, R>`), to a fixed point, or that its text
mentions in an `RVec`, `LRef` or `LCell` (`lean_array_fget<T>(a :
RVec<T>, …)`, whose calls of the FFI functions infer `T`). The functions
are found as `valueGenericPreludeFns` finds them: a line `fn name<…>` (or
`pub fn`), an FFI import when the line before it that is not blank is
`#[ffi(import)]`; a plain function's body is its lines from its `fn`
line (a one-line function has its body there) up to the next line that
starts an item. -/
def ffiTypeParams (prelude : String) : Std.HashMap String (Array Nat) := Id.run do
  -- (name, FFI import, type parameters, text)
  let mut fns : Array (String × Bool × Array String × String) := #[]
  let mut prev := ""
  let mut cur : Option (String × Bool × Array String × Array String) := none
  for line in prelude.splitOn "\n" do
    let decl := if line.startsWith "pub fn " then some (line.drop 7).toString
      else if line.startsWith "fn " then some (line.drop 3).toString else none
    let startsItem := decl.isSome || line.startsWith "#[" || line.startsWith "struct " ||
      line.startsWith "enum " || line.startsWith "pub struct " || line.startsWith "pub enum "
    if startsItem then
      if let some (n, ffi, gens, body) := cur then
        fns := fns.push (n, ffi, gens, "\n".intercalate body.toList)
      cur := none
    if let some rest := decl then
      let name := (rest.takeWhile fun c => c.isAlphanum || c == '_').toString
      let after := (rest.drop name.length).toString
      if after.startsWith "<" then
        let gens := ((after.drop 1).takeWhile (· != '>')).toString
        cur := some (name, prev.trimAscii.toString == "#[ffi(import)]",
          (gens.splitOn ",").toArray.map (·.trimAscii.toString), #[line])
    else if let some (n, ffi, gens, body) := cur then
      cur := some (n, ffi, gens, body.push line)
    unless line.all Char.isWhitespace do prev := line
  if let some (n, ffi, gens, body) := cur then
    fns := fns.push (n, ffi, gens, "\n".intercalate body.toList)
  let mut out : Std.HashMap String (Array Nat) := {}
  for (n, ffi, gens, _) in fns do
    if ffi then out := out.insert n (Array.range gens.size)
  -- A type parameter inside a runtime container (signature or body).
  for (n, ffi, gens, text) in fns do
    if ffi then continue
    let inCont := (genericUses text).filter fun (c, _) => c == "RVec" || c == "LRef" || c == "LCell"
    let ps := (Array.range gens.size).filter fun i =>
      inCont.any fun (_, args) => args.any fun a => (RR.parseTy a).any (·.subterms.contains (.named gens[i]!))
    unless ps.isEmpty do out := out.insert n ps
  -- Bodies: a type parameter passed on at such a position, to a fixed point.
  let mut changed := true
  while changed do
    changed := false
    for (n, ffi, gens, body) in fns do
      if ffi then continue
      let have_ := out.getD n #[]
      let mut ps := have_
      for (callee, args) in genericUses body do
        let some cps := out[callee]? | continue
        for j in cps do
          let some a := args[j]? | continue
          let some at_ := RR.parseTy a | continue
          for h : i in [:gens.size] do
            if !ps.contains i && at_.subterms.contains (.named gens[i]) then ps := ps.push i
      if ps.size != have_.size then
        out := out.insert n ps
        changed := true
  return out

/-- A use of `Nat` or `Int` that `rcgmp` without `--rcgmp-type-args` does
not allow: where (a function's name, or `prelude`) and what. -/
abbrev IntBackendViolation := String × String

mutual
  /-- The violations in expression `e` of function `fn`: calls of the FFI
  generics of `ffi` at a type that mentions `Nat` or `Int`. -/
  partial def intCheckExpr (ffi : Std.HashMap String (Array Nat)) (fn : String) (e : RR.Expr)
      (acc : Array IntBackendViolation) : Array IntBackendViolation :=
    match e with
    | .var _ | .atom _ => acc
    | .call f tys args =>
      let acc := match ffi[f]? with
        | some ps =>
          if ps.any (fun i => (tys[i]?.map mentionsNatInt).getD false) then
            acc.push (fn, s!"{f}<{", ".intercalate (tys.toList.map (·.render))}>")
          else acc
        | none => acc
      args.foldl (fun a x => intCheckExpr ffi fn x a) acc
    | .apply f a => intCheckExpr ffi fn a (intCheckExpr ffi fn f acc)
    | .ctor _ _ args => args.foldl (fun a x => intCheckExpr ffi fn x a) acc
    | .field e _ | .cast e _ => intCheckExpr ffi fn e acc
    | .lam _ _ b | .block b => intCheckBlock ffi fn b acc
    | .ite c t e => intCheckBlock ffi fn e (intCheckBlock ffi fn t (intCheckExpr ffi fn c acc))
    | .mtch s arms => arms.foldl (fun a arm => intCheckBlock ffi fn arm.body a) (intCheckExpr ffi fn s acc)
  partial def intCheckBlock (ffi : Std.HashMap String (Array Nat)) (fn : String) (b : RR.Block)
      (acc : Array IntBackendViolation) : Array IntBackendViolation :=
    intCheckExpr ffi fn b.result (b.lets.foldl (fun a (_, _, e) => intCheckExpr ffi fn e a) acc)
end

/-- The violations of a runtime container type (`RVec`, `LRef`, `LCell`)
of a `Nat` or `Int` among types `tys` of `where_`. -/
def intCheckTys (where_ : String) (tys : Array RR.Ty) (acc : Array IntBackendViolation) :
    Array IntBackendViolation :=
  tys.foldl (init := acc) fun acc t => t.subterms.foldl (init := acc) fun acc u =>
    match u with
    | .app n args =>
      if (n == "RVec" || n == "LRef" || n == "LCell") && args.any mentionsNatInt then acc.push (where_, u.render)
      else acc
    | _ => acc

/-- The violations in Reussir text `s` (the prelude, a raw item): explicit
FFI generic calls at a type that mentions `Nat` or `Int`, and runtime
containers of them. -/
def intCheckText (ffi : Std.HashMap String (Array Nat)) (where_ : String) (s : String)
    (acc : Array IntBackendViolation) : Array IntBackendViolation :=
  (genericUses s).foldl (init := acc) fun acc (f, args) =>
    let bad (a : String) : Bool := ((RR.parseTy a).map mentionsNatInt).getD false
    if (f == "RVec" || f == "LRef" || f == "LCell") && args.any bad then
      acc.push (where_, s!"{f}<{", ".intercalate args.toList}>")
    else match ffi[f]? with
      | some ps => if ps.any (fun i => (args[i]?.map bad).getD false) then
          acc.push (where_, s!"{f}<{", ".intercalate args.toList}>") else acc
      | none => acc

/-- The check (see the module comment), for a program translated with
`--int-backend rcgmp` and without `--rcgmp-type-args`: an internal error
naming the first uses left, if any. -/
def intBackendCheck (p : LoweredProgram) : CoreM Unit := do
  let ffi := ffiTypeParams p.prelude
  let mut bad : Array IntBackendViolation := intCheckText ffi "prelude" p.prelude #[]
  let items := p.typeItems ++ p.fnItems ++ p.stepItems ++ #[p.boxItem] ++ p.fns
  for it in items do
    match it with
    | .fn n _ _ body =>
      bad := intCheckTys n it.tys bad
      bad := intCheckBlock ffi n body bad
    | .raw t => bad := intCheckText ffi "raw item" t bad
    | .enum n .. | .struct n .. => bad := intCheckTys n it.tys bad
  if bad.isEmpty then return
  let shown := bad.extract 0 10 |>.map fun (w, what) => s!"  {what} in {w}"
  throwError "lean2rr: internal error: --int-backend rcgmp without --rcgmp-type-args: {bad.size} use(s) of \
    Nat or Int at a type argument of the runtime's generic FFI functions, or in its arrays and cells \
    (Reussir would pass a raw handle there and release it after the call; IntBackendCheck):\n\
    {"\n".intercalate shown.toList}"

end LeanToReussir
