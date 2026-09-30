import Lean
import LeanToReussir.RR
import LeanToReussir.Relevance
import LeanToReussir.Collect
import LeanToReussir.Mono

/-!
# Stage 4 foundations: state and type translation

Translation plan §5.1. Every mono type becomes a Reussir type:

* builtin types map to native Reussir types or runtime (prelude) types;
* erased types (`◾`, types as values) and the IO world (`lcVoid`) become
  `unit` — values of these types still occupy parameter positions, so
  arities are exactly Lean's;
* every other inductive becomes one generated nominal type per
  instantiation, keyed only by its *relevant* type arguments;
* function types become curried closures;
* `lcAny` (a type Lean itself does not know) becomes the uniform `Box`.
-/

namespace LeanToReussir
open Lean Compiler LCNF

/-- Layout of one constructor of a generated nominal type. -/
structure CtorLayout where
  /-- Reussir variant name (enums) — unused for structs. -/
  variant : String
  /-- Number of inductive parameters (leading arguments of a constructor
  application, dropped). -/
  numParams : Nat
  /-- One entry per Lean field: `some (i, ty)` when the field is relevant
  (its position among the Reussir fields and its type), `none` when it is
  erased and has no representation. -/
  fields : Array (Option (Nat × RR.Ty))

inductive Shape where
  /-- All constructors without relevant fields: `enum [value]`. -/
  | enumLike
  /-- One constructor: `struct`. -/
  | struct
  /-- Several constructors, some with fields: `enum`. -/
  | enum
  deriving BEq, Inhabited

structure TypeInfo where
  name : String
  shape : Shape
  ctors : NameMap CtorLayout
  /-- Constructor names in declaration order. -/
  ctorOrder : Array Name

structure LowerCtx where
  table : RelevanceTable
  /-- The mono declarations of the program (code and extern instances). -/
  decls : NameMap (Decl .pure)
  /-- Instance name ↦ instance key (original declaration and type arguments). -/
  keys : NameMap InstKey

structure LowerState where
  /-- Mono type (keyed by relevant arguments) ↦ generated type name. -/
  typeNames : Std.HashMap Expr String := {}
  typeInfos : Std.HashMap String TypeInfo := {}
  /-- Generated type name ↦ the (keyed) Lean type it represents, for diagnostics. -/
  typeKeys : Std.HashMap String Expr := {}
  /-- Generated type items, in creation order. -/
  typeItems : Array RR.Item := #[]
  /-- Variants of the uniform `Box` type: boxed Reussir type ↦ variant name. -/
  boxVariants : Array (RR.Ty × String) := #[]
  /-- Generated `[value]` structs carrying several join-point arguments. -/
  tupleTypes : Std.HashMap (Array RR.Ty) String := {}
  /-- Generated functions (declarations and outlined join points). -/
  fns : Array RR.Item := #[]
  /-- Nominal types that some `Box` value is unboxed to (converter bodies
  are generated at the end, once all `Box` variants are known). -/
  unboxTargets : Array String := #[]
  /-- Next once-cell slot for constants. -/
  cafSlots : Nat := 0
  /-- Structural conversions being generated (for recursive types). -/
  convsInProgress : Std.HashSet String := {}
  /-- Generated placeholder (`box(0)`) functions, per type. -/
  zeroFns : Std.HashMap RR.Ty String := {}
  /-- Placeholder functions whose body is being generated. -/
  zeroBusy : Std.HashSet RR.Ty := {}
  /-- String literals of the program, by id (see `strLit`). -/
  strLits : Array String := #[]
  strLitIds : Std.HashMap String Nat := {}
  /-- Generated element-wise array conversions, per (source, target) storage. -/
  vecConvs : Std.HashMap (RR.Ty × RR.Ty) String := {}
  counter : Nat := 0

abbrev LowerM := ReaderT LowerCtx (StateRefT LowerState CoreM)

def fresh (pre : String) : LowerM String := do
  let n := (← get).counter
  modify fun s => { s with counter := n + 1 }
  return s!"{pre}{n}"

/-- An identifier-safe rendering of a Lean name, for readable hints in
generated names (uniqueness always comes from a numeric component). -/
def nameHint (n : Name) : String :=
  let s := n.toString (escape := false)
  let s := s.map fun c => if c.isAlphanum then c else '_'
  if s.length > 40 then (s.drop (s.length - 40)).toString else s

/-- Reussir function name of a Lean declaration (Lean's own C mangling,
which is injective and yields valid identifiers). -/
def fnName (n : Name) : String := n.mangle "l_"

def boxName : String := "L2RBox"

/-- The uniform type. -/
def RR.Ty.box : RR.Ty := .named boxName

/-- Types that may cross Reussir's FFI boundary as parameters: integers,
floats, `bool`, and RC pointers (opaque runtime types and shared records). -/
def isBoundaryTy (t : RR.Ty) : LowerM Bool := do
  match t with
  | .named n =>
    if n ∈ ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64", "bool",
            "LStr", "LBig", boxName] then return true
    match (← get).typeInfos[n]? with
    | some info => return info.shape != .enumLike
    | none => return false
  | .app n _ => return n == "RVec" || n == "LRef"
  | .fn .. => return false

/-- The element type stored in a runtime array: values that cannot cross the
FFI boundary are wrapped in a one-field shared struct (Lean boxes array
elements too). -/
def arrayElemTy (t : RR.Ty) : LowerM (RR.Ty × Bool) := do
  if ← isBoundaryTy t then return (t, false)
  let key := #[t, .named "__elem_box"]
  if let some n := (← get).tupleTypes[key]? then return (.named n, true)
  let n ← fresh "ElemBox"
  modify fun s => { s with
    tupleTypes := s.tupleTypes.insert key n
    typeItems := s.typeItems.push (.struct n false #[t]) }
  return (.named n, true)

/-- The element type an array storage type holds, and whether the storage
is a one-field wrapper (see `arrayElemTy`). -/
def storageElem (st : RR.Ty) : LowerM (RR.Ty × Bool) := do
  let .named n := st | return (st, false)
  for (k, v) in (← get).tupleTypes.toList do
    if v == n && k.size == 2 && k[1]! == .named "__elem_box" then return (k[0]!, true)
  return (st, false)

/-- A string literal: `l2r_str_lit(id)`, which builds the string from a
table of byte strings generated with the program (`strLitTable`). Passing
a Reussir `str` to the runtime would go through a stack slot whose address
escapes, which keeps LLVM from turning tail calls of the enclosing function
into loops. -/
def strLit (s : String) : LowerM RR.Expr := do
  let id ← match (← get).strLitIds[s]? with
    | some id => pure id
    | none =>
      let id := (← get).strLits.size
      modify fun st => { st with strLits := st.strLits.push s, strLitIds := st.strLitIds.insert s id }
      pure id
  return .call "l2r_str_lit" #[] #[.atom (toString id)]

/-- The runtime function behind `strLit`: the literals as Rust byte strings. -/
def strLitTable (lits : Array String) : String :=
  let hex := "0123456789abcdef".toList.toArray
  let esc (s : String) : String := s.toUTF8.foldl (init := "") fun acc b =>
    if b ≥ 0x20 && b < 0x7f && b != 0x22 && b != 0x5c then acc.push (Char.ofNat b.toNat)
    else acc ++ "\\x" |>.push hex[(b / 16).toNat]! |>.push hex[(b % 16).toNat]!
  let items := lits.toList.map fun s => s!"b\"{esc s}\""
  "#[ffi(import)]\nfn l2r_str_lit(id : u64) -> LStr [{ {\n" ++
  s!"    const LITS: &[&[u8]] = &[{", ".intercalate items}];\n" ++
  "    leanrt::string::from_bytes(LITS[id as usize])\n} }];\n"

/-- Relevance of the parameters of inductive `ind` (see `Relevance.lean`). -/
def relevanceOf (ind : Name) (numParams : Nat) : LowerM (Array Bool) := do
  match (← read).table.find? ind with
  | some r => return r
  | none => return Array.replicate numParams true

mutual
  /-- Translate a mono type. -/
  partial def lowerType (e : Expr) : LowerM RR.Ty := do
    let e := e.consumeMData.headBeta
    match e with
    | .forallE _ d b _ => return .fn (← lowerType d) (← lowerType (b.instantiate1 anyExpr))
    | .sort _ => return .unit
    | .const .. | .app .. =>
      match e.getAppFn with
      | .const n _ => lowerTypeApp n e.getAppArgs
      | _ => return RR.Ty.box
    | _ => return RR.Ty.box

  partial def lowerTypeApp (n : Name) (args : Array Expr) : LowerM RR.Ty := do
    match n with
    | ``UInt8 => return .named "u8"
    | ``UInt16 => return .named "u16"
    | ``UInt32 => return .named "u32"
    | ``UInt64 | ``USize => return .named "u64"
    | ``Float => return .named "f64"
    | ``Float32 => return .named "f32"
    | ``Bool => return .bool
    | ``Unit | ``PUnit | ``lcVoid | ``lcErased => return .unit
    | ``lcAny => return RR.Ty.box
    | ``Nat => return .named "Nat"
    | ``Int => return .named "Int"
    | ``String => return .named "LStr"
    | ``ByteArray => return .app "RVec" #[.named "u8"]
    | ``FloatArray => return .app "RVec" #[.named "f64"]
    | ``Array =>
      let elem ← match args[0]? with
        | some a => lowerType a
        | none => pure RR.Ty.box
      let (elem, _) ← arrayElemTy elem
      return .app "RVec" #[elem]
    | _ =>
      -- An inductive with computed fields is represented by its
      -- implementation inductive `T._impl` (whose constructors also store
      -- the computed fields); mono code uses both names for the same values.
      if let some (.inductInfo ival) := (← getEnv).find? (n ++ `_impl) then
        return ← nominalType ival args
      match (← getEnv).find? n with
      | some (.inductInfo ival) => nominalType ival args
      | _ => return RR.Ty.box

  /-- The generated nominal type for an instantiated inductive. -/
  partial def nominalType (ival : InductiveVal) (args : Array Expr) : LowerM RR.Ty := do
    let rel ← relevanceOf ival.name ival.numParams
    -- Phantom (irrelevant) arguments do not create distinct types.
    let keyArgs := (List.range ival.numParams).toArray.map fun i =>
      if rel.getD i true then (args[i]?.getD anyExpr).consumeMData else erasedExpr
    let key := mkAppN (.const ival.name []) keyArgs
    if let some n := (← get).typeNames[key]? then return .named n
    let name ← fresh s!"T_{nameHint ival.name}_"
    modify fun s => { s with typeNames := s.typeNames.insert key name, typeKeys := s.typeKeys.insert name key }
    -- Constructor layouts, fields translated through Lean's own `toMonoType`
    -- so representation decisions (trivial structures, `Decidable`, …) match.
    let mut ctors : NameMap CtorLayout := {}
    let mut variants : Array (String × Array RR.Ty) := #[]
    for ctorName in ival.ctors do
      let ctorTy ← getOtherDeclBaseType ctorName []
      let mut ty ← instantiateForall ctorTy (args[:ival.numParams].toArray.map (·.consumeMData))
      let mut fields := #[]
      let mut rrFields := #[]
      repeat
        match ty.headBeta with
        | .forallE _ d b _ =>
          let mono ← toMonoType d
          if mono.isErased || mono == mkConst ``lcVoid then
            fields := fields.push none
          else
            let t ← lowerType mono
            fields := fields.push (some (rrFields.size, t))
            rrFields := rrFields.push t
          ty := b.instantiate1 anyExpr
        | _ => break
      -- The constructor's name relative to its type (`T.c._impl` for the
      -- constructors of a computed-field implementation `T._impl`).
      let base := match ival.name with | .str p "_impl" => p | n => n
      let rel := (ctorName.replacePrefix base .anonymous).toString (escape := false)
      let variant := "c_" ++ (rel.map fun c => if c.isAlphanum then c else '_')
      ctors := ctors.insert ctorName { variant, numParams := ival.numParams, fields }
      variants := variants.push (variant, rrFields)
    let shape :=
      if variants.all (·.2.isEmpty) then Shape.enumLike
      else if variants.size == 1 then Shape.struct
      else Shape.enum
    let item := match shape with
      | .enumLike => RR.Item.enum name true (if variants.isEmpty then #[("c_impossible", #[])] else variants)
      | .struct => RR.Item.struct name false variants[0]!.2
      | .enum => RR.Item.enum name false variants
    modify fun s => { s with
      typeInfos := s.typeInfos.insert name { name, shape, ctors, ctorOrder := ival.ctors.toArray }
      typeItems := s.typeItems.push item }
    return .named name
end

/-- The variant of `Box` holding values of type `t`. -/
def boxVariant (t : RR.Ty) : LowerM String := do
  if let some (_, v) := (← get).boxVariants.find? (·.1 == t) then return v
  let v := s!"b{(← get).boxVariants.size}"
  modify fun s => { s with boxVariants := s.boxVariants.push (t, v) }
  return v

/-- The uniform instance of an inductive: every relevant type argument is
`lcAny` (so data of those types is stored as `Box`). -/
def uniformType (ind : Name) : LowerM RR.Ty := do
  let some (.inductInfo ival) := (← getEnv).find? ind | return RR.Ty.box
  lowerTypeApp ind ((List.range ival.numParams).toArray.map fun _ => anyExpr)

/-- Name of the generated function converting a `Box` to nominal type `t`
(its body is generated at the end). -/
def unboxFn (t : String) : LowerM String := do
  unless (← get).unboxTargets.contains t do
    modify fun s => { s with unboxTargets := s.unboxTargets.push t }
  return s!"l2r_unbox_{t}"

/-- A `[value]` struct type carrying several join-point arguments. -/
def tupleType (tys : Array RR.Ty) : LowerM String := do
  if let some n := (← get).tupleTypes[tys]? then return n
  let n ← fresh "Tuple"
  modify fun s => { s with
    tupleTypes := s.tupleTypes.insert tys n
    typeItems := s.typeItems.push (.struct n true tys) }
  return n

/-- Relevance for every inductive mentioned by the program's types. -/
def programRelevance (decls : Array (Decl .pure)) : CoreM RelevanceTable := do
  let env ← getEnv
  let inds := decls.foldl (fun s d => foldDeclTypes (addInductives env) d s) ({} : NameSet)
  let inds := closeInductives env inds
  let (table, _) ← Meta.MetaM.run' <| computeRelevance inds.toArray
  return table

end LeanToReussir
