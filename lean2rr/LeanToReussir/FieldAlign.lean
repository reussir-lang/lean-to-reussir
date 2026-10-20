import LeanToReussir.RR

/-!
# The alignment of a member as Reussir lays it out

The alignment in bytes of a value of a type as a member of a record or of
an enum arm, as Reussir lays it out (`memberStorageType` and
`deriveCompoundLayout` in Reussir's `lib/IR/ReussirTypes.cpp`). Two users
sort fields by decreasing alignment with it, so that no padding comes
between them:
- the record field order (`fieldAlign` in LowerBase, Opt/FieldOrder);
- the fields of Outline's step variants (`stepFieldOrder`).
-/

namespace LeanToReussir.RR

/-- The alignment in bytes of a value of type `t` as a member, or `none` if
the model does not know it. `types` gives the declaration of a generated or
prelude type by name (an `.enum` or `.struct` item; for a shared one only
the kind matters). Pointer-sized: what Reussir stores as a pointer or one
tagged word (a shared record or enum, a function value, a closure, an
opaque runtime type: `rrAlign8` in LowerBase lists them). A `[value]`
struct or enum is laid out in place: the largest alignment of its members
and, for an enum, of its tag (8 bits up to 256 variants, then 16, then 32:
Reussir's `getTagType`). So `struct [value] W(u8)` has alignment 1. -/
partial def fieldAlign? (types : String → Option Item) (t : Ty) (fuel : Nat := 8) : Option Nat :=
  let maxAlign (init : Nat) (fs : Array Ty) : Option Nat :=
    fs.foldlM (init := init) fun a f => return max a (← fieldAlign? types f (fuel - 1))
  match t with
  | .named n =>
    match n with
    | "u8" | "i8" | "bool" | "L2RUnit" => some 1
    | "u16" | "i16" => some 2
    | "u32" | "i32" | "f32" => some 4
    | "u64" | "i64" | "f64" | "Nat" | "Int" | "LStr" | "LHandle" | "LAny" => some 8
    | _ =>
      match types n with
      | some (.enum _ false _) | some (.struct _ false _) => some 8
      | some (.enum _ true vs) =>
        if fuel == 0 then none else
        let tag := if vs.size ≤ 256 then 1 else if vs.size ≤ 65536 then 2 else 4
        vs.foldlM (init := tag) fun a (_, fs) => maxAlign a fs
      | some (.struct _ true fs) => if fuel == 0 then none else maxAlign 1 fs
      | _ => none
  | .app n _ => if n ∈ ["RVec", "LRef", "LCell", "Cell"] then some 8 else none
  | .fn .. | .cls .. => some 8

end LeanToReussir.RR
