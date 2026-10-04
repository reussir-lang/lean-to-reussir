/-! Runtime test: polymorphic code used at function and higher-order function
types where the code is uniform: rank-2 structure fields chosen at run time
applied to lists of functions, of functions over functions and of lists of
functions (and of UInt8 and Float); a method polymorphic in its own type from
a dictionary chosen at run time, at `Nat → Nat`, `(Nat → Nat) → Nat`,
`Nat × (Nat → Nat)` and UInt64; polymorphic recursion starting at function
types; nested datatypes (growth by a pair and by a list) carrying functions;
let-bound polymorphic functions at scalar, string and function types;
polymorphic functions applied to themselves; and static types nested 70
(a tuple) and 100 (an Option) levels deep, past the 64-level bound on type
arguments (plan §2.6).
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/higher_rank_poly, rank2_record_field,
poly_rank2_record_field, class_poly_method_erased_fn, let_polymorphic_fun,
local_fix_two_inst, let_poly_fn_instance, poly_fn_as_arg_tvar_leak,
curried_tvar_instantiation, poly_id_at_function_type,
nested_tree_pair_literal, non_uniform_pair_nest, non_uniform_list_nest,
deep_literal_nesting, type_level_tuple_fixpoint.
From the round-9 review, area crane (rv9/crane), program CrPoly. -/

namespace RtUniformFnTypes

-- rank-2 fields chosen at run time, used at function types
structure R2 where
  name : String
  f : {α : Type} → List α → List α
def r2s : List R2 := [⟨"rev", List.reverse⟩, ⟨"dup", fun xs => xs ++ xs⟩, ⟨"rot", fun xs => xs.drop 1 ++ xs.take 1⟩,
  ⟨"mid", fun xs => match xs with | a :: b :: r => b :: a :: r | l => l⟩]
@[noinline] def useR2 (r : R2) (k : Nat) : String :=
  let a := r.f [1, 2, k]
  let b := r.f ["x", "y"]
  let c := (r.f [(· + 1), (· * k), (· - 1)]).map (· 10)
  let d := (r.f [fun (g : Nat → Nat) => g ∘ g, fun g => g, fun g x => g x + g 0]).map (fun h => h (· + k) 1)
  let e := (r.f [[(· * 2)], [], [Nat.succ, Nat.pred]]).map (·.map (· 5))
  let f := (r.f [(1 : UInt8), 200, (k.toUInt8)]).map (· + 100)
  let g := (r.f [1.5, -0.0, k.toFloat])
  s!"{r.name}: {a} {b} {c} {d} {e} {f} {g}"

-- a method polymorphic in its own type, from a dictionary chosen at run time
class Mapper where mapf : {α : Type} → (α → α) → α → α
structure MPkg where
  name : String
  inst : Mapper
def mpkgs : List MPkg := [⟨"twice", ⟨fun f x => f (f x)⟩⟩, ⟨"thrice", ⟨fun f x => f (f (f x))⟩⟩, ⟨"id", ⟨fun _ x => x⟩⟩]
@[noinline] def useMapper (p : MPkg) (k : Nat) : String :=
  let _ := p.inst
  let a := Mapper.mapf (· + 3) k
  let b := Mapper.mapf (· ++ "s") "x"
  let c := Mapper.mapf (fun (g : Nat → Nat) => g ∘ g) (· * 2) 1
  let d := Mapper.mapf (fun (h : (Nat → Nat) → Nat) => fun g => h g + 1) (fun g => g k) (· + 1)
  let e := Mapper.mapf (fun (p : Nat × (Nat → Nat)) => (p.1 + 1, p.2 ∘ p.2)) (k, (· + 1))
  let f := Mapper.mapf (fun (u : UInt64) => u * 3) 7
  s!"{p.name}: {a} {b} {c} {d} {e.1} {e.2 0} {f}"

-- polymorphic recursion at a growing type, starting at a function type
def deep {α : Type} : Nat → α → (α → Nat) → Nat
  | 0, x, f => f x
  | n + 1, x, f => deep n (x, x) (fun p => f p.1 + f p.2)
def deepFn {α : Type} : Nat → α → (α → α) → (α → Nat) → Nat
  | 0, x, g, f => f (g x)
  | n + 1, x, g, f => deepFn n [x, g x] (List.map g) (fun l => l.foldl (fun a y => a + f y) 0)

-- nested datatypes carrying functions (growth by an index, Lean 4.34)
inductive Nest : Type → Type 1
  | leaf {α : Type} (x : α) : Nest α
  | node {α : Type} (n : Nest (α × α)) : Nest α
def Nest.collect {α : Type} (f : α → Nat) : Nest α → List Nat
  | .leaf x => [f x]
  | .node n => n.collect (fun p => f p.1 * 1000 + f p.2)
def Nest.build {α : Type} (x : α) (dup : α → α) : Nat → Nest α
  | 0 => .leaf x
  | n + 1 => .node (Nest.build (x, dup x) (fun p => (dup p.1, dup p.2)) n)
inductive NestL : Type → Type 1
  | leaf {α : Type} (x : α) : NestL α
  | node {α : Type} (n : NestL (List α)) : NestL α
def NestL.count {α : Type} (f : α → Nat) : NestL α → Nat
  | .leaf x => f x
  | .node n => n.count (fun l => l.foldl (fun a y => a + f y) 0)

-- let-bound polymorphic functions used at several types, scalar and functional
@[noinline] def letPoly (k : Nat) : String :=
  let pairUp := fun {α : Type} (x : α) => (x, x)
  let applyTwice := fun {α : Type} (f : α → α) (x : α) => f (f x)
  let a := pairUp k
  let b := pairUp "s"
  let c := pairUp (k.toUInt8 + 250)
  let d := pairUp (k.toFloat / 4)
  let e := pairUp (· + k)
  let f := applyTwice (fun (g : Nat → Nat) => g ∘ g) (· * 2) 1
  let g := applyTwice (· ++ "!") "hey"
  s!"{a} {b} {c} {d} {e.1 1} {e.2 2} {f} {g}"

-- a local recursive function used at two element types
@[noinline] def twoInst (k : Nat) : Nat × Nat :=
  let rec len {α : Type} : List α → Nat → Nat
    | [], a => a
    | _ :: r, a => len r (a + 1)
  (len (List.range k) 0, len ["a", "b"] 0 + len [(· + 1)] 0)

-- polymorphic functions passed to themselves
@[noinline] def twice {α : Type} (f : α → α) (x : α) : α := f (f x)
@[noinline] def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
@[noinline] def selfApp (k : Nat) : Nat × Nat × Nat × List (List Nat) :=
  (twice twice (· + k) 0, (twice (twice twice)) (· + 1) 0, (compose (compose (· + 1) (· * 2)) (· + 3) k),
   List.map (List.map (· + k)) [[1], [2, 3]])

-- a static type nested 70 and 130 levels deep (past the 64-level bound)
def T70 := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat ×
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat ×
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat ×
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
@[noinline] def mk70 (k : Nat) : T70 :=
  (k, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
   30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 64, 65, 66, 67, 68, k + 69)
@[noinline] def sum70 (t : T70) : Nat :=
  let (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29,
   a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59,
   a60, a61, a62, a63, a64, a65, a66, a67, a68, a69) := t
  a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18 + a19 + a20 + a21 + a22 + a23 + a24 + a25 + a26 + a27 + a28 + a29 +
   a30 + a31 + a32 + a33 + a34 + a35 + a36 + a37 + a38 + a39 + a40 + a41 + a42 + a43 + a44 + a45 + a46 + a47 + a48 + a49 + a50 + a51 + a52 + a53 + a54 + a55 + a56 + a57 + a58 + a59 +
   a60 + a61 + a62 + a63 + a64 + a65 + a66 + a67 + a68 + a69 * 1000
@[noinline] def lst70 (t : T70) : Nat := t.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
-- an Option nested 100 levels
def O100 := Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option (Option String)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
partial def depthOf {α : Type} (show' : α → String) : Nat → α → String
  | n, x => show' x ++ s!"@{n}"
@[noinline] def mkO (k : Nat) : O100 :=
  some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some ((if k > 100 then none else some s!"deep{k}"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
@[noinline] def peelO (o : O100) : String :=
  match o with
  | some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some (some s))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => s
  | _ => "short"

def main (args : List String) : IO Unit := do
  let k := args.length + 2
  for r in r2s do IO.println (useR2 r k)
  for p in mpkgs do IO.println (useMapper p k)
  IO.println s!"deep: {deep (5 + k) k id} {deep 3 (· + k) (· 1)} {deep 2 (fun (g : Nat → Nat) => g k) (· (· * 3))}"
  IO.println s!"deepFn: {deepFn 3 k (· + 1) id} {deepFn 2 (· * k) (fun g => g ∘ g) (· 1)}"
  IO.println s!"nest: {(Nest.build k (· + 1) 3).collect id} {(Nest.build (· + k) (fun g => g ∘ g) 2).collect (· 1)}"
  IO.println s!"nestL: {(NestL.node (.node (.leaf [[k, 1], [2]]))).count id} {(NestL.node (.leaf [(· + k), (· * k)])).count (· 10)}"
  IO.println s!"letPoly: {letPoly k}"
  IO.println s!"twoInst: {twoInst k}"
  IO.println s!"selfApp: {selfApp k}"
  let t := mk70 k
  IO.println s!"t70: {sum70 t} {lst70 t} {t.1} {(mk70 (k + 1)).2.2.2.1}"
  IO.println s!"o100: {peelO (mkO k)} {peelO (some none)}"

end RtUniformFnTypes

def main (args : List String) : IO Unit := RtUniformFnTypes.main args
