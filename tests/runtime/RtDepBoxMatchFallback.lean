/-! Runtime test: a `match` on a dependent payload (`v : ty.listDenote`, a
family that is not reducible, so the payload's type is not known where it
is stored), for every way the payload can have been built (blowup audit
BA-17; branch fix-box-match's RtBoxMatchFallback): a list built by typed
code, a list built where its element type is an existential's field, an
empty list; patterns whose binders give the element type (`x :: _` at
`Nat`), give none (`| [] => … | _ => …`) or give an unknown one (a family
over an existential's type); nested patterns, a pair as the payload, a
tail returned, and the matched value used whole after the match (in the
alternative that reads its fields, in the default alternative, and after
an inner `match`). Each line prints what every reader computes. -/

inductive Ty | nat | str | pair

def Ty.listDenote : Ty → Type
  | .nat => List Nat
  | .str => List String
  | .pair => List (Nat × String)

def Ty.pairDenote : Ty → Type
  | .nat => Nat × List Nat
  | .str => String × String
  | .pair => List Nat × Nat

structure DL where
  ty : Ty
  v : ty.listDenote

structure DP where
  ty : Ty
  v : ty.pairDenote

@[noinline] def headDL (d : DL) : Nat :=
  match d with
  | ⟨.nat, x :: _⟩ => x + 1
  | ⟨.str, s :: _⟩ => s.length + 100
  | ⟨.pair, p :: _⟩ => p.1 + p.2.length + 1000
  | _ => 0

@[noinline] def twoDL (d : DL) : Nat :=
  match d with
  | ⟨.nat, x :: y :: _⟩ => x * 10 + y
  | ⟨.pair, (a, s) :: (b, t) :: _⟩ => a + b + s.length + t.length
  | _ => 7

@[noinline] def tailDL (d : DL) : List Nat :=
  match d with
  | ⟨.nat, _ :: t⟩ => t
  | _ => []

@[noinline] def emptyDL (d : DL) : Bool :=
  match d with
  | ⟨.nat, []⟩ => true
  | ⟨.str, []⟩ => true
  | _ => false

-- The matched list used whole in an alternative.
@[noinline] def wholeDL (d : DL) : Nat × List Nat :=
  match d with
  | ⟨.nat, v⟩ => (match (v : List Nat) with | x :: _ => x | [] => 0, v)
  | _ => (0, [])

-- ... in the default alternative, whose `cons` cell is not read ...
@[noinline] def dfltDL (d : DL) : List Nat :=
  match d with
  | ⟨.nat, v⟩ => match (v : List Nat) with
    | [] => [42]
    | _ => v
  | _ => []

-- ... and in the continuation of the inner match.
@[noinline] def jpDL (d : DL) (b : Bool) : List Nat :=
  match d with
  | ⟨.nat, v⟩ =>
    let r := match (v : List Nat) with
      | x :: _ => if b then x else x + 1
      | [] => 1
    r :: v
  | _ => []

@[noinline] def sumDP (d : DP) : Nat :=
  match d with
  | ⟨.nat, (a, l)⟩ => a + l.length
  | ⟨.str, (s, t)⟩ => s.length + t.length
  | ⟨.pair, (l, n)⟩ => l.foldl (· + ·) n

@[noinline] def fstDP (d : DP) : Nat :=
  match d with
  | ⟨.nat, (a, _)⟩ => a
  | _ => 0

-- A list built where its element type is a field (uniform code: a list of
-- boxes), boxed as it is through an equality.
structure Pkg where
  α : Type
  xs : List α
  ty : Ty
  h : ty.listDenote = List α

@[noinline] def Pkg.toDL (p : Pkg) : DL := ⟨p.ty, p.h ▸ p.xs⟩

structure PPkg where
  α : Type
  v : α × List α
  h : Ty.pairDenote .nat = (α × List α)

@[noinline] def PPkg.toDP (p : PPkg) : DP := ⟨.nat, p.h ▸ p.v⟩

-- Binders of unknown type: a family over an existential's type `α`.
def Ty.wrap : Ty → Type → Type
  | .nat, α => List α
  | .str, α => Option α
  | .pair, α => α × α

structure WP where
  α : Type
  ty : Ty
  v : ty.wrap α

@[noinline] def lenWP (w : WP) : Nat :=
  match w with
  | ⟨_, .nat, v⟩ => match v with
    | [] => 0
    | _ :: t => 1 + t.length
  | ⟨_, .str, v⟩ => match v with
    | some _ => 1
    | none => 0
  | _ => 2

@[noinline] def mk (b : Bool) (n : Nat) : DL :=
  if b then ⟨.nat, List.range n⟩ else ⟨.str, (List.range n).map toString⟩

@[noinline] def mkEmpty (b : Bool) : DL :=
  if b then ⟨.nat, ([] : List Nat)⟩ else ⟨.str, ([] : List String)⟩

def main (args : List String) : IO Unit := do
  let n := (args.headD "5").toNat!
  let xs := List.range n
  let ds : List DL := [⟨.nat, xs⟩, ⟨.str, xs.map (s!"s{·}")⟩, ⟨.pair, xs.map fun i => (i, s!"p{i}")⟩,
    ⟨.nat, []⟩, ⟨.str, []⟩, mk true n, mk false n, mkEmpty true, mkEmpty false,
    Pkg.toDL ⟨Nat, xs.map (· + 3), .nat, rfl⟩, Pkg.toDL ⟨String, ["u", "vw"], .str, rfl⟩,
    Pkg.toDL ⟨Nat × String, [(4, "four"), (5, "fv")], .pair, rfl⟩,
    Pkg.toDL ⟨Nat, [], .nat, rfl⟩, Pkg.toDL ⟨Nat, [8], .nat, rfl⟩]
  for d in ds do
    IO.println s!"{headDL d} {twoDL d} {tailDL d} {emptyDL d} {wholeDL d} {dfltDL d} {jpDL d true} {jpDL d false}"
  let ps : List DP := [⟨.nat, (n, xs)⟩, ⟨.str, ("ab", "cde")⟩, ⟨.pair, (xs, 9)⟩,
    PPkg.toDP ⟨Nat, (6, [1, 2, 3]), rfl⟩]
  for p in ps do IO.println s!"{sumDP p} {fstDP p}"
  let ws : List WP := [⟨Nat, .nat, (xs : List Nat)⟩, ⟨String, .nat, (["a"] : List String)⟩,
    ⟨Nat, .nat, ([] : List Nat)⟩, ⟨Nat, .str, some 3⟩, ⟨String, .str, (none : Option String)⟩, ⟨Nat, .pair, (1, 2)⟩]
  for w in ws do IO.println s!"{lenWP w}"
