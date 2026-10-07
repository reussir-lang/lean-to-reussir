/-! Runtime test: long chains of values whose type is not known where they are
stored, built, read and freed at an 8 MB stack (RtDepDeep.pipe): building
and reading run in loops, and freeing must not take one stack frame per
level (natively each object is freed without recursion). Each chain has
N levels and is freed before the next is built:
- packages nested in each other through `NonScalar` (`Nest`: the next
  package cast to `NonScalar` and back with `unsafeCast`, natively the
  same object);
- a chain of `Dynamic` values each holding the next one (`Link`, read with
  `Dynamic.get?`), and a `List Dynamic` of N values;
- a tree deep along its left child at a type parameter (`TL Nat`, built by
  typed code, packed in an existential and walked there by code over the
  unknown type: the shape of blowup audit BA-00);
- chains through `Thunk α`, `Task α`, `IO.Ref α` (holding the next level
  as `NonScalar`), `Option α` and `Array α` (each level a structure holding
  the next one in that container), and options at an unknown type;
- closures each capturing the one before (built and freed; a few levels
  are called).
Argument: N (default 300000). -/

structure Nest where
  v : NonScalar
  d : Nat

@[noinline] unsafe def mkNest (n : Nat) : Nest := Id.run do
  let mut p : Nest := ⟨unsafeCast (7 : Nat), 0⟩
  for i in [0:n] do p := ⟨unsafeCast p, i + 1⟩
  return p

@[noinline] unsafe def sumNest (p : Nest) : Nat := go p 0
where
  go (p : Nest) (acc : Nat) : Nat :=
    if p.d == 0 then acc + (unsafeCast p.v : Nat) else go (unsafeCast p.v) (acc + p.d)

structure Link where
  tag : Nat
  next : Option Dynamic
  deriving TypeName

@[noinline] def mkLinks (n : Nat) : Dynamic := Id.run do
  let mut d : Dynamic := .mk (Link.mk 0 none)
  for i in [0:n] do d := .mk (Link.mk (i + 1) (some d))
  return d

@[noinline] partial def walkLinks (d : Dynamic) (acc : Nat) : Nat :=
  match d.get? Link with
  | some l => match l.next with
    | some n => walkLinks n (acc + l.tag)
    | none => acc + l.tag
  | none => acc + 1000000007

deriving instance TypeName for String

@[noinline] def mkDyns (n : Nat) : List Dynamic :=
  (List.range n).map fun i => if i % 3 == 0 then .mk (toString i) else .mk (Link.mk i none)

@[noinline] def sumDyns (l : List Dynamic) : Nat :=
  l.foldl (fun s d => match d.get? String, d.get? Link with
    | some t, _ => s + t.length
    | _, some k => s + k.tag
    | _, _ => s) 0

inductive TL (α : Type) where
  | leaf
  | node (l : TL α) (v : α) (r : TL α)

structure PkgTL where
  α : Type
  t : TL α
  f : α → Nat

@[noinline] def mkLeft (n : Nat) : TL Nat := Id.run do
  let mut acc : TL Nat := .leaf
  for i in [0:n] do acc := .node acc (i % 5) .leaf
  return acc

/-- Code over the unknown type, a loop down the left spine. -/
@[noinline] def PkgTL.walk (p : PkgTL) : Nat × Nat := go p.t 0 0
where
  go : TL p.α → Nat → Nat → Nat × Nat
    | .leaf, d, s => (d, s)
    | .node l v _, d, s => go l (d + 1) (s + p.f v)

-- Chains through generic containers.
structure TC where
  v : Nat
  next : Option (Thunk TC)

@[noinline] def mkTC (n : Nat) : TC := Id.run do
  let mut c : TC := ⟨0, none⟩
  for i in [0:n] do c := ⟨i + 1, some (Thunk.pure c)⟩
  return c

@[noinline] partial def sumTC (c : TC) (acc : Nat) : Nat :=
  match c.next with
  | some t => sumTC t.get (acc + c.v)
  | none => acc + c.v

structure KC where
  v : Nat
  next : Option (Task KC)

@[noinline] def mkKC (n : Nat) : KC := Id.run do
  let mut c : KC := ⟨0, none⟩
  for i in [0:n] do c := ⟨i + 1, some (.pure c)⟩
  return c

@[noinline] partial def sumKC (c : KC) (acc : Nat) : Nat :=
  match c.next with
  | some t => sumKC t.get (acc + c.v)
  | none => acc + c.v

/-- A reference cannot hold its own structure (not a positive occurrence):
the next level goes in as `NonScalar`. -/
structure RC where
  v : Nat
  next : Option (IO.Ref NonScalar)

@[noinline] unsafe def mkRC (n : Nat) : IO RC := do
  let mut c : RC := ⟨0, none⟩
  for i in [0:n] do c := ⟨i + 1, some (← IO.mkRef (unsafeCast c))⟩
  return c

@[noinline] unsafe def sumRC (c : RC) (acc : Nat) : IO Nat :=
  match c.next with
  | some r => do sumRC (unsafeCast (← r.get)) (acc + c.v)
  | none => return acc + c.v

inductive AC where
  | mk (v : Nat) (kids : Array AC)

@[noinline] def mkAC (n : Nat) : AC := Id.run do
  let mut c : AC := .mk 0 #[]
  for i in [0:n] do c := .mk (i + 1) #[c]
  return c

@[noinline] partial def sumAC (c : AC) (acc : Nat) : Nat :=
  match c with
  | .mk v kids => match kids[0]? with
    | some k => sumAC k (acc + v)
    | none => acc + v

/-- A chain of options at an unknown type: each level an existential. -/
structure OC (α : Type) where
  v : α
  next : Option (OC α)

@[noinline] def mkOC {α : Type} (x : α) (n : Nat) : OC α := Id.run do
  let mut c : OC α := ⟨x, none⟩
  for _ in [0:n] do c := ⟨x, some c⟩
  return c

@[noinline] partial def lenOC {α : Type} (c : OC α) (acc : Nat) : Nat :=
  match c.next with
  | some c => lenOC c (acc + 1)
  | none => acc

structure PkgOC where
  α : Type
  c : OC α

@[noinline] def PkgOC.len (p : PkgOC) : Nat := lenOC p.c 0

@[noinline] def mkClosures (n : Nat) : Nat → Nat := Id.run do
  let mut f : Nat → Nat := fun x => x + 1000
  for i in [0:n] do
    let g := f
    f := fun x => if x == 0 then i else g (x - 1)
  return f

unsafe def main (args : List String) : IO Unit := do
  let n := (args.headD "300000").toNat!
  IO.println s!"nest {sumNest (mkNest n)}"
  IO.println s!"links {walkLinks (mkLinks n) 0}"
  IO.println s!"dyns {sumDyns (mkDyns n)}"
  IO.println s!"left spine {PkgTL.walk ⟨Nat, mkLeft n, (· + 1)⟩}"
  IO.println s!"thunks {sumTC (mkTC n) 0}"
  IO.println s!"tasks {sumKC (mkKC n) 0}"
  IO.println s!"refs {← sumRC (← mkRC n) 0}"
  IO.println s!"arrays {sumAC (mkAC n) 0}"
  IO.println s!"options {PkgOC.len ⟨Nat, mkOC 5 n⟩} {PkgOC.len ⟨String, mkOC "s" n⟩}"
  let f := mkClosures n
  IO.println s!"closures {f 0} {f 3} {f 10}"
