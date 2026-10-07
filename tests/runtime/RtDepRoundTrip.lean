/-! Runtime test: references and function values that go through code that
does not know their type and come back. A reference keeps its identity
wherever it is stored: a value set through one alias is seen through every
other alias. Each reference below is stored in an existential package, a
dependent field, a `List α`, an `Array α`, an `Option α`, a thunk, a
task's result, a closure, a value built by polymorphic recursion and an
`IO.Promise`'s value; code over the unknown type sets or modifies it,
and typed code reads it through the original alias (and the other way
round). An `ST.Ref` does the same inside `runST`. Function values (a
closure over a counter reference, a partial application, a closure over a
`Float`) go typed → uniform → typed and are called after each crossing: the
calls must hit the same counter. Native Lean prints the values each alias
sees. -/

structure RPk where
  α : Type
  r : IO.Ref α
  v : α
  f : α → Nat

/-- Code over the unknown type: sets the reference to the package's value. -/
@[noinline] def RPk.set (p : RPk) : IO Unit := p.r.set p.v

@[noinline] def RPk.read (p : RPk) : IO Nat := return p.f (← p.r.get)

/-- Modifies every reference of a list, at an unknown element type. -/
@[noinline] def bumpAll {α : Type} (rs : List (IO.Ref α)) (g : α → α) : IO Unit := rs.forM (·.modify g)

structure LPk where
  α : Type
  rs : List (IO.Ref α)
  arr : Array (IO.Ref α)
  opt : Option (IO.Ref α)
  g : α → α

@[noinline] def LPk.run (p : LPk) : IO Unit := do
  bumpAll p.rs p.g
  for r in p.arr do r.modify p.g
  if let some r := p.opt then r.modify p.g

inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure DRef where
  ty : Ty
  r : IO.Ref ty.denote

@[noinline] def DRef.bump (d : DRef) : IO Unit :=
  match d with
  | ⟨.nat, r⟩ => r.modify (· + 1000)
  | ⟨.str, r⟩ => r.modify (· ++ "!")

/-- References carried along a recursion at a growing type. -/
def nestRefs {α : Type} (set : α → IO Unit) : Nat → α → IO Unit
  | 0, x => set x
  | n + 1, x => nestRefs (fun (p : α × α) => do set p.1; set p.2) n (x, x)

structure FPk where
  α : Type
  f : α
  call : α → Nat → IO Nat

@[noinline] def FPk.callTwice (p : FPk) (x : Nat) : IO Nat := do
  return (← p.call p.f x) + (← p.call p.f (x + 1))

@[noinline] def FPk.repack (p : FPk) : FPk := ⟨p.α, p.f, p.call⟩

structure DFn where
  ty : Ty
  f : ty.denote → ty.denote

@[noinline] def DFn.via (d : DFn) : DFn := ⟨d.ty, d.f⟩

/-- Each call bumps the counter: every call must reach this closure. -/
@[noinline] def counterFn (c : IO.Ref Nat) : Nat → IO Nat := fun x => do
  let k ← c.modifyGet fun k => (k, k + 1)
  return x * 10 + k

/-- An `ST.Ref` stored twice in a list and modified through both. -/
@[noinline] def stRefs (n : Nat) : Nat := runST fun σ => do
  let x : ST.Ref σ Nat ← ST.mkRef n
  let y := [x, x]
  for z in y do z.modify (· * 2)
  x.get

@[noinline] def addThree (a b c : Nat) : Nat := a + 2 * b + 3 * c

def main : IO Unit := do
  -- an existential package
  let r ← IO.mkRef (0 : Nat)
  RPk.set ⟨Nat, r, 42, id⟩
  IO.println s!"pkg set: {← r.get}"
  r.set 7
  IO.println s!"pkg read: {← RPk.read ⟨Nat, r, 0, (· * 2)⟩}"
  let s ← IO.mkRef "a"
  RPk.set ⟨String, s, "bb", String.length⟩
  IO.println s!"pkg string: {← s.get}"
  -- lists, arrays, options of references
  let r1 ← IO.mkRef (1 : Nat)
  let r2 ← IO.mkRef (2 : Nat)
  LPk.run ⟨Nat, [r1, r2, r1], #[r2, r1], some r2, (· * 3)⟩
  IO.println s!"containers: {← r1.get} {← r2.get}"
  -- a dependent field
  let rn ← IO.mkRef (5 : Nat)
  let rs ← IO.mkRef "x"
  for d in [DRef.mk .nat rn, ⟨.str, rs⟩, ⟨.nat, rn⟩] do d.bump
  IO.println s!"dependent: {← rn.get} {← rs.get}"
  -- a thunk, a task, a closure
  let th : Thunk (IO.Ref Nat) := Thunk.pure r
  let tk : Task (IO.Ref Nat) := Task.spawn fun _ => r
  let cl : Unit → IO.Ref Nat := fun _ => r
  RPk.set ⟨Nat, th.get, 100, id⟩
  RPk.set ⟨Nat, tk.get, (← r.get) + 1, id⟩
  (cl ()).modify (· + 1)
  IO.println s!"thunk task closure: {← r.get}"
  -- polymorphic recursion
  let acc ← IO.mkRef (0 : Nat)
  nestRefs (fun (k : IO.Ref Nat) => k.modify (· + 1)) 4 acc
  IO.println s!"nest: {← acc.get}"
  -- a promise resolved through a package
  let pr ← IO.Promise.new (α := IO.Ref Nat)
  pr.resolve r
  let rr := pr.result!.get
  rr.set 55
  IO.println s!"promise: {← r.get} {← RPk.read ⟨Nat, rr, 0, id⟩}"
  -- ST.Ref
  IO.println s!"st: {stRefs 10}"
  -- function values
  let c ← IO.mkRef (0 : Nat)
  let f := counterFn c
  let p1 : FPk := ⟨Nat → IO Nat, f, fun g x => g x⟩
  let a ← p1.callTwice 1
  let b ← p1.repack.repack.callTwice 2
  IO.println s!"fn: {a} {b} {← f 9} {← c.get}"
  let p2 : FPk := ⟨Nat → Nat → Nat, addThree 1, fun g x => return g x x⟩
  IO.println s!"pap: {← p2.callTwice 3} {← p2.repack.callTwice 4}"
  let fl : Float := 2.5
  let d1 : DFn := ⟨.nat, fun x => x + fl.toUInt64.toNat⟩
  let d2 : DFn := ⟨.str, fun s => s ++ toString fl⟩
  match d1.via.via, d2.via with
  | ⟨.nat, g⟩, ⟨.str, h⟩ => IO.println s!"dfn: {g 1} {h "v"}"
  | _, _ => IO.println "dfn: ?"
