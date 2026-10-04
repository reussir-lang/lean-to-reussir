/-!
Externs of the program in the `Array` namespace, used on containers whose
element type depends on a value (mono type `Array lcAny`). The optimization
`uniform-updates` runs `Array` externs there at their `lcAny` instances:
- `Array.pushTwice` and `Array.restart` run their Lean definitions (code
  instances): they are not extern instances, and must not be
  re-instantiated as ones (that would call their C symbols, which lean2rr
  never links). `Array.restart` uses none of its parameters, so Lean's
  `reduceArity` leaves its calls on the instance itself, which the pass
  sees as a call of an `Array` declaration whose persisted declaration is
  an extern;
- `Array.push0` names the runtime's `lean_array_push`; an extern of the
  program is never bound to Lean's runtime, so its definition runs too (a
  code instance, at `lcAny` as well).
Natively the C code in `RtExternUniform.ffi.c` and Lean's runtime run.
-/

@[extern "rt_uniform_push_twice"]
def Array.pushTwice {α : Type} (a : Array α) (v : α) : Array α := (a.push v).push v

@[extern "rt_uniform_restart"]
def Array.restart {α : Type} (_a : Array α) : Array α := #[]

@[extern "lean_array_push"]
def Array.push0 {α : Type} (a : Array α) (v : α) : Array α := a.push v

inductive Ty | nat | str
deriving BEq, Repr

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

structure Column where
  ty : Ty
  data : Array ty.denote

def Column.add (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, (d.pushTwice (i * 2^62)).push0 (i + 1)⟩
  | ⟨.str, d⟩ => ⟨.str, (d.pushTwice s!"s{i}").push0 "x"⟩

def Column.add1 (c : Column) (i : Nat) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.push0 i⟩
  | ⟨.str, d⟩ => ⟨.str, d.push0 s!"t{i}"⟩

def Column.restart (c : Column) : Column :=
  match c with
  | ⟨.nat, d⟩ => ⟨.nat, d.restart⟩
  | ⟨.str, d⟩ => ⟨.str, d.restart⟩

def Column.summary (c : Column) : String :=
  match c with
  | ⟨.nat, d⟩ => s!"nat {d.size} {d.foldl (· + ·) 0} {d.back?}"
  | ⟨.str, d⟩ => s!"str {d.size} {d.foldl (fun a s => a + s.length) 0} {d.back?}"

def main : IO Unit := do
  let mut cs : Array Column := #[⟨.nat, #[]⟩, ⟨.str, #[]⟩]
  for i in [0:300] do
    cs := cs.map (·.add i)
    cs := cs.map (·.add1 i)
    if i % 100 == 42 then cs := cs.map (·.restart)
  for c in cs do IO.println c.summary
