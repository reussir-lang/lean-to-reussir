/-! Runtime test (compact scalar arrays; review of arrays-compact, finding
F1): an array of boxes that arrives in a box (mono `lcAny`) is read at a
position that is no binder of the program, at a scalar array type. The
whole-program check must turn that kind off, else the box (an array of
boxes) is unboxed as a compact array (natively each prints its numbers; a
wrong check stopped the lean2rr build's run: "unreachable code").
- A typed-DSL universe (`Ty.denote`): `rep` builds an `Array t.denote`
  (mono `Array lcAny`), `len` matches on the code and reads the value with
  externs at `UInt64` (`Array.size`, `get!`): extern parameters.
- The same with the reads going to `ByteArray.mk` and `FloatArray.mk`
  (constructors that the runtime implements): their parameters.
- An array of boxes cast by a proved equation (no axiom, no `unsafe`) to
  `T b` and read in one branch by externs at `UInt64`, and put into a
  structure field `Array UInt64`: extern parameters and a constructor
  field. No binder of the program has a scalar array type there. -/

inductive Ty | u64 | nat | arr (t : Ty)

@[reducible] def Ty.denote : Ty → Type
  | .u64 => UInt64
  | .nat => Nat
  | .arr t => Array t.denote

@[noinline] def rep (t : Ty) (n : Nat) (x : t.denote) : (Ty.arr t).denote := Array.replicate n x

@[noinline] def len (t : Ty) (v : t.denote) : Nat :=
  match t, v with
  | .arr .u64, v => v.size + (v[1]!).toNat
  | .arr .nat, v => v.size + v[1]!
  | _, _ => 0

@[noinline] def go (t : Ty) (x : t.denote) : Nat := len (.arr t) (rep t 3 x)

inductive Ty2 | u8 | f64 | arr (t : Ty2)

@[reducible] def Ty2.denote : Ty2 → Type
  | .u8 => UInt8
  | .f64 => Float
  | .arr t => Array t.denote

@[noinline] def rep2 (t : Ty2) (n : Nat) (x : t.denote) : (Ty2.arr t).denote := Array.replicate n x

@[noinline] def len2 (t : Ty2) (v : t.denote) : Nat :=
  match t, v with
  | .arr .u8, v => (ByteArray.mk v).size
  | .arr .f64, v => (FloatArray.mk v).size + 100
  | _, _ => 0

@[noinline] def go2 (t : Ty2) (x : t.denote) : Nat := len2 (.arr t) (rep2 t 3 x)

def E : Bool → Type
  | true => UInt64
  | false => Nat

def T : Bool → Type
  | true => Array UInt64
  | false => Array Nat

theorem T_eq : ∀ b, Array (E b) = T b
  | true => rfl
  | false => rfl

@[noinline] def mkA (b : Bool) (n : Nat) (x : E b) : Array (E b) := Array.replicate n x

@[noinline] def mkT (b : Bool) (n : Nat) (x : E b) : T b := cast (T_eq b) (mkA b n x)

@[noinline] def useT (b : Bool) (a : T b) : Nat :=
  match b, a with
  | true, a => Array.size (α := UInt64) a + (Array.get!Internal (α := UInt64) a 1).toNat
  | false, a => Array.size (α := Nat) a + Array.get!Internal (α := Nat) a 1

structure S where
  d : Array UInt64
  k : Nat

@[noinline] def toS (b : Bool) (a : T b) : Option S :=
  match b, a with
  | true, a => some ⟨a, 1⟩
  | false, _ => none

def main : IO Unit := do
  IO.println (go .u64 (5 : UInt64))
  IO.println (go .nat (7 : Nat))
  IO.println (go2 .f64 (2.5 : Float))
  IO.println (go2 .u8 (5 : UInt8))
  IO.println (useT true (mkT true 3 (5 : UInt64)))
  IO.println (useT false (mkT false 2 (7 : Nat)))
  match toS true (mkT true 4 (9 : UInt64)) with
  | some s => IO.println s!"{s.d.size} {s.d[3]!} {s.k}"
  | none => IO.println "none"
