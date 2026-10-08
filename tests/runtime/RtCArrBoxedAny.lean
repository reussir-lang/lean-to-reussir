/-! Runtime test (compact scalar arrays; found while checking hunt HCA-02):
a compact array that arrives in a box (mono `lcAny`) is read by an extern
whose parameter is an array of boxes (`Array lcAny`). The box is unboxed
there as an array of boxes, so the whole-program check must turn the kind
off (docs/implementation/representations/compact-arrays.md, "The
whole-program check turns a kind off", `posNode`). Before, `u64` stayed
on, and leanrt converted the array at each read (the safety net; with
`L2R_DEBUG_ARRAY_CONVERT=1` it printed `leanrt: compact array of kind 11
converted to boxes`). `mkT true` builds an `Array UInt64` in a typed
branch and returns it as `T true` (mono `lcAny`); `sizeT` and `lenT` read
it through a proved cast (no axiom, no `unsafe`) with `Array.size` and
`Array.toList` at `E b` (mono `lcAny`). -/
def E : Bool → Type
  | true => UInt64
  | false => Nat

def T : Bool → Type
  | true => Array UInt64
  | false => Array Nat

theorem T_eq : ∀ b, T b = Array (E b)
  | true => rfl
  | false => rfl

@[noinline] def mkT (b : Bool) (n : Nat) : T b :=
  match b with
  | true => ((Array.range n).map (·.toUInt64 + 0x8000000000000000) : Array UInt64)
  | false => (Array.range n : Array Nat)

@[noinline] def sizeT (b : Bool) (a : T b) : Nat := (cast (T_eq b) a : Array (E b)).size

@[noinline] def lenT (b : Bool) (a : T b) : Nat := (cast (T_eq b) a : Array (E b)).toList.length

def main : IO Unit := do
  IO.println s!"{sizeT true (mkT true 4)} {sizeT false (mkT false 3)}"
  IO.println s!"{lenT true (mkT true 5)} {lenT false (mkT false 2)}"
