/-! Runtime test: the alignment of a `[value]` struct of sub-word fields in
a record (optimization `field-order`). A `mutual` block keeps Lean from
replacing a one-field structure by its field, so `W`, `WW` and `W4` are
`[value]` structs (`struct [value] T_W(u8)`). Reussir lays such a struct out
in place, with the largest alignment of its fields (size 1, alignment 1 for
`T_W`). lean2rr's field order counted every `[value]` struct as 8 bytes
aligned, so these records got padding (the variants as in the `.rr`, sizes
without the cell header):
- `P.mk (w : W) (n : Nat) (b : UInt8)` was `(T_W, Nat, u8)`, 24 bytes; now
  `(Nat, T_W, u8)`, 16 bytes;
- `Q.a (b : UInt8) (w : W4) (h : UInt16) (n : Nat) (ww : WW)` was
  `(T_W4, Nat, T_WW, u16, u8)`, 24 bytes; now `(Nat, T_W4, u16, u8, T_WW)`,
  16 bytes;
- `L.cons (ww : WW) (next : L) (s : String) (b : UInt8)` was
  `(T_WW, L, LStr, u8)`, 32 bytes; now `(L, LStr, T_WW, u8)`, 24 bytes;
- `T.node (next : T) (s : String) (w : W) (b : UInt8)` stays
  `(T, LStr, T_W, u8)`, 24 bytes (`w` came after the words already).
The program builds and reads values of each record (constructions,
patterns), and its output must be native's. -/

mutual
inductive W where
  | mk (x : UInt8)
inductive WW where
  | mk (w : W)
inductive W4 where
  | mk (x : UInt32)
inductive P where
  | mk (w : W) (n : Nat) (b : UInt8)
inductive Q where
  | z
  | a (b : UInt8) (w : W4) (h : UInt16) (n : Nat) (ww : WW)
inductive T where
  | nil
  | node (next : T) (s : String) (w : W) (b : UInt8)
inductive L where
  | nil
  | cons (ww : WW) (next : L) (s : String) (b : UInt8)
end

@[noinline] def mkP (i : Nat) : P := .mk ⟨i.toUInt8⟩ i (i+1).toUInt8
@[noinline] def mkQ (i : Nat) : Q :=
  if i == 0 then .z else .a i.toUInt8 ⟨i.toUInt32 * 100000⟩ (i * 300).toUInt16 (i*3) ⟨⟨(i+7).toUInt8⟩⟩
@[noinline] def mkT (n : Nat) : T := Id.run do
  let mut acc := T.nil
  for i in [0:n] do acc := .node acc "s" ⟨i.toUInt8⟩ (3*i).toUInt8
  return acc
@[noinline] def mkL (n : Nat) : L := Id.run do
  let mut acc := L.nil
  for i in [0:n] do acc := .cons ⟨⟨i.toUInt8⟩⟩ acc "ab" (2*i).toUInt8
  return acc

@[noinline] def sumP : P → Nat
  | .mk (.mk x) n b => x.toNat + n + b.toNat
@[noinline] def sumQ : Q → Nat
  | .z => 1
  | .a b (.mk w) h n (.mk (.mk x)) => b.toNat + w.toNat + h.toNat + n + x.toNat
@[noinline] def sumT : T → Nat
  | .nil => 0
  | .node t s (.mk x) b => s.length + x.toNat + b.toNat + sumT t
@[noinline] def sumL : L → Nat
  | .nil => 0
  | .cons (.mk (.mk x)) next s b => x.toNat + s.length + b.toNat + sumL next

def main : IO Unit := do
  let mut t := 0
  for i in [0:300] do
    t := t + sumP (mkP i) + sumQ (mkQ i)
  IO.println t
  IO.println (sumT (mkT 300))
  IO.println (sumL (mkL 300))
