/-! Runtime test: string positions, indices and sizes at the edges of the
integer representations: below and at 2^60, 2^61 (rcgmp's immediates end
there), 2^62, 2^63 and 2^64. `next` and `prev` past the end give the
position plus or minus one, so their result can be any size; `get`,
`get?`, `extract`, `atEnd`, `isValid` and array reads treat a position or
index from 2^63 like one from 2^64 (out of range). Under
`--int-backend rcgmp` the prelude makes a size or a small position a `Nat`
through a mask to 61 bits and truncates indices to `i64`
(runtime/prelude.rr, `l2r_nat_size`). -/

@[noinline] def pos (n : Nat) : String.Pos.Raw := ⟨n⟩
@[noinline] def idx (n : Nat) : Nat := n

def edges : List Nat :=
  [0, 1, 2, 6, 7, 2^60 - 1, 2^60, 2^61 - 2, 2^61 - 1, 2^61, 2^62, 2^63 - 1, 2^63, 2^64 - 1, 2^64, 2^64 + 5]

def main : IO Unit := do
  let s := "héllo"
  let a := #[10, 20, 30]
  let b : ByteArray := ⟨#[1, 2, 3]⟩
  for n in edges do
    let p := pos n
    IO.println s!"{n}: next {(String.Pos.Raw.next s p).byteIdx} prev {(String.Pos.Raw.prev s p).byteIdx} get {String.Pos.Raw.get s p} get? {String.Pos.Raw.get? s p} atEnd {String.Pos.Raw.atEnd s p} valid {String.Pos.Raw.isValid s p} extract {String.Pos.Raw.extract s (pos 0) p}|{String.Pos.Raw.extract s p (pos 3)} arr {a[idx n]?} {a.getD (idx n) 0} bytes {b[idx n]?}"
  IO.println s!"sizes {s.utf8ByteSize} {s.length} {a.size} {b.size} {(FloatArray.mk #[1.0, 2.0]).size}"
