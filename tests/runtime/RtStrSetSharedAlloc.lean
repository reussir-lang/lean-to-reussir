/-! Runtime test (review HSTR-01): `String.Pos.Raw.set` on a shared string
copies it with room for its old length plus what the new character adds
(natively `lean_string_utf8_set` makes a new string of exactly its new
size). lean2rr copied it with room to double (as a push or an append
copies a shared string, natively too), so each modified copy of a shared
string cost its length again. The program keeps `n`
modified copies of one shared string of about 1000 characters (the
argument, default 100), one character replaced in each, by a two-byte one
in every 7th copy; tests/runtime/alloc-check.sh compares the bytes
requested and the peak memory at two sizes (RtStrSetSharedAlloc.alloc). -/
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 100
  let base := String.ofList (List.replicate (1000 + args.length) 'a')
  let mut acc : Array String := Array.mkEmpty n
  for i in [0:n] do
    let c := if i % 7 == 0 then 'é' else 'b'
    acc := acc.push (String.Pos.Raw.set base ⟨i % 1000⟩ c)
  IO.println (acc.foldl (fun k s => k + s.utf8ByteSize + s.length) 0)
