/-! Runtime test (known failure): a `List Nat` read as `List UInt8` through
`unsafeCast`, whose head is used both at `UInt8` and put back into a
list. Natively the list cell gets the head's object unchanged (the word
of 300), so read back as `Nat` it is 300. lean2rr unboxes the head once at
`UInt8` (300 becomes 44) for the addition and boxes that `UInt8` again for
the new cell: read back as `Nat` it is 44. -/

@[noinline] def bump {α : Type} [Add α] [OfNat α 1] : List α → List α × List α
  | [] => ([], [])
  | x :: r => ([x + 1], r ++ [x])

@[noinline] unsafe def asBytes (xs : List Nat) : List UInt8 := unsafeCast xs

@[noinline] unsafe def asNats (xs : List UInt8) : List Nat := unsafeCast xs

unsafe def main : IO Unit := do
  let (a, b) := bump (asBytes [300, 7])
  IO.println a
  IO.println (asNats b)
