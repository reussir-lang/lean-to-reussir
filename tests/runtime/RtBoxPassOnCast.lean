/-! Runtime test: `box(0)` and words read at another type through
`unsafeCast` are passed on unchanged when the value only goes back into
boxes (lean2rr: `boxedOnlyVars`, `boxUnboxed?`), as native code passes the
object on. The units of a `List Unit` are `box(0)`: read as `Nat` they are
0, also after a copy. A `List Nat` read as `List UInt8` reads each word
truncated, and the copy keeps the words, so read back as `Nat` they are
the original values, as natively. -/

@[noinline] def rev {α : Type} (xs : List α) : List α := xs.reverse

@[noinline] def copy {α : Type} : List α → List α → List α
  | [], acc => acc.reverse
  | x :: xs, acc => copy xs (x :: acc)

@[noinline] unsafe def zeros : List Nat := unsafeCast [(), (), ()]

@[noinline] unsafe def asBytes (xs : List Nat) : List UInt8 := unsafeCast xs

@[noinline] unsafe def asNats (xs : List UInt8) : List Nat := unsafeCast xs

unsafe def main : IO Unit := do
  IO.println ((rev zeros).map (· + 1))
  IO.println ((copy zeros []).map (· + 5))
  let bs := asBytes [300, 7, 511]
  IO.println bs
  IO.println (rev bs)
  IO.println (asNats (rev bs))
  IO.println (asNats (copy bs []))
