/-! Runtime test: allocations of promises (hunt HBOX2-03; with
`RtPromiseBoxAlloc.alloc`). `IO.Promise α` is `lcAny` in mono code, so
lean2rr passes each promise boxed. Its runtime type `LPromise` is a counted
pointer, the same FFI type as `LHandle`, so the box holds it directly;
before, lean2rr wrapped it in a cell of its own (an `ElemBox`), one more
allocation per promise. The argument is the number of promises, each made,
resolved and read. -/

@[noinline] def one (i : Nat) : IO Nat := do
  let p ← IO.Promise.new (α := Nat)
  p.resolve (i + 1)
  return p.result!.get

def main (args : List String) : IO Unit := do
  let n := (args.headD "10").toNat!
  let mut s := 0
  for i in [0:n] do
    s := s + (← one i)
  IO.println s
