/-! Runtime test (review HA-01): `a[i]!` and `a.set! i v` out of bounds,
the panic message and the releases around it. Each released value holds
the last reference to a handle on /dev/stderr whose buffered line is
written when it closes; `RtArrayGetOobOrder.pipe` runs the program with
stdout and stderr on one pipe, then again with `LEAN_ABORT_ON_PANIC=1`.
- `get!`: natively the extern borrows the array, panics, and the caller
  releases the array after the call: the message, then handle A's line.
  lean2rr ended the read's view (freeing the array, its last reference)
  before the panic: A's line came first, and under `LEAN_ABORT_ON_PANIC`
  it was written although native writes only the message.
- `set!`: natively `lean_array_set_panic` releases the value first, then
  panics: B's line, then the message (lean2rr already agreed). -/

@[noinline] def mkArr (h : IO.FS.Handle) : Array (Option IO.FS.Handle) := #[some h]
@[noinline] def mkNone (n : Nat) : Array (Option IO.FS.Handle) := Array.replicate n none

def main : IO Unit := do
  -- get!: the array (the last reference to handle A) is lent to the
  -- extern; natively released after the call returns.
  let hA ← IO.FS.Handle.mk "/dev/stderr" .write
  hA.putStr "A: array of get! freed\n"
  let a := mkArr hA
  let x := a[5]!
  IO.eprintln s!"get! returned {x.isSome}"
  -- set!: the value (the last reference to handle B) is released first
  -- natively (lean_array_set_panic: lean_dec(v), then the panic).
  let hB ← IO.FS.Handle.mk "/dev/stderr" .write
  hB.putStr "B: value of set! freed\n"
  let b := mkNone 1
  let b := b.set! 7 (some hB)
  IO.eprintln s!"set! returned {b.size}"
