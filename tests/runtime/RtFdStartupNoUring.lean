/-! Runtime test: the descriptors open at startup when libuv may not use
io_uring (lean-runtime io-1 finding A821, section C). Lean 4.34.0 links
libuv 1.48.0, which creates its two io_uring rings only when
`uv__use_io_uring` holds (kernel 5.10.186 or later, overridden by
`UV_USE_IO_URING`); `RtFdStartupNoUring.pipe` sets `UV_USE_IO_URING=0`,
so natively 6 descriptors are open before `main`, not 8 (RtFdLimit). -/

def main : IO Unit := do
  let entries ← System.FilePath.readDir "/proc/self/fd"
  let mut fds : Array Nat := #[]
  for e in entries do
    if let some n := e.fileName.toNat? then fds := fds.push n
  -- The listing's own directory descriptor is the first free number.
  IO.println s!"open at startup: {fds.qsort (· < ·)}"
