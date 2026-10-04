/-! Runtime test: bytes read from a file (`IO.FS.readBinFile`, one
`Handle.read` of the file's size) land in the byte array itself, as
natively: the peak memory stays near the file's size, not twice it (review
RVA-01: the runtime read into a buffer and copied it into the array). The
`.pipe` makes a 64 MiB file; the program prints whether its peak resident
size (`VmHWM`) stayed under 1.5 times the file plus 32 MiB. -/
def vmHwmKB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for l in s.splitOn "\n" do
    if l.startsWith "VmHWM:" then
      return ((l.drop 6).trim.takeWhile Char.isDigit).toNat!
  return 0

def main (args : List String) : IO Unit := do
  let b ← IO.FS.readBinFile args.head!
  let hwm ← vmHwmKB
  IO.println s!"read {b.size} bytes, last {b[b.size - 1]!}"
  IO.println s!"peak under 1.5x: {decide (hwm * 1024 < b.size * 3 / 2 + 32 * 1024 * 1024)}"
  -- Other readers of the same path: a short read keeps working.
  let h ← IO.FS.Handle.mk args.head! .read
  let c ← h.read 10
  IO.println s!"chunk {c.size} {c.toList}"
  let r ← IO.getRandomBytes 1000
  IO.println s!"random {r.size}"
