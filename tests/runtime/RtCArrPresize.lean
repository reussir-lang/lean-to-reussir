/-! Runtime test (compact scalar arrays, plan "Why" and "Tests": the RSS
check for a presize-like program): lean-zip's `ByteArray.presize n` is
`ByteArray.mk (Array.replicate n 0)` (natively an `@[extern]` to C; here a
plain definition, so that the program does not count as casting). Mode
`bytes` presizes a buffer and fills it in place by an LZ77-like copy
within the buffer (`set!`/`get!`); mode `array` fills an `Array UInt8`
made by `Array.replicate` with `uset` and converts it with `ByteArray.mk`
at the end. Each prints the size, a checksum and probes. Natively the
replicated array is n boxed words (8n bytes) before `ByteArray.mk` copies
it into n bytes; with compact arrays it is n bytes, and `ByteArray.mk` is
the identity. `RtCArrPresize.alloc` runs n = 5 * 10^6 and 5 * 10^7 and
bounds lean2rr's peak memory at n = 5 * 10^7 by 120000 KB (the compact
buffer is 48828 KB; the boxed one alone 390625 KB). Arguments: a mode
(`bytes`, `array` or `both`, the default) and n (default 5 * 10^7). -/

@[noinline] def presize (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

/-- Literal bytes for the first 997 positions, then each byte is the one 997
before it plus one (an overlapping copy, as an LZ77 match). -/
@[noinline] def fillBytes (b : ByteArray) : ByteArray := Id.run do
  let mut b := b
  for i in [0:b.size] do
    b := b.set! i (if i < 997 then (i * 31 + 7).toUInt8 else b.get! (i - 997) + 1)
  return b

@[noinline] def fillArray (a : Array UInt8) : Array UInt8 := Id.run do
  let mut a := a
  for i in [0:a.size] do
    let j := i.toUSize
    if h : j.toNat < a.size then
      a := a.uset j (if i < 997 then (i * 31 + 7).toUInt8 else a[i - 997]! + 1) h
  return a

def checksum (b : ByteArray) : UInt64 := b.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 7

def report (tag : String) (b : ByteArray) : IO Unit :=
  IO.println s!"{tag} {b.size} {checksum b} {b.get! 0} {b.get! (b.size / 2)} {b.get! (b.size - 1)}"

def main (args : List String) : IO Unit := do
  let mode := args.head?.getD "both"
  let n := (args[1]? >>= String.toNat?).getD 50000000
  if mode == "bytes" || mode == "both" then
    report "bytes" (fillBytes (presize n))
  if mode == "array" || mode == "both" then
    report "array" (ByteArray.mk (fillArray (Array.replicate n 0)))
