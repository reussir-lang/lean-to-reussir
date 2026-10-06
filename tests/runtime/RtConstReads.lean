/-!
Constants read in loops, one of each kind of once-cell (docs/implementation/
startup/constants.md, "A read of a constant is one load"). Its output is
checked against native's like any test; `tests/runtime/const-read-check.sh`
also builds it to LLVM IR and fails when a read in one of its loops is a
call, or reads the slot through the runtime's slot record instead of the
table at a fixed address (lean-zip's decoder read its tables through two
calls each).

- `crcTable`: a table computed by a loop, a program constant (forced at
  startup, in its module's order);
- `lenBase`: a literal table (its body is a closed term);
- the literal array of `litSum`: a closed term of the loop's function (lazy:
  computed at its first read, as natively);
- `UInt64.size`: a toolchain constant (lazy), a big `Nat`;
- `mask`: a `UInt8` computed by a loop (a value smaller than a word);
- `zero64`, `zero8`: a `UInt64` 0 and a `UInt8` 0 (their words are 0: a
  read also loads the slot's set flag, and must give 0);
- `crc32` again inside a task.
-/

def crcTable : Array UInt32 := Id.run do
  let mut t := Array.mkEmpty 256
  for n in [0:256] do
    let mut c : UInt32 := n.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 != 0 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
    t := t.push c
  return t

def lenBase : Array UInt16 := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43,
  51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

def mask : UInt8 := Id.run do
  let mut m : UInt8 := 0
  for i in [0:5] do
    m := m ||| ((1 : UInt8) <<< i.toUInt8)
  return m

def zero64 : UInt64 := (List.range 3).foldl (fun a b => a * b.toUInt64) 1

def zero8 : UInt8 := (List.range 3).foldl (fun a b => a * b.toUInt8) 1

def crc32 (data : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for b in data do
    c := crcTable[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

def lenSum (data : ByteArray) : Nat := Id.run do
  let mut s := 0
  for b in data do
    s := s + (lenBase[b.toNat % 29]!).toNat
  return s

def litSum (data : ByteArray) : Nat := Id.run do
  let mut s := 0
  for b in data do
    let t : Array UInt8 := #[1, 2, 4, 8, 16, 32, 64, 128, 3, 5, 7]
    s := s + (t[b.toNat % 11]!).toNat
  return s

def bigMod (data : ByteArray) : Nat := Id.run do
  let mut s : Nat := 0
  for b in data do
    s := (s * 256 + b.toNat) % UInt64.size
  return s

def maskSum (data : ByteArray) : UInt64 := Id.run do
  let mut s : UInt64 := 0
  for b in data do
    s := s + (b &&& mask).toUInt64 + zero64 + (b * zero8).toUInt64
  return s

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 5000
  let data := ByteArray.mk (Array.ofFn (n := n) fun i => (i.val * 7 + 3).toUInt8)
  IO.println (crc32 data)
  IO.println (lenSum data)
  IO.println (litSum data)
  IO.println (bigMod data)
  IO.println (maskSum data)
  let t := Task.spawn fun _ => crc32 (data.push 1)
  IO.println t.get
  IO.println s!"{mask} {zero64} {zero8} {lenBase.size} {crcTable[255]!}"
