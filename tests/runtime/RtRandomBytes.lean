import Std.Internal.UV.System
/-! Runtime test: `IO.getRandomBytes` and libuv's `random`. Sizes only (and
that 16 bytes or more are not all zero); the errors native Lean reports: a byte
array that cannot exist is `ENOMEM`, libuv refuses more than 0x7FFFFFFF
bytes at once (`E2BIG`, before filling anything), and `/dev/urandom`
cannot be opened when no descriptor is left (`RtRandomBytes.pipe` runs the
program under `ulimit -n 64`; 0 bytes need no descriptor). -/

def showErr (label : String) (act : IO α) (fmt : α → String) : IO String := do
  try return s!"{label}: {fmt (← act)}" catch e => return s!"{label}: error: {e}"

partial def fill (acc : Array IO.FS.Handle) : IO (Array IO.FS.Handle) := do
  match ← (IO.FS.Handle.mk "/dev/null" .read).toBaseIO with
  | .ok h => if acc.size < 1000 then fill (acc.push h) else return acc
  | .error _ => return acc

def bytes (n : Nat) : IO String :=
  showErr s!"getRandomBytes {n}" (IO.getRandomBytes (USize.ofNat n)) fun b =>
    -- (16 random bytes are all zero with probability 2^-128)
    s!"{b.size} bytes" ++ if n ≥ 16 then s!", some nonzero {b.data.any (· != 0)}" else ""

def uvRandom (n : UInt64) : IO String := showErr s!"random {n}" (do
    let p ← Std.Internal.UV.System.random n
    match ← IO.wait p.result! with
    | .ok b => return s!"{b.size} bytes"
    | .error e => return s!"async error: {e}") id

def main : IO Unit := do
  for n in [0, 1, 16, 100000, 2^64 - 24, 2^64 - 1] do
    IO.println (← bytes n)
  for n in [0, 16, 0x80000000] do
    IO.println (← uvRandom n)
  let hs ← fill #[]
  IO.println (← bytes 16)
  IO.println (← bytes 0)
  IO.println s!"descriptors exhausted {decide (hs.size > 0)}"
