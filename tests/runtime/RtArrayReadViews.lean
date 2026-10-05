/-! Runtime test: array and string reads. A read gives its reference to the
array up first, for a view (the array's block, which the read frees when it
held the last reference), then checks the bounds and takes the element or
ends the view. Reads that consume the last reference to a fresh array and
reads of an array used again, for each element representation (`Array Nat`
and `Array Int` with big elements, strings, structures, `UInt64`,
`ByteArray`, `FloatArray`): `a[i]'h`, `a[i]!` in bounds and out of bounds
(a small and a big index: the panic and the default; `ByteArray` and
`FloatArray` answer 0 without one), folds (`uget`); string reads at
positions a proof keeps valid (`String.foldl`) and at raw positions, also
big ones. -/

structure Q where
  s : String
  n : Nat
deriving Repr, Inhabited

@[noinline] def natArr (k : Nat) : Array Nat := #[k, 2^64 + k, k + 1, 2^70]
@[noinline] def intArr (k : Nat) : Array Int := #[-(k : Int), -(2^64 : Int) - k, k]
@[noinline] def strArr (k : Nat) : Array String := #[s!"a{k}", s!"bb{k}", "c"]
@[noinline] def qArr (k : Nat) : Array Q := #[⟨s!"q{k}", k⟩, ⟨"r", 2^65 + k⟩]
@[noinline] def u64Arr (k : Nat) : Array UInt64 := #[k.toUInt64, 7, 0xFFFFFFFFFFFFFFFF]
@[noinline] def bytes (k : Nat) : ByteArray := ⟨#[k.toUInt8, 200, 3]⟩
@[noinline] def floats (k : Nat) : FloatArray := ⟨#[k.toFloat, 2.5, -0.0]⟩
@[noinline] def str (k : Nat) : String := s!"xλ{k}€y"

-- Reads at an index a proof keeps in bounds, each the last use of a fresh
-- array (or not, when `keep`: the array is read again afterwards).
@[noinline] def proved (k i : Nat) (keep : Bool) : String := Id.run do
  let a := natArr k
  let b := intArr k
  let c := strArr k
  let d := qArr k
  let e := u64Arr k
  let f := bytes k
  let g := floats k
  let ra := if h : i < a.size then a[i] else 0
  let rb := if h : i < b.size then b[i] else 0
  let rc := if h : i < c.size then c[i] else ""
  let rd := if h : i < d.size then d[i] else ⟨"", 0⟩
  let re := if h : i < e.size then e[i] else 0
  let rf := if h : i < f.size then f[i] else 0
  let rg := if h : i < g.size then g[i] else 0
  let again := if keep then s!" again {a.size + b.size + c.size + d.size + e.size + f.size + g.size} {a[0]!} {c[0]!} {d[0]!.s}" else ""
  return s!"{ra} {rb} {rc} {rd.s} {rd.n} {re} {rf} {rg}{again}"

-- `get!` in bounds, each the last use of a fresh array.
@[noinline] def bang (k i : Nat) : String :=
  s!"{(natArr k)[i]!} {(intArr k)[i]!} {(strArr k)[i]!} {(qArr k)[i]!.n} {(u64Arr k)[i]!} {(bytes k).get! i} {(floats k).get! i}"

-- Folds read through `uget`.
@[noinline] def folds (k : Nat) : String :=
  let a := natArr k
  let c := strArr k
  let e := u64Arr k
  s!"{a.foldl (· + ·) 0} {(intArr k).foldl (· + ·) 0} {c.foldl (· ++ ·) ""} {(qArr k).foldl (fun n q => n + q.n) 0} {e.foldl (· + ·) 0} {(bytes k).foldl (fun n b => n + b.toNat) 0} {a.size + c.size + e.size}"

-- A loop over an array that stays shared (the caller keeps it).
@[noinline] def sumLoop (a : Array Nat) (i acc : Nat) : Nat :=
  if h : i < a.size then sumLoop a (i + 1) (acc + a[i]) else acc

@[noinline] def strReads (k : Nat) (p : Nat) : String :=
  let s := str k
  let t := str k
  s!"{(str k).foldl (fun n c => n + c.toNat) 0} {String.Pos.Raw.get s ⟨p⟩} {String.Pos.Raw.get t ⟨2^64⟩} {(String.Pos.Raw.next (str k) ⟨p⟩).byteIdx} {String.Pos.Raw.atEnd (str k) ⟨2^64⟩}"

def main (args : List String) : IO Unit := do
  let k := args.length + 3
  for i in [0:4] do
    IO.println s!"proved {i}: {proved k i false}"
    IO.println s!"proved {i} keep: {proved k i true}"
  IO.println s!"bang 1: {bang k 1}"
  IO.println s!"folds: {folds k}"
  let a := (natArr k).push (2^66)
  IO.println s!"loop: {sumLoop a 0 0} {sumLoop a 1 0} {a.size}"
  IO.println s!"strings: {strReads k 1} {strReads k 3}"
  -- out of bounds: Array panics and answers the default, ByteArray and
  -- FloatArray answer 0 without a message; a small and a big index
  IO.println s!"oob nat: {(natArr k)[7]!}"
  IO.println s!"oob nat big: {(natArr k)[2^64 + k]!}"
  IO.println s!"oob str: {(strArr k)[5]!}"
  IO.println s!"oob int big: {(intArr k)[2^70]!}"
  IO.println s!"oob bytes: {(bytes k).get! 9} {(bytes k).get! (2^64)} {(floats k).get! 9} {(floats k).get! (2^65)}"
  let kept := strArr k
  IO.println s!"oob kept: {kept[2^64]!} {kept[1]!}"
