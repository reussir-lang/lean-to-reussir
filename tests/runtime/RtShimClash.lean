/-!
A program that declares a name which a module of `Std` it does not import
declares too: natively no clash. lean2rr's shim (`L2RShim`) imports
`Std.Internal.UV`, which imports `Std.Data.ByteSlice` and its root-namespace
`ByteSlice`; imported with this program, the two `ByteSlice`s clashed and
lean2rr stopped ("environment already contains 'ByteSlice.start'").
lean2rr now loads the shim's part over `Init` only (`L2RShim.Core`) in that
case, which still replaces `IO.Promise.isResolved`.
-/

structure ByteSlice where
  bytes : ByteArray
  start : Nat
  stop : Nat

def ByteSlice.size (s : ByteSlice) : Nat := s.stop - s.start

def ByteSlice.toList (s : ByteSlice) : List UInt8 :=
  (List.range s.size).map fun i => s.bytes.get! (s.start + i)

def main : IO Unit := do
  let s : ByteSlice := ⟨⟨#[1, 2, 3, 4]⟩, 1, 3⟩
  IO.println s.size
  IO.println s.toList
  let p ← IO.Promise.new (α := Nat)
  IO.println (← p.isResolved)
  p.resolve 5
  IO.println (← p.isResolved)
