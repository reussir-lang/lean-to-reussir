/-! Runtime test: `Array`, `ByteArray`, `Subarray`: bounds checks (`get!`/`set!` panics), push/pop/swap, in-place
updates of unique arrays, sorting, folds. -/

structure P where
  x : Nat
  name : String
deriving Repr, BEq, Hashable

def mkArr (n : Nat) : Array Nat := Id.run do
  let mut a := #[]
  for i in [0:n] do
    a := a.push ((i * 7919) % 101)
  return a

def main (args : List String) : IO Unit := do
  let n := args.length + 20
  let a := mkArr n
  IO.println s!"a {a} size {a.size} usize {a.usize}"
  IO.println s!"get! {a[3]!} {a[n-1]!} oob {a[n]!} {a[1000000]!} get? {a[2]?} {a[n]?} getD {a.getD 100 42}"
  IO.println s!"set! {a.set! 0 999 |>.toList.take 3} oob {(a.set! n 5).size} setD {(a.setIfInBounds 100 1).size}"
  IO.println s!"pop {a.pop.size} {(#[] : Array Nat).pop.size} back {a.back!} {(#[] : Array Nat).back!} back? {a.back?}"
  IO.println s!"swap {(a.swapIfInBounds 0 1).toList.take 3} {(a.swapIfInBounds 0 100).toList.take 3}"
  IO.println s!"qsort {a.qsort (· < ·)} insertionSort {(a.extract 0 8).insertionSort (· < ·)}"
  IO.println s!"map {a.map (· * 2) |>.toList.take 5} filter {a.filter (· % 2 == 0)} reverse {a.reverse.toList.take 4}"
  IO.println s!"foldl {a.foldl (· + ·) 0} foldr {a.foldr (· + ·) 0} any {a.any (· > 99)} all {a.all (· < 101)} contains {a.contains 58}"
  IO.println s!"append {(a ++ a).size} extract {a.extract 3 7} {a.extract 10 5} {a.extract 5 1000 |>.size} replicate {Array.replicate 4 'x'}"
  IO.println s!"range {Array.range 10} zip {(Array.range 3).zip #["a", "b", "c"]} find? {a.find? (· > 90)} findIdx? {a.findIdx? (· > 90)}"
  IO.println s!"sum {(Array.range 100000).foldl (· + ·) 0} mapIdx {(Array.range 5).mapIdx (fun i x => i * x)}"
  IO.println s!"toList {a.toList.length} ofList {#[1, 2, 3].toList} {List.toArray [4, 5, 6]} isEmpty {a.isEmpty} {(#[] : Array Nat).isEmpty}"
  IO.println s!"subarray {a[2:5]} {a[2:5].toArray} {a[:3].foldl (· + ·) 0} {a[n-2:].size}"
  -- ByteArray
  let ba := ByteArray.mk #[1, 2, 3, 255]
  IO.println s!"bytes {ba} size {ba.size} get! {ba.get! 1} oob {ba.get! 10} set! {(ba.set! 0 9).toList} oob {(ba.set! 10 9).toList}"
  IO.println s!"bytes push {(ba.push 7).toList} append {(ba ++ ba).toList} extract {(ba.extract 1 3).toList} hash {hash ba} eq {ba == ba}"
  IO.println s!"copySlice {(ba.copySlice 1 (ByteArray.mk #[0, 0, 0, 0, 0]) 2 2).toList} {(ba.copySlice 0 ByteArray.empty 0 10).toList} {(ba.copySlice 5 ba 0 1).toList}"
  IO.println s!"utf8 {"héllo".toUTF8} {String.fromUTF8? (ByteArray.mk #[104, 195, 169])} {String.fromUTF8? (ByteArray.mk #[255])} {(String.fromUTF8! "abc".toUTF8)}"
