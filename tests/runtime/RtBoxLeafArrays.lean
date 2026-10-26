/-! Runtime test: typed arrays in boxes (the heads of lists), freed whole
by user code, by a reference's `set` (a free the runtime starts) and as the
element of an array that `set!` replaces. A typed array of leaf elements
(`Array Nat`, `Array Int`, `Array String`, `Array (Array UInt8)`) is a
leaf payload of the box (lean2rr's `boxLeafArrayElem`): released directly,
also inside a free, where it waited as a pending cell before. An
`Array Pt` of records is not. tests/runtime/box-leaf-check.sh checks the
payload numbers in the translation; this test checks the results.
Argument: N (default 1000). -/

structure Pt where
  x : Nat
  y : Nat

@[noinline] def mk (n : Nat) : List (Array Nat) × List (Array Int) × List (Array String) × List (Array (Array UInt8)) × List (Array Pt) :=
  let ns := (List.range n).map fun i => #[i, i + 1]
  let is := (List.range n).map fun (i : Nat) => #[Int.ofNat i - 500, -1]
  let ss := (List.range n).map fun i => #[toString i]
  let bs := (List.range n).map fun i => #[#[(i % 256).toUInt8], #[]]
  let ps := (List.range n).map fun i => #[{ x := i, y := i * 2 : Pt }]
  (ns, is, ss, bs, ps)

def sums (t : List (Array Nat) × List (Array Int) × List (Array String) × List (Array (Array UInt8)) × List (Array Pt)) : String :=
  let (ns, is, ss, bs, ps) := t
  let a := ns.foldl (fun acc xs => acc + xs.foldl (· + ·) 0) 0
  let b := is.foldl (fun acc xs => acc + xs.foldl (· + ·) 0) 0
  let c := ss.foldl (fun acc xs => acc + xs.foldl (fun l s => l + s.length) 0) 0
  let d := bs.foldl (fun acc xs => acc + xs.foldl (fun l s => l + s.size) 0) 0
  let e := ps.foldl (fun acc xs => acc + xs.foldl (fun l p => l + p.x + p.y) 0) 0
  s!"{a} {b} {c} {d} {e}"

def main (args : List String) : IO Unit := do
  let n := (args.headD "1000").toNat!
  -- Dropped whole by user code.
  IO.println (sums (mk n))
  -- Freed by a reference's `set` (a free the runtime starts).
  let r ← IO.mkRef (mk n)
  IO.println (sums (← r.get))
  r.set ([], [], [], [], [])
  IO.println (sums (← r.get))
  -- The element of an array that `set!` replaces.
  let arr := #[mk n]
  IO.println (sums arr[0]!)
  let arr := arr.set! 0 ([], [], [], [], [])
  IO.println (sums arr[0]!)
