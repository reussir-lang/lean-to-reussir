/-! Runtime test (typed references, clean step B2; review of the change):
references whose element type holds a reference, beside typed references.
Mono types a reference `lcAny`, so a reference of a reference (`outer`) and
of an array of references (`rr`) is made and used at `lcAny` or
`Array lcAny`; the check compares the instances' type arguments before mono
too, where they keep their own heads (`ST.Ref lcAny Nat`), so they meet no
reference of another element type and the other kinds stay typed: `Nat`,
`Pt`, `String`, `Array UInt8`, `StdGen` (`RtTRefNested.l2r-debug`). Before,
each of them turned every kind off. A reference of a cancel token (`rt`)
is there too: `IO.CancelToken` is a structure of two fields, so mono keeps
its head and it has its own cell kind, which its fields' observable
release turns off; it needs no comparison before mono. -/

structure Pt where
  n : Nat
  s : String
  deriving Inhabited

instance : ToString Pt := ⟨fun p => s!"<{p.n},{p.s}>"⟩

def main : IO Unit := do
  -- A reference of a reference.
  let inner ← IO.mkRef (5 : Nat)
  let outer ← IO.mkRef inner
  (← outer.get).modify (· + 1)
  let inner2 ← IO.mkRef (10 : Nat)
  outer.set inner2
  (← outer.get).modify (· * 2)
  IO.println s!"nested {← inner.get} {← inner2.get} {← (← outer.get).get} {← (← outer.get).ptrEq inner2}"
  -- A reference of an array of references.
  let refs ← (List.range 3).toArray.mapM fun i => IO.mkRef ({ n := i, s := "r" } : Pt)
  let rr ← IO.mkRef refs
  for r in (← rr.get) do r.modify fun p => { p with n := p.n + 10 }
  if let some r := refs[0]? then rr.modify (·.push r)
  let xs ← rr.get
  let vals ← xs.mapM (·.get)
  let same ← match xs[0]?, xs[3]? with
    | some a, some b => a.ptrEq b
    | _, _ => pure false
  IO.println s!"refs {vals} {xs.size} {same}"
  -- A reference of a cancel token.
  let tok ← IO.CancelToken.new
  let rt ← IO.mkRef tok
  (← rt.get).set
  IO.println s!"token {← tok.isSet}"
  -- Typed references beside them.
  let ru ← IO.mkRef (#[] : Array UInt8)
  for i in [0:5] do ru.modify (·.push i.toUInt8)
  let rs ← IO.mkRef "s"
  rs.modify (· ++ "t")
  let rp ← IO.mkRef ({ n := 1, s := "p" } : Pt)
  rp.modify fun p => { p with n := p.n * 7 }
  IO.println s!"typed {← ru.get} {← rs.get} {← rp.get}"
