/-! Runtime test (typed references, clean step B2): typed and boxed cell
kinds in one program. Typed: a structure (`I:Pt`), `Nat`, `String`, an
array of records (`A(I:Pt)`). Off, because their values can hold a value
whose release the program can observe: `List (Nat → Nat)` (closures; so
`List String` is off too, one kind `I:List`), the standard output stream
(`I:IO.FS.Stream`, a structure of closures), `Array (Nat → Nat)`
(`A(box)`). No cell kind at all: `Nat → Nat`, `Thunk Nat`, `UInt64`,
`Float`. `RtTRefMixed.l2r-debug` lists the decisions. -/

structure Pt where
  n : Nat
  s : String
  deriving Inhabited

instance : ToString Pt := ⟨fun p => s!"<{p.n},{p.s}>"⟩

def main : IO Unit := do
  let rp ← IO.mkRef ({ n := 1, s := "a" } : Pt)
  let rn ← IO.mkRef (3 : Nat)
  let rs ← IO.mkRef "s"
  let rap ← IO.mkRef (#[] : Array Pt)
  let rfl ← IO.mkRef ([(· + 1), (· * 2)] : List (Nat → Nat))
  let rsl ← IO.mkRef (["x"] : List String)
  let rout ← IO.mkRef (← IO.getStdout)
  let rfa ← IO.mkRef (#[(· + 10)] : Array (Nat → Nat))
  let rf ← IO.mkRef (fun (x : Nat) => x + 100)
  let rt ← IO.mkRef (Thunk.mk fun _ => (7 : Nat))
  let ru ← IO.mkRef (18446744073709551615 : UInt64)
  let rd ← IO.mkRef (2.5 : Float)
  for i in [0:4] do
    rp.modify fun p => { p with n := p.n + i, s := p.s ++ toString i }
    rn.modify (· * 3 + i)
    rs.modify (· ++ "!")
    rap.modify (·.push { n := i, s := "e" })
    rfl.modify ((· + i) :: ·)
    rsl.modify (toString i :: ·)
    rfa.modify (·.push (· * i))
    rf.modify fun f x => f (x + i)
    rt.modify fun t => Thunk.mk fun _ => t.get + i
    ru.modify (· + 1)
    rd.modify (· * 1.5)
  let fs ← rfl.get
  let fa ← rfa.get
  IO.println s!"{← rp.get} {← rn.get} {← rs.get} {(← rap.get).map toString} {fs.map (· 1)} {← rsl.get}"
  IO.println s!"{fa.map (· 2)} {(← rf.get) 1} {(← rt.get).get} {← ru.get} {← rd.get}"
  (← rout.get).putStrLn "through the stream in a reference"
  rout.set (← IO.getStderr)
  (← rout.get).putStrLn "through stderr in a reference"
  IO.println s!"{← rp.ptrEq rp} {← rsl.ptrEq rsl}"
