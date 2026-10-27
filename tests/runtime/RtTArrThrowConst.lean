/-! Runtime test (typed arrays, clean step B1; arrays hunt): a `mapM` in
`ExceptT String IO` whose function throws. Lean caches the thrown value
`Except.error "…"` as a constant, typed at the loop over `Array lcAny`
(`Except String (Array lcAny)`), and the loop's copy that Stage 3 types
(`Array String`, `Array Pt`) reads the same constant. The value holds no
array, so a binder bound to the constant is no crossing, as one bound to
the constructor (hunt HCA-01; `CAM.noArrConsts`): `LStr` and `I:Pt` stay
typed (`RtTArrThrowConst.l2r-debug`). Before, the constant's type
`Array lcAny` turned `LStr` off (and, under `StateT (Array Pt)`, `I:Pt`
too, and the `map` loops went back in place). Each shape runs with an
input that throws and one that does not. Argument: n. -/

structure Pt where
  x : Nat
  name : String

instance : ToString Pt := ⟨fun p => s!"<{p.x},{p.name}>"⟩

@[noinline] def strs (xs : Array Nat) : IO Unit := do
  let act : ExceptT String IO (Array String) := xs.mapM fun x => do
    if x > 10 then throw "too many"
    pure (toString x)
  match ← act.run with
  | .ok r => IO.println s!"ok {r}"
  | .error e => IO.println s!"err {e}"

@[noinline] def pts (xs : Array Nat) : IO Unit := do
  let act : StateT (Array Pt) (ExceptT String IO) (Array String) := xs.mapM fun x => do
    modify (·.push { x, name := s!"n{x}" })
    let s ← get
    if s.size > 10 then throw "too long"
    pure (s.map (·.name) |>.foldl (· ++ ·) "")
  match ← (act.run #[]).run with
  | .ok (r, s) => IO.println s!"stateExcept {r} {s}"
  | .error e => IO.println s!"stateExcept err {e}"

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 4
  strs ((Array.range n).map (· + 1))
  strs ((Array.range (n + 10)).map (· + 1))
  pts (Array.range n)
  pts (Array.range (n + 10))
