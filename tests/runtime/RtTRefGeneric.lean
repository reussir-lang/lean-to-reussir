/-! Runtime test (typed references, clean step B2: the fallback). The same
element types as typed code uses also reach code of unknown type: an
existential package (`Pkg`: a type, a reference of it, a printer) reads
and updates references made by typed code at `Nat`, `String`, a structure,
`Array Nat` and `List Nat` through operations at `lcAny`; and `viaUniform`
makes a reference where its element type is unknown (`IO.mkRef m.v`, an
operation at `lcAny` too) and typed code reads it back at `Nat`. An
operation at `lcAny` can meet every reference, so every cell kind is off
(`RtTRefGeneric.l2r-debug`) and every reference holds boxes, as without
the optimization; typed code still updates the arrays and strings that
only a cell holds in place (`RtTRefGeneric.alloc`: n = 2000 and 8000
`modify` steps of typed code on a reference that the package also reads).
Arguments: a kind (`arr`, `str`) or nothing (every check), and n. -/

structure Pt where
  n : Nat
  s : String
  deriving Inhabited

instance : ToString Pt := ⟨fun p => s!"<{p.n},{p.s}>"⟩

/-- An existential package: its reference is read at `lcAny`. -/
structure Pkg where
  α : Type
  r : IO.Ref α
  show' : α → String
  step : α → α

@[noinline] def touch (p : Pkg) : IO String := do
  p.r.modify p.step
  let v ← p.r.get
  let old ← p.r.swap v
  p.r.set (p.step old)
  return p.show' (← p.r.get)

/-- A reference made where its element type is unknown. -/
structure Mk where
  α : Type
  v : α
  show' : α → String

@[noinline] def viaUniform (m : Mk) : IO (IO.Ref m.α) := do
  let r ← IO.mkRef m.v
  r.set (← r.get)
  return r

def check : IO Unit := do
  let rn ← IO.mkRef (5 : Nat)
  let rs ← IO.mkRef "s"
  let rp ← IO.mkRef ({ n := 1, s := "p" } : Pt)
  let ra ← IO.mkRef (#[1, 2] : Array Nat)
  let rl ← IO.mkRef ([3] : List Nat)
  let pkgs : List Pkg := [⟨Nat, rn, toString, (· + 2 ^ 64)⟩, ⟨String, rs, id, (· ++ "!")⟩,
    ⟨Pt, rp, toString, fun p => { p with n := p.n + 1 }⟩, ⟨Array Nat, ra, toString, (·.push 9)⟩,
    ⟨List Nat, rl, toString, (0 :: ·)⟩]
  for p in pkgs do IO.println s!"pkg {← touch p}"
  -- Typed code on the same references.
  rn.modify (· * 2)
  rs.modify (· ++ "?")
  rp.modify fun p => { p with s := p.s ++ "q" }
  ra.modify (·.push 7)
  rl.modify (1 :: ·)
  IO.println s!"typed {← rn.get} {← rs.get} {← rp.get} {← ra.get} {← rl.get} {← rn.ptrEq rn}"
  for p in pkgs do IO.println s!"pkg {← touch p}"
  -- Made at an unknown type, read by typed code.
  let r ← viaUniform ⟨Nat, 41, toString⟩
  let r : IO.Ref Nat := r
  r.modify (· + 1)
  IO.println s!"uniform {← r.get}"

def steps (kind : String) (n : Nat) : IO String := do
  match kind with
  | "arr" =>
    let r ← IO.mkRef (#[] : Array Nat)
    let p : Pkg := ⟨Array Nat, r, fun a => toString a.size, id⟩
    for i in [0:n] do
      r.modify (·.push i)
      if i % 500 == 0 then discard <| touch p
    return s!"arr {(← r.get).size} {← touch p}"
  | "str" =>
    let r ← IO.mkRef ""
    let p : Pkg := ⟨String, r, fun s => toString s.length, id⟩
    for i in [0:n] do
      r.modify (·.push (Char.ofNat (97 + i % 26)))
      if i % 500 == 0 then discard <| touch p
    return s!"str {(← r.get).length} {← touch p}"
  | _ => return s!"unknown kind {kind}"

def main (args : List String) : IO Unit := do
  match args with
  | [kind, n] => IO.println (← steps kind (n.toNat?.getD 0))
  | _ =>
    check
    IO.println (← steps "arr" 1000)
    IO.println (← steps "str" 1000)
