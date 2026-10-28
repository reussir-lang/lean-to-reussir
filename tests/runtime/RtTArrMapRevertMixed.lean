/-! Runtime test (typed arrays; review of the map loops' revert,
2026-10-27, HsRevert1; Performance): monadic `mapM`s between pointer kinds
that end up off (`LStr`, `Nat` and their arrays: the existential `Pk`
meets them), with a captured structure spread by `flatten-structs` and an
early exit (`Except`), a nested map (`IO`), and a `StateT (Array UInt8) IO`
map. The last one's loop returns its array of boxes together with the
compact state `Array UInt8` (one value, one flow class for the check), so
entered in place it would turn `u8` off: `revertPtrSplits` keeps that
entry's split (`arrayElemsIn`), and the other entries go back in place.
`.l2r-debug`: 5 entries in place again, `u8` stays on. On d9fb69ed the
`StateT` entry made the check after the revert turn `u8` off, so every
entry kept its split (8); on dev 0a1e4391 only those of a pure `map`
went back (2). Outputs identical to native. -/
structure Cfg where
  add : Nat
  tag : String

structure Pk where
  τ : Type
  v : Array τ
@[noinline] def pkSize (p : Pk) : Nat := p.v.size

-- captured structure (spread by flatten-structs), Except with an early exit
@[noinline] def lensE (c : Cfg) (a : Array String) : Except String (Array Nat) :=
  a.mapM fun s => if s == "stop" then .error s!"{c.tag} stop" else .ok (s.length + c.add)

-- StateT over IO with a compact state
@[noinline] def strsS (a : Array Nat) : StateT (Array UInt8) IO (Array String) :=
  a.mapM fun n => do
    modify (·.push n.toUInt8)
    if n == 1000000 then IO.println "big"
    pure s!"<{n}>"

-- nested: rows of strings to rows of lengths, in IO
@[noinline] def rowsIO (rs : Array (Array String)) : IO (Array (Array Nat)) :=
  rs.mapM fun r => do
    if r.size == 1000000 then IO.println "huge"
    pure (r.map String.length)

def main : IO Unit := do
  let src : Array String := #["a", "bb", "ccc"]
  match lensE ⟨10, "T"⟩ src with
  | .ok r => IO.println s!"lensE {r} {src}"
  | .error e => IO.println s!"lensE err {e}"
  match lensE ⟨1, "U"⟩ #["x", "stop", "y"] with
  | .ok r => IO.println s!"lensE {r}"
  | .error e => IO.println s!"lensE err {e}"
  let ns : Array Nat := #[3, 1, 4]
  let (out, st) ← (strsS ns).run #[7]
  IO.println s!"strsS {out} {st} {ns}"
  let rows : Array (Array String) := #[#["p", "qq"], #[], #["rrr"]]
  let lr ← rowsIO rows
  IO.println s!"rowsIO {lr} {rows}"
  IO.println s!"{pkSize ⟨String, src⟩} {pkSize ⟨Nat, ns⟩} {pkSize ⟨Array String, rows⟩} {pkSize ⟨Array Nat, lr⟩} {pkSize ⟨String, out⟩}"
