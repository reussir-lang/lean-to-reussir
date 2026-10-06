/-! Runtime test: `Int` values at the edges of the small range (`int32`,
Lean's `LEAN_MIN_SMALL_INT..LEAN_MAX_SMALL_INT`), computed at run time:
`Int.add`, `sub`, `mul`, the divisions and remainders, `neg` and the
conversions from `Nat`, `Int8`..`Int64`, `ISize`, `UInt32`, `UInt64`,
`String` and `Float` landing exactly on the range's edges and just outside,
and big values that come back into the range. Then the equality and the
order of every pair, small against big among them.

lean2rr answers `a = b` for a small and a big word without a call (a big
`Int` is never in the small range: every result is normalized, the audit of
runtime switch step 10): a result that came back into the range but stayed
big would compare unequal to the same small value here. -/

/-- A structure with `Int` fields: its derived `DecidableEq` compares them
with `Int.decEq`. -/
structure Pt where
  x : Int
  n : Nat
  y : Int
deriving DecidableEq

def printVals (xs : Array (String × Int)) : IO Unit := do
  for (n, v) in xs do
    IO.println s!"{n} = {v}"

def main (args : List String) : IO Unit := do
  -- `z` is 0, but not a constant the compiler could fold.
  let z : Int := args.length
  let zn : Nat := args.length
  let hi : Int := z + 2147483647
  let lo : Int := z - 2147483648
  let two31 : Int := z + 2147483648
  let two32 : Int := z + 4294967296
  let vals : Array (String × Int) := #[
    ("hi", hi), ("lo", lo), ("hi - 1", hi - 1), ("lo + 1", lo + 1),
    ("hi + 1", hi + 1), ("lo - 1", lo - 1),
    ("(hi + 1) + -1", (hi + 1) + (z - 1)), ("(lo - 1) + 1", (lo - 1) + (z + 1)),
    ("(hi + 1) - 1", (hi + 1) - (z + 1)), ("(lo - 1) - -1", (lo - 1) - (z - 1)),
    ("2^40 - (2^40 - 5)", (z + 2^40) - (z + 2^40 - 5)), ("(lo - 1) - (lo - 1)", (lo - 1) - (lo - 1)),
    ("lo + -1", lo + (z - 1)), ("hi + hi", hi + hi), ("lo + lo", lo + lo), ("hi - lo", hi - lo), ("lo - hi", lo - hi),
    ("46340 * 46340", (z + 46340) * (z + 46340)), ("46341 * 46341", (z + 46341) * (z + 46341)),
    ("-46341 * 46341", (z - 46341) * (z + 46341)), ("2^16 * 2^15", (z + 65536) * (z + 32768)),
    ("-2^16 * 2^15", (z - 65536) * (z + 32768)), ("lo * -1", lo * (z - 1)), ("lo * 1", lo * (z + 1)),
    ("2^32 * 0", two32 * z), ("2^32 * -1", two32 * (z - 1)), ("(hi + 1) * -1", (hi + 1) * (z - 1)),
    ("lo * lo", lo * lo), ("(2^40) * (2^40)", (z + 2^40) * (z + 2^40)),
    ("lo / -1", lo / (z - 1)), ("lo.tdiv -1", lo.tdiv (z - 1)), ("lo.fdiv -1", lo.fdiv (z - 1)),
    ("2^31 / 2", two31 / (z + 2)), ("2^32 / 2", two32 / (z + 2)), ("2^32 / -2", two32 / (z - 2)),
    ("2^32.tdiv -2", two32.tdiv (z - 2)), ("(2^32 + 1).fdiv -2", (two32 + 1).fdiv (z - 2)),
    ("-(2^32 + 1) / 2", (-(two32 + 1)) / (z + 2)), ("(-(2^32) - 1).tdiv 2", (-two32 - 1).tdiv (z + 2)),
    ("2^33 / 4", (two32 * 2) / (z + 4)), ("x / 0", (two32 + 7) / z), ("x % 0", (two32 + 7) % z),
    ("lo % -1", lo % (z - 1)), ("lo.tmod -1", lo.tmod (z - 1)), ("lo.fmod -1", lo.fmod (z - 1)),
    ("(2^40 + 3) % 2^40", (z + 2^40 + 3) % (z + 2^40)), ("(-(2^40) - 3) % 2^40", (z - 2^40 - 3) % (z + 2^40)),
    ("(-(2^40) - 3).tmod 2^40", (z - 2^40 - 3).tmod (z + 2^40)), ("(2^40 + 3).fmod -(2^40)", (z + 2^40 + 3).fmod (z - 2^40)),
    ("(2^32 + 5) % 10", (two32 + 5) % (z + 10)), ("lo % 2^32", lo % two32), ("(lo - 1) % 2^31", (lo - 1) % two31),
    ("-lo", -lo), ("-(hi + 1)", -(hi + 1)), ("-(lo - 1)", -(lo - 1)), ("-hi", -hi), ("-(-(hi + 1))", -(-(hi + 1))),
    ("ofNat (2^31 - 1)", Int.ofNat (zn + 2147483647)), ("ofNat 2^31", Int.ofNat (zn + 2147483648)),
    ("ofNat (2^63 - 1)", Int.ofNat (zn + 2^63 - 1)), ("ofNat 2^63", Int.ofNat (zn + 2^63)),
    ("negSucc (2^31 - 1)", Int.negSucc (zn + 2147483647)), ("negSucc 2^31", Int.negSucc (zn + 2147483648)),
    ("negSucc 2^63", Int.negSucc (zn + 2^63)),
    ("Int8 min", (Int8.ofInt (z - 128)).toInt), ("Int16 max", (Int16.ofInt (z + 32767)).toInt),
    ("Int32 min", (Int32.ofInt lo).toInt), ("Int32 max", (Int32.ofInt hi).toInt),
    ("Int64 hi + 1", (Int64.ofInt (hi + 1)).toInt), ("Int64 lo - 1", (Int64.ofInt (lo - 1)).toInt),
    ("Int64 lo", (Int64.ofInt lo).toInt), ("Int64 min", (Int64.ofInt (z - 2^63)).toInt),
    ("ISize hi", (ISize.ofInt hi).toInt), ("ISize hi + 1", (ISize.ofInt (hi + 1)).toInt),
    ("UInt32 2^31", Int.ofNat (UInt32.ofNat (zn + 2147483648)).toNat),
    ("UInt64 2^31 - 1", Int.ofNat (UInt64.ofNat (zn + 2147483647)).toNat),
    ("UInt64 max", Int.ofNat (UInt64.ofNat (zn + 2^64 - 1)).toNat),
    ("\"2147483647\".toInt!", (toString (zn + 2147483647)).toInt!),
    ("\"2147483648\".toInt!", (toString (zn + 2147483648)).toInt!),
    ("\"-2147483648\".toInt!", ("-" ++ toString (zn + 2147483648)).toInt!),
    ("\"-2147483649\".toInt!", ("-" ++ toString (zn + 2147483649)).toInt!),
    ("frExp 2^31 exponent", (Float.frExp (Float.ofInt two31)).2),
    ("Float.ofInt (hi + 1) round trip", Int.ofNat (Float.ofInt (hi + 1)).toUInt64.toNat),
    ("natAbs lo", Int.ofNat lo.natAbs), ("toNat (hi + 1)", Int.ofNat (hi + 1).toNat),
    ("Array Int round trip", ((#[lo - 1, hi + 1, (hi + 1) - (z + 1)] : Array Int).map (· + z))[2]!)]
  printVals vals
  -- Equality and order of every pair: '=' and '#' for `==` true and false,
  -- then the `compare` of the pair ('<', '=', '>'), then `<` and `≤`.
  for (n, a) in vals do
    let mut eqs := ""
    let mut ords := ""
    let mut lts := ""
    for (_, b) in vals do
      eqs := eqs.push (if a == b then '=' else '#')
      ords := ords.push (match compare a b with | .lt => '<' | .eq => '=' | .gt => '>')
      lts := lts.push (if a < b then 'l' else if a ≤ b then 'e' else 'g')
    IO.println s!"{n}: {eqs} {ords} {lts}"
  -- `decide`, `!=`, `max`/`min`, pairs, and `Int.decEq` through a
  -- structure's derived equality (`Pt`).
  let back := (hi + 1) + (z - 1)
  IO.println s!"decide {decide (back = hi)} {decide (back = hi + 1)} ne {back != hi} {(lo - 1) != lo}"
  IO.println s!"max {max back (hi + 1)} min {min ((lo - 1) + (z + 1)) lo}"
  let pairs : Array (Int × Int) := #[(back, hi), ((lo - 1) - (z - 1), lo), (hi + 1, hi), (-(hi + 1), lo)]
  IO.println s!"pairs {pairs.map fun (x, y) => x == y}"
  let pts : Array (Pt × Pt) := #[
    (⟨back, zn, lo - 1⟩, ⟨hi, zn, lo - 1⟩), (⟨back, zn, (lo - 1) + (z + 1)⟩, ⟨hi, zn, lo⟩),
    (⟨hi + 1, zn, z⟩, ⟨hi, zn, z⟩), (⟨z, zn, -(hi + 1)⟩, ⟨z, zn, lo⟩), (⟨two32 / 2, zn, z⟩, ⟨two31, zn, z⟩),
    (⟨two32 / 2 - 1, zn, z⟩, ⟨hi, zn, z⟩), (⟨lo, zn + 1, z⟩, ⟨lo, zn, z⟩)]
  IO.println s!"structures {pts.map fun (p, q) => decide (p = q)}"
