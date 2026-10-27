/-! Runtime test: optimization `flatten-structs` and a two-constructor value
built behind a join on its tag (`materialize`; a call's result that the
pass splits, stored whole), then matched, with a second `match` on the same
value inside an alternative (Lean leaves it under the `if`): the
alternative knows the value's constructor (`xformCases`' `built`), so the
inner `match` takes its arm without a second match at run time (hunt of
the pass: before, the alternative learnt nothing, as the object's variable
has no type in the pass's facts). An inner `match` in a default
alternative stays a match.
- `storeE`: an `Except String (Nat × Nat)`;
- `storeS`: constructors with the same field types (`Ctors.shared`);
- `meet`: after the inner match, the value meets another call's result at
  a join point whose parameter the pass splits, so what the alternative
  knows of it goes into that parameter's fields.
tests/runtime/flatten-match-check.sh counts the arms of the matches on
these types in the loops' code. Argument: n. -/
@[noinline] def mkE (i : Nat) : Except String (Nat × Nat) :=
  if i % 7 == 6 then .error (toString i) else .ok (i, i + 1)

-- reads mkE's result and its payload field by field
@[noinline] def readE (i : Nat) : Nat :=
  match mkE i with
  | .ok p => p.1 + p.2
  | .error _ => 0

@[noinline] def storeE (n : Nat) : Array (Except String (Nat × Nat)) × Nat := Id.run do
  let mut a := Array.mkEmpty n
  let mut s := 0
  for i in [0:n] do
    let r := mkE i
    a := a.push r
    match r with
    | .ok p =>
      s := s + p.1
      if p.2 % 2 == 0 then
        match r with
        | .ok q => s := s + q.2
        | .error _ => s := s + 1000
    | _ =>
      match r with
      | .error e => s := s + e.length
      | .ok _ => s := s + 7
  return (a, s)

-- constructors with the same field types
inductive S where
  | l (n : Nat) (s : String)
  | r (n : Nat) (s : String)

instance : ToString S := ⟨fun | .l n s => s!"l({n},{s})" | .r n s => s!"r({n},{s})"⟩

@[noinline] def mkS (i : Nat) : S :=
  if i % 2 == 0 then .l i s!"L{i}" else .r (i * 10) s!"R{i}"

@[noinline] def storeS (n : Nat) : Array S × Nat := Id.run do
  let mut a := Array.mkEmpty n
  let mut s := 0
  for i in [0:n] do
    let v := mkS i
    a := a.push v
    match v with
    | .l k t =>
      if k % 4 == 0 then
        match v with
        | .l k2 t2 => s := s + k2 + t2.length + t.length
        | .r .. => s := s + 1000
      else s := s + 1
    | _ =>
      match v with
      | .r k2 t2 => s := s + k2 + t2.length
      | .l .. => s := s + 2000
  return (a, s)

inductive R where
  | a (x : Nat) (s : String)
  | b (f : Float) (u : UInt8) (arr : Array Nat)

instance : ToString R := ⟨fun | .a x s => s!"a({x},{s})" | .b f u arr => s!"b({f},{u},{arr})"⟩

@[noinline] def mkR (i : Nat) : R :=
  if i % 3 == 0 then .a i s!"a{i}" else .b i.toFloat i.toUInt8 #[i, i + 1]

@[noinline] def meet (n : Nat) : Array R × Nat × String := Id.run do
  let mut a := Array.mkEmpty n
  let mut s := 0
  let mut log := ""
  for i in [0:n] do
    let r := mkR i
    a := a.push r
    match r with
    | .a x t =>
      if x % 2 == 0 then
        match r with
        | .a y u => s := s + y + u.length
        | .b .. => s := s + 1000
      let c := if x % 4 == 0 then r else mkR (i + 2)
      match c with
      | .a z w => s := s + z; log := log ++ w ++ t
      | .b f u arr => s := s + u.toNat + arr.size + f.toUInt64.toNat
    | .b f u arr =>
      if u % 2 == 0 then
        match r with
        | .b g v brr => s := s + v.toNat + brr.size + (g + f).toUInt64.toNat + arr.size
        | _ => s := s + 7
      let c := if u % 4 == 0 then mkR (i + 1) else r
      match c with
      | .a z w => s := s + z * 100; log := log ++ w
      | .b g v _ => s := s + v.toNat * 2 + g.toUInt64.toNat
  return (a, s, log)

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 20
  let (a, s) := storeE n
  let errs := a.foldl (fun k r => match r with | .error _ => k + 1 | .ok _ => k) 0
  IO.println s!"{a.size} {errs} {s} {readE 3} {readE 6}"
  let (b, t) := storeS n
  IO.println s!"{b.size} {t} {b.toList.take 5}"
  let (c, u, log) := meet n
  IO.println s!"{c.size} {u} {log.length} {log.take 40}"
  IO.println s!"{c.toList.take 5}"
