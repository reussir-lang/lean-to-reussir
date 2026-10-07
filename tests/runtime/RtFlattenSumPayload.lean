/-! Runtime test: optimization `flatten-structs` and a two-constructor value
used whole, then matched, its payload used whole in the alternative
(review of the pass, round 5, G1). The value is built behind a join on
its tag (`materialize`), so the payload built there is not in scope
afterwards; a `cases` on such a value matches the built object, whose
fields are the ones built (`xform`): the payload is built once, as native
(`same=true`). `storeE`: a call's result (`mkE`, split because `readE`
reads it field by field); `storeO`: a join point's parameter. -/
@[noinline] def mkE (i : Nat) : Except String (Nat × Nat) :=
  if i % 7 == 6 then .error (toString i) else .ok (i, i + 1)

-- reads mkE's result and its payload field by field
@[noinline] def readE (i : Nat) : Nat :=
  match mkE i with
  | .ok p => p.1 + p.2
  | .error _ => 0

@[noinline] def storeE (n : Nat) : Array (Except String (Nat × Nat)) × Array (Nat × Nat) := Id.run do
  let mut a := Array.mkEmpty n
  let mut b := Array.mkEmpty n
  for i in [0:n] do
    let r := mkE i
    a := a.push r
    match r with
    | .ok p => b := b.push p
    | .error _ => pure ()
  return (a, b)

@[noinline] def storeO (n : Nat) : Array (Option (Nat × Nat)) × Array (Nat × Nat) := Id.run do
  let mut a := Array.mkEmpty n
  let mut b := Array.mkEmpty n
  for i in [0:n] do
    let o := if i % 3 == 2 then none else some (i, i + 1)
    a := a.push o
    if a.size % 5 == 1 then a := a.push o
    if a.size % 7 == 3 then a := a.push o
    match o with
    | some p => b := b.push p
    | none => pure ()
  return (a, b)

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [mode, k] =>
    let n := k.toNat!
    if mode == "e" then
      let (a, b) := storeE n
      IO.println s!"{a.size} {b.size} {readE 3}"
    else
      let (a, b) := storeO n
      IO.println s!"{a.size} {b.size}"
  | _ =>
    let (a, b) := storeE 3
    let s := match a[0]! with | .ok p => ptrAddrUnsafe p == ptrAddrUnsafe b[0]! | .error _ => false
    IO.println s!"storeE {b} {readE 2} same={s}"
    let (a, b) := storeO 3
    let s := match a[0]! with | some p => ptrAddrUnsafe p == ptrAddrUnsafe b[0]! | none => false
    IO.println s!"storeO {b} same={s}"
