/-! Runtime test (typed arrays; review of the map loops' revert, 2026-10-27;
Performance): entering a split `map` loop in place again must not turn
another kind off. `conv`'s `mapM` in `Except` maps an
`Array (String × String)` to an `Array (String × Nat)`; Stage 3 splits its
loop. `Prod`'s kind goes off (the existential `Pk` meets the array), so the
split's entries could go back to Lean's loop over `Array lcAny`; but that
array's flow class takes in the requests' array (`Array Req`, kind
`I:Req`, on), as in Cedar (Z06t: `toRequest`'s `mapM`, three kinds), and
the check then turns `I:Req` off. So the program with the entries in
place is not kept and the splits stay (`.l2r-debug`: the entries kept
split; `I:Req` stays on). With `flatten-structs` on (as by default) the
entries are calls of the split's worker, which `revertPtrSplits` now
enters in place too (`RtTArrMapInPlaceIO`). On dev 0a1e4391 the split's
worker was not recognized and the splits stayed; with `flatten-structs`
off, the entries went back and `I:Req` went off. Argument: n. -/

structure Req where
  ctx : Array (String × Nat)
  tag : Nat
  deriving Inhabited

@[noinline] def conv (a : Array (String × String)) : Except String (Array (String × Nat)) :=
  a.mapM fun (k, v) => match v.toNat? with
    | some n => .ok (k, n)
    | none => .error s!"bad {v}"

structure Pk where
  τ : Type
  v : Array τ

@[noinline] def pkSize (p : Pk) : Nat := p.v.size

@[noinline] def mkReq (i : Nat) : Except String Req := do
  let c ← conv #[("a", toString i), ("b", toString (i + 1))]
  pure ⟨c, i⟩

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 10
  let mut rs : Array Req := #[]
  for i in [0:n] do
    match mkReq i with
    | .ok r => rs := rs.push r
    | .error e => IO.println e
  match conv #[("x", "1"), ("y", "z")] with
  | .ok c => IO.println s!"ok {c.size}"
  | .error e => IO.println e
  let s := rs.foldl (fun acc r => acc + r.tag + r.ctx.foldl (fun a p => a + p.2) 0) 0
  IO.println s!"{s} {rs.size} {pkSize ⟨String × Nat, rs[0]!.ctx⟩}"
