/-! Runtime test: optimization `flatten-structs` builds each value once
(review of the pass, round 4, F4 and F5):
- `both`: a call's result stored with its inner record (two nested levels
  used whole; `mkO`'s result is read field by field elsewhere): one record
  and one inner record per step, as native;
- `loopJ`: a peeled loop's state used whole at its exit both in a join
  point's body and as its argument: two rebuilds where native has none
  (the state stays whole there, `constrainDecl`'s sites);
- `exit2`: a peeled loop's state stored at its exit with its inner record
  (`Env.mats`: the inner record is built once, inside the state);
- `chain`: a pair built in two branches at a loop's exit, stored by the
  join point that receives it and passed on to a second join point, which
  stores what it receives (the pair or a new one): one pair, as native, not
  a second copy in the second join point (round 2; a join point's
  parameter is never rebuilt). -/
structure I where
  a : Nat
  b : Nat
  deriving Inhabited

structure O where
  i : I
  c : Nat
  deriving Inhabited

@[noinline] def mkO (n : Nat) : O := ⟨⟨n, n + 1⟩, n + 2⟩
-- reads mkO's result and its inner record field by field
@[noinline] def readO (n : Nat) : Nat := (mkO n).i.a + (mkO (n + 1)).c

-- stores the record and its inner record
@[noinline] def both (n : Nat) : Array (O × I) := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    let x := mkO i
    out := out.push (x, x.i)
  return out

-- peeled loop; at its exit the state goes to a join point (one jump gives
-- it s) whose body stores both q and s
@[noinline] def loopJ (s : I) : Nat → Array I → Array I
  | 0, acc =>
    let q := if acc.size % 2 == 0 then s else ⟨0, acc.size⟩
    (acc.push q).push s
  | n+1, acc => loopJ ⟨s.a + 1, s.b⟩ n acc

@[noinline] def readJ (n : Nat) : Nat := (loopJ ⟨n, n⟩ n #[]).size

-- peeled loop; at its exit the state and its inner record are stored
@[noinline] def loopE (s : O) : Nat → Array (O × I) → Array (O × I)
  | 0, acc => acc.push (s, s.i)
  | n+1, acc => loopE ⟨⟨s.i.a + 1, s.i.b⟩, s.c + n⟩ n acc

@[noinline] def readE (n : Nat) : Nat := (loopE ⟨⟨n, n⟩, n⟩ n #[]).size

@[noinline] def keep (acc : Array (Nat × Nat)) (p : Nat × Nat) : Array (Nat × Nat) := acc.push p

@[noinline] def chainJ (s : Nat × Nat) : Nat → Array (Nat × Nat) → Array (Nat × Nat)
  | 0, acc =>
    let p := if s.1 % 2 == 0 then (s.1 + 1, s.2) else (s.2, s.1 + 2)
    let acc := keep acc p
    let q := if acc.size % 3 == 0 then (p.2, p.1) else p
    let acc := keep acc q
    let acc := keep acc (q.2, acc.size)
    if acc.size % 2 == 0 then keep acc (acc.size, q.1) else acc
  | n+1, acc => chainJ (s.1 + 1, s.2 + n) n acc

@[noinline] def readChain (n : Nat) : Nat := (chainJ (n, n) n #[]).size

@[noinline] def consume (p : Nat × Nat) : Nat := p.1 * 3 + p.2

@[noinline] def chain2 (s : Nat × Nat) (k : Nat) : Nat × Nat :=
  match k with
  | 0 =>
    let p := if s.1 % 2 == 0 then (s.1 + 1, s.2) else (s.2, s.1 + 2)
    let c := consume p
    let q := if c % 3 == 7 then (p.2, p.1) else p
    let d := consume q
    let e := consume (q.2, d)
    if e % 2 == 0 then q else (e % 100, d % 100)
  | k + 1 => chain2 (s.1 + 1, s.2 + k) k

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [mode, k] =>
    let n := k.toNat!
    if mode == "both" then
      let out := both n
      IO.println s!"{out.size} {readO 3}"
    else if mode == "exit2" then
      let mut t := 0
      for i in [0:n] do
        t := t + ((loopE ⟨⟨i, 1⟩, 2⟩ 1 #[])[0]!.1.c)
      IO.println s!"{t} {readE 2}"
    else if mode == "chain" then
      let mut t := 0
      for i in [0:n] do
        t := t + (chainJ (2 * i, 1) (i % 2) #[]).size + (chain2 (2 * i, 1) 1).1
      IO.println s!"{t} {readChain 2}"
    else
      let mut t := 0
      for _ in [0:n] do
        t := t + (loopJ ⟨n, 1⟩ 1 #[]).size
      IO.println s!"{t} {readJ 2}"
  | _ =>
    let out := both 2
    IO.println s!"both {out[1]!.1.c} {readO 1} same={ptrAddrUnsafe out[0]!.1.i == ptrAddrUnsafe out[0]!.2}"
    let j := loopJ ⟨5, 6⟩ 1 #[]
    IO.println s!"loopJ {j[0]!.a} {readJ 1} same={ptrAddrUnsafe j[0]! == ptrAddrUnsafe j[1]!}"
    let e := (loopE ⟨⟨5, 6⟩, 7⟩ 1 #[])[0]!
    IO.println s!"exit2 {e.1.c} {e.2.a} {readE 1} same={ptrAddrUnsafe e.1.i == ptrAddrUnsafe e.2}"
    IO.println s!"chain2 {chain2 (2, 3) 0} {chain2 (3, 3) 2} {chain2 (4, 9) 1}"
    let c := chainJ (4, 5) 0 #[]
    IO.println s!"chain {c} {readChain 1} same={ptrAddrUnsafe c[0]! == ptrAddrUnsafe c[1]!}"
