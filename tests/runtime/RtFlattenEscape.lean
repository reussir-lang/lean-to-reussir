/-! Runtime test: optimization `flatten-structs` and a constructor
application the pass leaves unbuilt that goes split both to another
loop's worker (`g`, which with no step returns it: its result is a tuple a
caller rebuilds) and to a second place: a peeled loop's next state
(`outer`, `outerJ` through an if-merge) or a split result (`pairOf`;
review of the pass, round 6, H1). Natively one object; such a value now
counts as built (`constrainDecl`'s flow sites), so it is one object here
too (`same=true`). -/
structure P where
  a : Nat
  b : Nat
  deriving Inhabited

-- every step builds a new P; with k = 0 it returns p itself
@[noinline] def g (p : P) : Nat → P
  | 0 => p
  | k+1 => g ⟨p.a + 1, p.b⟩ k

-- reads g's result field by field
@[noinline] def readG (n : Nat) : Nat := (g ⟨n, n⟩ n).a

-- peeled (s stored at the exit); c goes to g and becomes the next state
@[noinline] def outer (s : P) (z : Nat) : Nat → Array P → Array P
  | 0, acc => acc.push s
  | n+1, acc =>
    let c : P := ⟨s.a + 1, s.b⟩
    let r := g c z
    outer c z n (acc.push r)

-- the same, the next state through an if-merge
@[noinline] def outerJ (s : P) (z : Nat) : Nat → Array P → Array P
  | 0, acc => acc.push s
  | n+1, acc =>
    let c : P := ⟨s.a + 1, s.b⟩
    let r := g c z
    let q := if n % 2 == 0 then c else ⟨s.b, s.a + 2⟩
    outerJ q z n (acc.push r)

-- c both in g's result and in the pair: the pair's caller builds it twice
@[noinline] def pairOf (n z : Nat) : P × P :=
  let c : P := ⟨n, n + 1⟩
  (g c z, c)

@[noinline] def readPair (n : Nat) : Nat := (pairOf n 0).1.a + (pairOf n 1).2.b

@[noinline] def storePairs (n : Nat) : Array (P × P) := Id.run do
  let mut out := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (pairOf i 0)
  return out

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [mode, k] =>
    let n := k.toNat!
    let s0 : P := ⟨n, 1⟩
    let mut t := 0
    if mode == "outer" then
      for _ in [0:n] do t := t + (outer s0 0 1 #[]).size
    else if mode == "outerJ" then
      for _ in [0:n] do t := t + (outerJ s0 0 2 #[]).size
    else
      t := (storePairs n).size
    IO.println s!"{t} {readG 3} {readPair 2}"
  | _ =>
    let s0 : P := ⟨args.length + 7, 1⟩
    let o := outer s0 0 1 #[]
    let oj := outerJ s0 0 2 #[]
    let p := (storePairs 2)[1]!
    IO.println s!"outer {o.size} same={ptrAddrUnsafe o[0]! == ptrAddrUnsafe o[1]!}"
    IO.println s!"outerJ {oj.size} same={ptrAddrUnsafe oj[1]! == ptrAddrUnsafe oj[2]!}"
    IO.println s!"pairOf {p.1.a} {p.2.b} {readG 2} {readPair 1} same={ptrAddrUnsafe p.1 == ptrAddrUnsafe p.2}"
