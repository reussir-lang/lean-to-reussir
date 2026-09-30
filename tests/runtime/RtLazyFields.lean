import Std
/-! Runtime test: matches on a value that stays live in the arm (it is
stored whole in a new constructor) while its fields are used in other
branches. lean2rr binds such fields where they are used, matching the value
again there (see `lowerCases`). Checked on unique and on shared (persistent)
values. -/
open Std

inductive T where
  | leaf
  | node (size : Nat) (k : Nat) (v : String) (l r : T)
deriving Inhabited

def T.size : T → Nat
  | .leaf => 0
  | .node s _ _ _ _ => s

def T.mk (k : Nat) (v : String) (l r : T) : T := .node (l.size + r.size + 1) k v l r

/-- Weight-balanced rotations in the style of `Std.DTreeMap.Internal.balanceL`:
`l` is used whole in one branch and taken apart in the others. -/
def balanceL (k : Nat) (v : String) (l r : T) : T :=
  match l with
  | .leaf => T.mk k v .leaf r
  | .node ls lk lv ll lr =>
    if ls > 3 * r.size + 1 then
      match ll, lr with
      | .node lls _ _ _ _, .node _ lrk lrv lrl lrr =>
        if lr.size < 2 * lls then T.mk lk lv ll (T.mk k v lr r)
        else T.mk lrk lrv (T.mk lk lv ll lrl) (T.mk k v lrr r)
      | .leaf, .node _ lrk lrv _ _ => T.mk lrk lrv (T.mk lk lv .leaf .leaf) (T.mk k v .leaf r)
      | _, _ => T.mk lk lv ll (T.mk k v lr r)
    else .node (ls + r.size + 1) k v l r

def balanceR (k : Nat) (v : String) (l r : T) : T :=
  match r with
  | .leaf => T.mk k v l .leaf
  | .node rs rk rv rl rr =>
    if rs > 3 * l.size + 1 then
      match rl, rr with
      | .node _ rlk rlv rll rlr, .node rrs _ _ _ _ =>
        if rl.size < 2 * rrs then T.mk rk rv (T.mk k v l rl) rr
        else T.mk rlk rlv (T.mk k v l rll) (T.mk rk rv rlr rr)
      | .node _ rlk rlv _ _, .leaf => T.mk rlk rlv (T.mk k v l .leaf) (T.mk rk rv .leaf .leaf)
      | _, _ => T.mk rk rv (T.mk k v l rl) rr
    else .node (l.size + rs + 1) k v l r

def T.insert (x : Nat) (s : String) : T → T
  | .leaf => .node 1 x s .leaf .leaf
  | .node n k v l r =>
    match compare x k with
    | .lt => balanceL k v (l.insert x s) r
    | .gt => balanceR k v l (r.insert x s)
    | .eq => .node n x s l r

def T.toList : T → List (Nat × String)
  | .leaf => []
  | .node _ k v l r => l.toList ++ (k, v) :: r.toList

def T.check : T → Bool
  | .leaf => true
  | .node s _ _ l r => s == l.size + r.size + 1 && l.check && r.check

def T.height : T → Nat
  | .leaf => 0
  | .node _ _ _ l r => max l.height r.height + 1

/-- The matched list is used whole in one branch, its tail in the other,
behind a join point (the comparison's result). -/
def mergeLists : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    let c := if x < y then Ordering.lt else if x == y then .eq else .gt
    match c with
    | .gt => y :: mergeLists (x :: xs) ys
    | _ => x :: mergeLists xs (y :: ys)

/-- A field of a lazily bound field: `p` stays live, `p.2` is taken apart
only in one branch. -/
def pairs : List (Nat × List Nat) → List (Nat × List Nat)
  | [] => []
  | p :: rest =>
    match p with
    | (n, z :: zs) => if n % 3 == 0 then (n + z, zs) :: pairs rest else p :: (n, [z]) :: pairs rest
    | (_, []) => p :: pairs rest

/-- A structure `cases` (the pair) where `t` is dead: `r` is bound before it
(a structure match is no branch). -/
def subtrees (t : T) (acc : List Nat) : List Nat × Nat :=
  match t with
  | .leaf => (acc, 0)
  | .node s k _ l r =>
    let t2 := T.node s k "copy" t .leaf
    let acc := t2.size :: acc
    let (acc, a) := subtrees l acc
    let (acc, b) := subtrees r acc
    (acc, a + b + k)

inductive U where
  | leaf
  | node (l : U) (k : Nat) (r : U)
deriving Inhabited

def U.hash : U → Nat
  | .leaf => 7
  | .node l k r => (U.hash l * 31 + k * 17 + U.hash r * 13) % 1000000007
def U.size : U → Nat
  | .leaf => 0
  | .node l _ r => U.size l + 1 + U.size r

@[noinline] def mkU (n s : Nat) : U :=
  match n with
  | 0 => U.leaf
  | n+1 => U.node (mkU (n/2) (s*3+1)) (s % 1000) (mkU (n/3) (s*5+2))

@[noinline] def big (a b c : Nat) : Nat := (a * 3 + b * 5 + c) % 1000003

/-- z is matched lazily (stored whole); its field x is matched lazily too
(stored whole); the else branch does not use z but uses x, and contains
an outlined join point whose body takes x apart in one branch. -/
@[noinline] def nested (z : U) (c : Nat) : U :=
  match z with
  | .leaf => U.leaf
  | .node x zk zr =>
    match x with
    | .leaf => U.node z c z
    | .node xl xk _ =>
      if c < zk then U.node z c x
      else Id.run do
        let m ← if c % 4 == 1 then pure (big c 1 x.size) else if c % 4 == 0 then return U.node U.leaf (x.size) U.leaf else if c % 4 == 2 then pure (big c 2 xk) else pure (big c 3 zk)
        let a1 := big m xk c
        let a2 := big a1 m xk
        let a3 := big a2 a1 m
        let a4 := big a3 a2 a1
        let a5 := big a4 a3 a2
        let a6 := big a5 a4 a3
        let a7 := big a6 a5 a4
        let a8 := big a7 a6 a5
        let a9 := big a8 a7 a6
        let a10 := big a9 a8 a7
        let a11 := big a10 a9 a8
        let a12 := big a11 a10 a9
        let a13 := big a12 a11 a10
        let a14 := big a13 a12 a11
        let a15 := big a14 a13 a12
        let a16 := big a15 a14 a13
        let a17 := big a16 a15 a14
        let a18 := big a17 a16 a15
        let a19 := big a18 a17 a16
        let a20 := big a19 a18 a17
        let a21 := big a20 a19 a18
        let a22 := big a21 a20 a19
        let a23 := big a22 a21 a20
        let a24 := big a23 a22 a21
        let a25 := big a24 a23 a22
        let a26 := big a25 a24 a23
        let a27 := big a26 a25 a24
        let a28 := big a27 a26 a25
        let a29 := big a28 a27 a26
        let a30 := big a29 a28 a27
        let a31 := big a30 a29 a28
        let a32 := big a31 a30 a29
        let a33 := big a32 a31 a30
        let a34 := big a33 a32 a31
        let a35 := big a34 a33 a32
        let a36 := big a35 a34 a33
        let a37 := big a36 a35 a34
        let a38 := big a37 a36 a35
        let a39 := big a38 a37 a36
        let a40 := big a39 a38 a37
        let a41 := big a40 a39 a38
        let a42 := big a41 a40 a39
        let a43 := big a42 a41 a40
        let a44 := big a43 a42 a41
        let a45 := big a44 a43 a42
        let a46 := big a45 a44 a43
        let a47 := big a46 a45 a44
        let a48 := big a47 a46 a45
        let a49 := big a48 a47 a46
        if a49 % 2 == 0 then return U.node xl a49 U.leaf
        else return U.node x a49 zr

def main : IO Unit := do
  -- unique tree
  let mut t := T.leaf
  for i in [0:2000] do
    t := t.insert ((i * 7919) % 2003) s!"v{i}"
  IO.println s!"unique: size {t.size} check {t.check} height {t.height} sum {(t.toList.map (·.1)).foldl (· + ·) 0}"
  -- persistent versions share nodes: every rebuild must copy what is shared
  let mut versions : Array T := #[]
  let mut u := T.leaf
  for i in [0:300] do
    u := u.insert ((i * 37) % 301) s!"w{i}"
    if i % 50 == 0 then versions := versions.push u
  let grown := versions.map fun v => (List.range 40).foldl (fun a j => a.insert (j * 11 + 1000) "x") v
  for v in versions, g in grown do
    IO.println s!"version: {v.size} {v.check} -> {g.size} {g.check} {g.height}"
  IO.println s!"first keys: {(versions[1]!.toList.take 5)}"
  -- Std.TreeMap, unique and persistent
  let mut m : TreeMap Nat String := {}
  for i in [0:3000] do
    m := m.insert ((i * 101) % 3001) s!"{i}"
  let m2 := (List.range 1500).foldl (fun a i => a.erase (i * 2)) m
  let m3 := (List.range 100).foldl (fun a i => a.insert (i + 5000) "y") m
  IO.println s!"treemap: {m.size} {m2.size} {m3.size} {m.foldl (fun a k _ => a + k) 0} {m2.foldl (fun a k _ => a + k) 0}"
  IO.println s!"treemap get: {m.get? 1234} {m2.get? 1234} {m2.get? 1235} {m3.get? 5050}"
  -- lists
  let xs := (List.range 30).map (· * 3)
  let ys := (List.range 30).map (· * 2)
  IO.println s!"merge: {mergeLists xs ys}"
  IO.println s!"merge shared: {mergeLists xs xs |>.length} {xs.length}"
  let ps := (List.range 12).map fun i => (i, List.range (i % 4))
  IO.println s!"pairs: {pairs ps}"
  IO.println s!"pairs again: {pairs ps |>.length} {ps.length}"
  let (sl, ss) := subtrees (versions[2]!) []
  IO.println s!"subtrees: {sl.length} {sl.take 5} {ss}"
  let ub := mkU 18 1
  let mut acc := 0
  for i in [0:100] do
    acc := (acc + (nested ub (i * 37 % 1000)).hash) % 1000000007
  IO.println s!"nested: {acc} {ub.hash}"
