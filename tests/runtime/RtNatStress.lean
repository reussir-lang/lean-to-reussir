import Std.Data.HashMap

/-! Runtime test: the release of big numbers. Big `Nat`/`Int` values go
through every container (structures, constructors, `Array Nat`, arrays of
structures, `List`, `Option`, `IO.Ref` (set, swap and modify alternating
small and big values), `Thunk`, `Task`, `HashMap`, a tree, closures),
shared, updated in place and copied, round after round. Run by
the suite (outputs compared with native) and by `nat-alloc-check.sh`, which
builds it with leanrt's big-number counters and checks that every big
number a round makes is freed exactly once. Size argument: the number of
rounds. -/


structure Cell where
  a : Nat
  b : Int
  c : Nat
  deriving Inhabited

inductive T where
  | leaf
  | node (l : T) (k : Nat) (v : Int) (r : T)

def T.ins : T → Nat → Int → T
  | .leaf, k, v => .node .leaf k v .leaf
  | .node l k' v' r, k, v =>
    if k < k' then .node (l.ins k v) k' v' r
    else if k' < k then .node l k' v' (r.ins k v)
    else .node l k (v' + v) r

def T.total : T → Int
  | .leaf => 0
  | .node l k v r => l.total + (k : Int) + v + r.total

def big (i : Nat) : Nat := 2 ^ (64 + i % 70) + i

@[noinline] def round (i : Nat) (acc : Nat) : IO Nat := do
  let b := big i
  let c : Cell := { a := b, b := -(b : Int) * 3, c := b * b }
  let shared := (c, c)
  let mut arr : Array Nat := #[b, b + 1, i]
  arr := arr.set! 0 (arr[0]! * 2)
  arr := arr.push (b - 1)
  let cells : Array Cell := #[c, { c with a := c.a + 1 }]
  let lst : List Int := [c.b, c.b - 1, (i : Int)]
  let opt : Option Nat := if i % 2 == 0 then some b else none
  let r ← IO.mkRef b
  r.modify (· + i)
  let old ← r.swap (b * 3)
  let th : Thunk Nat := Thunk.mk fun _ => b + 5
  let tk : Task Int := Task.spawn fun _ => c.b - 7
  let m : Std.HashMap Nat Int := ({} : Std.HashMap Nat Int).insert b c.b |>.insert (b + 1) (-1)
  let t := (List.range 8).foldl (fun t j => t.ins (b + j % 3) ((j : Int) - c.b)) T.leaf
  let f : Nat → Nat := fun x => x + b
  let s1 := shared.1.a + shared.2.c % 1000 + arr.foldl (· + ·) 0 + cells[1]!.a % 7
  let s2 := (lst.foldl (· + ·) 0).natAbs % 1000 + opt.getD 0 % 13 + old % 11 + (← r.get) % 17
  let s3 := th.get % 19 + tk.get.natAbs % 23 + (m.getD b 0).natAbs % 29 + t.total.natAbs % 31 + f 3 % 37
  -- `IO.Ref Nat` / `IO.Ref Int` set, swap and modify, alternating small
  -- and big values: each set releases the old value after storing the new.
  let rn ← IO.mkRef (0 : Nat)
  let ri ← IO.mkRef (0 : Int)
  let mut s4 := 0
  for j in [0:4] do
    rn.set (if j % 2 == 0 then b + j else j)
    ri.set (if j % 2 == 0 then -(b : Int) - j else (j : Int))
    let o1 ← rn.swap (if j % 2 == 0 then j else b * 2)
    let o2 ← ri.swap (if j % 2 == 0 then (j : Int) else (b : Int) * 3)
    rn.modify (· + (if j % 2 == 0 then b else 1))
    ri.modify (· - (if j % 2 == 0 then 1 else (b : Int)))
    s4 := s4 + o1 % 7 + o2.natAbs % 11
  s4 := s4 + (← rn.get) % 13 + (← ri.get).natAbs % 17
  return (acc + s1 % 1000003 + s2 + s3 + s4) % 1000000007

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind String.toNat?).getD 1000
  let mut acc := 0
  for i in [0:n] do
    acc ← round i acc
  IO.println s!"rounds {n} checksum {acc}"
