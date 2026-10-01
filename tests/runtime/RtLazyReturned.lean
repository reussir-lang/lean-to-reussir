/-! Runtime test: a matched value returned whole (adv4 RP4-08, PF4-03) or a
structure stored whole (PF4-10) binds its other fields only where they are
used (translation plan §5.5, "reuse-friendly shapes"), so Reussir reuses the
matched cell. Results must not change: inserting a key already present
returns the tree itself (`ptrEq`), old versions stay intact while new ones
reuse cells, keys compared through calls (`Nat`, `String`, `compare`) and
pairs of an association list kept whole when skipped. -/

inductive TN where
  | leaf
  | node (l : TN) (k : Nat) (r : TN)
  deriving Inhabited

def TN.ins : TN → Nat → TN
  | .leaf, k => .node .leaf k .leaf
  | t@(.node l k' r), k => if k < k' then .node (l.ins k) k' r else if k' < k then .node l k' (r.ins k) else t

def TN.insC : TN → Nat → TN
  | .leaf, k => .node .leaf k .leaf
  | t@(.node l k' r), k =>
    match compare k k' with
    | .lt => .node (l.insC k) k' r
    | .gt => .node l k' (r.insC k)
    | .eq => t

def TN.toList : TN → List Nat
  | .leaf => []
  | .node l k r => l.toList ++ k :: r.toList

inductive TS where
  | leaf
  | node (l : TS) (k : String) (v : Nat) (r : TS)
  deriving Inhabited

def TS.ins : TS → String → TS
  | .leaf, k => .node .leaf k 1 .leaf
  | t@(.node l k' v r), k => if k < k' then .node (l.ins k) k' v r else if k' < k then .node l k' v (r.ins k) else t

def TS.sum : TS → Nat
  | .leaf => 0
  | .node l _ v r => l.sum + v + r.sum

def TS.size : TS → Nat
  | .leaf => 0
  | .node l _ _ r => l.size + 1 + r.size

inductive Tr where
  | node (count : Nat) (kids : List (UInt32 × Tr))

def Tr.bump : Tr → List UInt32 → Tr
  | .node c ks, [] => .node (c + 1) ks
  | .node c ks, _ :: rest => Tr.bump (.node (c + 2) ks) rest

def Tr.go (k : UInt32) (rest : List UInt32) : List (UInt32 × Tr) → List (UInt32 × Tr)
  | [] => [(k, Tr.bump (.node 0 []) rest)]
  | (k', t) :: more => if k == k' then (k', t.bump rest) :: more else (k', t) :: Tr.go k rest more

def Tr.counts (l : List (UInt32 × Tr)) : List (UInt32 × Nat) :=
  l.map fun (k, t) => match t with | .node c _ => (k, c)

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  -- Nat keys: versions kept, an existing key returns the same tree.
  let mut t := TN.leaf
  let mut versions : Array TN := #[]
  for i in [0:300] do
    t := t.ins ((i * 37 + k) % 101)
    if i % 50 == 0 then versions := versions.push t
  -- the root's key: the tree itself; another present key: a new path
  let t2 := t.ins k
  IO.println s!"nat {t.toList.length} same {ptrEq t t2} {ptrEq t (t.insC k)} {ptrEq t (t.ins 17)} versions {versions.map (·.toList.length)} {(versions[1]!).toList.take 8}"
  let mut c := TN.leaf
  for i in [0:200] do c := c.insC ((i * 13 + k) % 67)
  IO.println s!"compare {c.toList.length} {c.toList.take 10} {ptrEq c (c.insC k)} {ptrEq c (c.insC 5)}"
  -- String keys.
  let mut s := TS.leaf
  let mut sv : Array TS := #[]
  for i in [0:400] do
    s := s.ins (toString ((i * 7919 + k) % 211))
    if i % 100 == 0 then sv := sv.push s
  IO.println s!"string {s.size} {s.sum} same {ptrEq s (s.ins (toString k))} {ptrEq s (s.ins "5")} versions {sv.map (·.size)}"
  -- An association list whose skipped pairs are kept whole.
  let mut l : List (UInt32 × Tr) := []
  let mut lv : Array (List (UInt32 × Tr)) := #[]
  for i in [0:2000] do
    l := Tr.go ((i * 7919 + k) % 23).toUInt32 (if i % 3 == 0 then [1] else []) l
    if i % 500 == 0 then lv := lv.push l
  IO.println s!"assoc {l.length} {(Tr.counts l).take 6} versions {lv.map fun v => (Tr.counts v).foldl (fun a (_, n) => a + n) 0}"
