/-! Runtime test: structure fields used in one branch while another branch
keeps the structure whole (lean2rr moves the field projection into the
branches that use it, translation plan §5.5): association-list updates
whose matching arm calls a recursive function, a mutual version, a trie
insert, and a field used in both branches, before and after the branch. -/

inductive Tr where
  | node (count : Nat) (kids : List (UInt32 × Tr))

def Tr.bump : Tr → List UInt32 → Tr
  | .node c ks, [] => .node (c + 1) ks
  | .node c ks, _ :: rest => Tr.bump (.node (c + 2) ks) rest

def Tr.go (k : UInt32) (rest : List UInt32) : List (UInt32 × Tr) → List (UInt32 × Tr)
  | [] => [(k, Tr.bump (.node 0 []) rest)]
  | (k', t) :: more => if k == k' then (k', t.bump rest) :: more else (k', t) :: Tr.go k rest more

partial def Tr.size : Tr → Nat
  | .node c ks => c + (ks.map fun (_, t) => t.size).foldl (· + ·) 0

mutual
  partial def insT (path : List UInt32) : Tr → Tr
    | .node c ks => match path with
      | [] => .node (c + 1) ks
      | k :: rest => .node c (insL k rest ks)
  partial def insL (k : UInt32) (rest : List UInt32) : List (UInt32 × Tr) → List (UInt32 × Tr)
    | [] => [(k, insT rest (.node 0 []))]
    | (k', t) :: more => if k == k' then (k', insT rest t) :: more else (k', t) :: insL k rest more
end

structure Entry where
  key : String
  val : Nat
  tag : List Nat

def upd (k : String) : List Entry → List Entry
  | [] => [{ key := k, val := 1, tag := [] }]
  | e :: es => if e.key == k then { e with val := e.val + 1, tag := e.val :: e.tag } :: es else e :: upd k es

def both (p : Nat × List Nat) (b : Bool) : Nat × List Nat :=
  if b then (p.1 + p.2.length, p.2) else if p.1 > 3 then p else (p.1 * 2, 0 :: p.2)

def main (args : List String) : IO Unit := do
  let n := 20000 + args.length
  let mut l : List (UInt32 × Tr) := []
  for i in [0:n] do
    l := Tr.go ((i * 7919) % 200).toUInt32 (if i % 3 == 0 then [1] else []) l
  IO.println s!"assoc {l.length} {(l.map fun (_, t) => t.size).foldl (· + ·) 0}"
  let mut t : Tr := .node 0 []
  for i in [0:n] do
    t := insT [((i * 31) % 17).toUInt32, ((i * 7) % 5).toUInt32, (i % 3).toUInt32] t
  IO.println s!"trie {t.size}"
  let mut es : List Entry := []
  for i in [0:n / 10] do
    es := upd s!"k{(i * 13) % 50}" es
  IO.println s!"entries {es.length} {(es.map (·.val)).foldl (· + ·) 0} {(es.map (·.tag.length)).foldl (· + ·) 0}"
  let mut p : Nat × List Nat := (1, [])
  for i in [0:40] do
    p := both p (i % 4 == 0)
  IO.println s!"both {p.1} {p.2.length}"
