inductive T where
  | leaf
  | node (l : T) (k : Nat) (v : String) (r : T)
  deriving Inhabited

def T.sum : T → Nat
  | .leaf => 0
  | .node l k v r => l.sum + k + v.length + r.sum

def T.ins (t : T) (k : Nat) (v : String) : T :=
  match t with
  | .leaf => .node .leaf k v .leaf
  | .node l k' v' r =>
    if k < k' then .node (l.ins k v) k' v' r
    else if k' < k then .node l k' v' (r.ins k v)
    else t

-- a call result matched; one arm returns it, others rebuild/reshape
def rot (t : T) (k : Nat) : T :=
  let x := t.ins k "z"
  match x with
  | .node l a b r => if a % 3 == 0 then .node r a b l else if a % 3 == 1 then x else .node l (a+1) b r
  | .leaf => .leaf

def second (_ : T) (y : T) : T := y

def mix (t : T) (k : Nat) : T :=
  let x := rot t k
  match x with
  | .node l a b r => if a % 2 == 0 then second x (.node l a b l) else x
  | .leaf => x

def opt (t : T) (k : Nat) : Option T :=
  let x := if k % 5 == 0 then none else some (mix t k)
  match x with
  | some y => if k % 7 == 0 then some (rot y k) else x
  | none => none

def main (args : List String) : IO Unit := do
  let n := 3000 + args.length
  let mut t := T.leaf
  let mut keep : Array T := #[]
  let mut acc := 0
  for i in [0:n] do
    let k := (i * 7919) % 1009
    t := t.ins k s!"v{k}"
    match opt t k with
    | some y =>
      acc := acc + y.sum % 1000
      if i % 13 == 0 then keep := keep.push y
      -- shared use: t still alive, y may share t's nodes
      let z := mix y (k + 1)
      acc := acc + z.sum % 97
    | none => acc := acc + 1
    if i % 100 == 0 then t := mix t i
  IO.println s!"{acc} {keep.size} {keep.foldl (fun s x => s + x.sum % 1000) 0} {t.sum}"
