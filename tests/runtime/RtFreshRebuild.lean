/-! Shapes for fresh-rebuild: join points, uniform code, existential
packages, nested matches, Except/Option/EStateM binds. -/
inductive T where
  | leaf
  | node (l : T) (k : Nat) (v : String) (r : T)
  deriving Inhabited, Repr

@[noinline] def ins (t : T) (k : Nat) (v : String) : T :=
  match t with
  | .leaf => .node .leaf k v .leaf
  | .node l k' v' r =>
    if k < k' then .node (ins l k v) k' v' r
    else if k' < k then .node l k' v' (ins r k v)
    else t

@[noinline] def find (t : T) (k : Nat) : Option T :=
  match t with
  | .leaf => none
  | .node l k' _ r =>
    if k < k' then find l k else if k' < k then find r k else some t

@[noinline] def sub (t : T) (k : Nat) : T :=
  match find t k with
  | some n => match n with
    | .node .. => n
    | .leaf => .leaf
  | none => .leaf

-- A join point after the match whose body returns the matched value.
@[noinline] def jpRet (t : T) (k : Nat) (flag : Bool) : T :=
  let x := ins t k "j"
  let y := if flag then 1 else 2
  match x with
  | .node l a b r => if a + y > 3 then .node r a b l else x
  | .leaf => .leaf

structure Pkg where
  α : Type
  v : Option α
  f : α → Nat

@[noinline] def usePkg (p : Pkg) : Option p.α :=
  match p.v with
  | some a => if p.f a > 2 then some a else none
  | none => none

@[noinline] def poly {α : Type} (g : Nat → Except String α) (n : Nat) : Except String α :=
  match g n with
  | .error e => .error e
  | .ok a => if n > 100 then .error "big" else .ok a

def step (n : Nat) : ExceptT String (StateM Nat) Nat := do
  let s ← get
  if n % 7 == 3 then throw s!"bad {n} at {s}"
  set (s + n)
  return n * 2

def run (xs : List Nat) : Except String Nat × Nat :=
  (xs.foldlM (fun acc x => do let y ← step x; return acc + y) 0).run.run 0

@[noinline] def chain (n : Nat) : Option (Nat × String) :=
  let a := if n % 3 == 0 then none else some (n, toString n)
  match a with
  | some p => if p.1 > 1000 then none else a
  | none => none

def main (args : List String) : IO Unit := do
  let k := args.length
  let mut t := T.leaf
  for i in [0:50] do
    t := ins t ((i * 37) % 101) s!"v{i}"
  IO.println (repr (sub t 37 |> fun n => match n with | .node _ k v _ => (k, v) | .leaf => (0, "")))
  IO.println (repr (match jpRet t 37 true with | .node _ k v _ => (k, v) | .leaf => (0, "")))
  IO.println (repr (match jpRet t 999 false with | .node _ k v _ => (k, v) | .leaf => (0, "")))
  let p : Pkg := ⟨String, some s!"hello{k}", String.length⟩
  IO.println (match usePkg p with | some s => s!"pkg {s}" | none => "pkg none")
  let r := poly (fun n => if n == 5 then Except.error "five" else Except.ok [n, k]) 5
  IO.println (match r with | .ok l => s!"ok {l}" | .error e => s!"err {e}")
  let r := poly (fun n => if n == 5 then Except.error "five" else Except.ok [n, k]) 6
  IO.println (match r with | .ok l => s!"ok {l}" | .error e => s!"err {e}")
  IO.println (repr (run [1, 2, 4, 5]))
  IO.println (repr (run [1, 2, 3, 5]))
  IO.println (repr (chain 4))
  IO.println (repr (chain 3))
  let mut acc := 0
  for i in [0:200000] do
    match run [i % 11, (i + 1) % 11] with
    | (.ok v, s) => acc := acc + v + s
    | (.error e, s) => acc := acc + e.length + s
  IO.println acc
