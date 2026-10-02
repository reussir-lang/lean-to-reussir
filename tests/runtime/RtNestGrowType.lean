/-! Runtime test: inductives whose recursive fields use the type at a larger
argument (nested datatypes with a non-uniform parameter, accepted by
`unsafe inductive`). Translating `Nest Nat` would need `Nest (Nat × Nat)`,
`Nest ((Nat × Nat) × (Nat × Nat))`, … without end: a field type that grows
is the uniform instantiation (`Nest Box`), and typed values convert to it
where they meet (plan §5.1, "Recursion").
- `Nest`: growth by a pair, values built and read by polymorphically
  recursive code, a typed `Nest (Nat × Nat)` built directly.
- `Perfect`: perfect trees, growth in the only recursive constructor.
- `G`: growth inside a function type (`Nat → G (List α)`).
- `M`: growth through a mutual partner (`A α` holds `B (α × α)`, `B β`
  holds `A (List β)`).
- `Rose`: growth through another inductive (`List (Rose (Option α))`). -/

unsafe inductive Nest (α : Type) where
  | nil
  | cons (x : α) (rest : Nest (α × α))

unsafe def Nest.size {α : Type} : Nest α → Nat
  | .nil => 0
  | .cons _ r => 1 + 2 * r.size

unsafe def Nest.build {α : Type} : Nat → α → (α → α) → Nest α
  | 0, _, _ => .nil
  | n + 1, x, f => .cons x (Nest.build n (x, f x) (fun p => (f p.1, f p.2)))

unsafe def Nest.flatten {α : Type} : Nest α → List α
  | .nil => []
  | .cons x r => x :: (r.flatten.foldr (fun p acc => p.1 :: p.2 :: acc) [])

unsafe def Nest.toStr {α : Type} [ToString α] : Nest α → String
  | .nil => "."
  | .cons x r => toString x ++ " " ++ r.toStr

unsafe def Nest.len {α : Type} : Nest α → Nat
  | .nil => 0
  | .cons _ r => 1 + r.len

unsafe inductive Perfect (α : Type) where
  | leaf (x : α)
  | succ (t : Perfect (α × α))

unsafe def Perfect.make {α : Type} : Nat → α → Perfect α
  | 0, x => .leaf x
  | n + 1, x => .succ (Perfect.make n (x, x))

unsafe def Perfect.sumWith {α : Type} (f : α → Nat) : Perfect α → Nat
  | .leaf x => f x
  | .succ t => t.sumWith (fun p => f p.1 + f p.2)

unsafe inductive G (α : Type) where
  | stop (x : α)
  | next (f : Nat → G (List α))

unsafe def G.depth {α : Type} : G α → Nat
  | .stop _ => 0
  | .next f => 1 + (f 0).depth

unsafe def G.deep {α : Type} : Nat → α → G α
  | 0, x => .stop x
  | n + 1, x => .next fun k => G.deep n (List.replicate (k + 1) x)

mutual
  unsafe inductive A (α : Type) where
    | done (x : α)
    | more (x : α) (b : B (α × α))
  unsafe inductive B (α : Type) where
    | done
    | more (y : α) (a : A (List α))
end

mutual
  unsafe def A.count {α : Type} : A α → Nat
    | .done _ => 1
    | .more _ b => 1 + b.count
  unsafe def B.count {β : Type} : B β → Nat
    | .done => 0
    | .more _ a => 1 + a.count
end

unsafe inductive Rose (α : Type) where
  | node (x : α) (kids : List (Rose (Option α)))

unsafe def Rose.count {α : Type} : Rose α → Nat
  | .node _ ks => 1 + (ks.map Rose.count).foldl (· + ·) 0

unsafe def Rose.mk {α : Type} : Nat → α → Rose α
  | 0, x => .node x []
  | n + 1, x => .node x [Rose.mk n (some x), Rose.mk n none]

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println s!"min {(Nest.cons (1 : Nat) (.cons (2, 3) .nil)).len}"
  let n1 : Nest Nat := Nest.build (k + 5) 1 (· + 1)
  IO.println s!"nest {n1.size} {n1.flatten.length} {n1.flatten.take 10} {n1.flatten.foldl (· + ·) 0}"
  let n2 : Nest String := Nest.build 4 "a" (· ++ "b")
  IO.println s!"nest str {n2.toStr}"
  let n3 : Nest (Nat → Nat) := Nest.build 4 id (fun f => f ∘ (· + 1))
  IO.println s!"nest fn {n3.flatten.map (· 0)}"
  let typed : Nest (Nat × String) := .cons (k, "x") (.cons ((1, "y"), (2, "z")) .nil)
  IO.println s!"nest typed {typed.len} {typed.size} {typed.toStr}"
  IO.println s!"perfect {(Perfect.make (k + 10) (3 : Nat)).sumWith id} {(Perfect.make 5 "ab").sumWith String.length}"
  IO.println s!"g {(G.next (fun n => G.stop [n, n]) : G Nat).depth} {(G.deep (k + 6) "s").depth}"
  let a : A Nat := .more 1 (.more (2, 3) (.more [(4, 5)] .done))
  IO.println s!"mutual {a.count}"
  IO.println s!"rose {(Rose.mk (k + 6) (1 : Nat)).count}"
