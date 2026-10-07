/-! Runtime test: one large value (a list and an array of M numbers) stored in
K generic containers of every kind at once: `Option α`, `α × α`, `List α`,
`Array α`, `Thunk α`, a closure `Unit → α`, `Except String α`, an
`IO.Ref α`, each inside an existential package (`Pack`, its element type
a field) or a dependent field (`DPack`, read back at its own type), all
alive together, then each read in O(1). Native Lean shares the one value:
its allocations grow with K (the containers) plus M (the value, once),
never with K × M. A translation that copies the value into each container
in another representation needs K × M cells. The output is checked here;
the allocations and the peak memory with K and with M grown by
tests/runtime/alloc-check.sh (RtDepShareMany.alloc). Arguments: K M
(default 50 50). -/

structure Holder (α : Type) where
  opt : Option α
  pair : α × α
  list : List α
  arr : Array α
  th : Thunk α
  fn : Unit → α
  ex : Except String α

@[noinline] def Holder.of {α : Type} (v : α) : Holder α :=
  ⟨some v, (v, v), [v, v], #[v], Thunk.pure v, fun _ => v, .ok v⟩

structure Pack where
  α : Type
  h : Holder α
  f : α → Nat

/-- Code over the unknown type: reads every container once, O(1) each. -/
@[noinline] def Pack.read (p : Pack) : Nat :=
  let h := p.h
  (h.opt.map p.f).getD 0 + p.f h.pair.1 + p.f h.pair.2 + (h.list.head?.map p.f).getD 0 +
    (h.arr[0]?.map p.f).getD 0 + p.f h.th.get + p.f (h.fn ()) +
    (match h.ex with | .ok v => p.f v | .error _ => 0)

/-- Code over the unknown type that builds new containers of the value. -/
@[noinline] def Pack.rewrap (p : Pack) : Pack := ⟨p.α, Holder.of p.h.pair.2, p.f⟩

inductive Ty | list | arr

@[reducible] def Ty.denote : Ty → Type
  | .list => List Nat
  | .arr => Array Nat

structure DPack where
  ty : Ty
  h : Holder ty.denote

/-- Typed code: reads the containers at `List Nat` and `Array Nat`. -/
@[noinline] def DPack.read (d : DPack) : Nat :=
  match d with
  | ⟨.list, h⟩ => h.pair.1.headD 0 + (h.opt.getD []).length.min 1 + (h.list.headD []).headD 0
  | ⟨.arr, h⟩ => h.pair.2.size + h.th.get.back?.getD 0 + (h.fn ()).size

structure RPack where
  ty : Ty
  r : IO.Ref ty.denote

@[noinline] def RPack.read (p : RPack) : IO Nat :=
  match p with
  | ⟨.list, r⟩ => do return (← r.get).headD 0 + 1
  | ⟨.arr, r⟩ => do return (← r.get).size

/-- The packages (pure: a `Pack` lives in `Type 1`). -/
@[noinline] def buildPacks (k : Nat) (l : List Nat) (a : Array Nat) : Array Pack := Id.run do
  let mut packs : Array Pack := #[]
  for i in [0:k] do
    if i % 2 == 0 then
      packs := packs.push ⟨List Nat, Holder.of l, fun l => l.headD 0 + l.length⟩
    else
      packs := packs.push ⟨Array Nat, Holder.of a, fun a => a.size + a.back?.getD 0⟩
  return packs ++ packs.map Pack.rewrap

@[noinline] def buildDPacks (k : Nat) (l : List Nat) (a : Array Nat) : Array DPack :=
  (Array.range k).map fun i => if i % 2 == 0 then ⟨.list, Holder.of l⟩ else ⟨.arr, Holder.of a⟩

def main (args : List String) : IO Unit := do
  let k := (args.getD 0 "50").toNat!
  let m := (args.getD 1 "50").toNat!
  let l := (List.range m).map (· + 3)
  let a := (Array.range m).map (· * 2)
  let packs := buildPacks k l a
  let dpacks := buildDPacks k l a
  let mut rpacks : Array RPack := #[]
  for i in [0:k] do
    if i % 2 == 0 then rpacks := rpacks.push ⟨.list, ← IO.mkRef l⟩
    else rpacks := rpacks.push ⟨.arr, ← IO.mkRef a⟩
  let s := packs.foldl (fun s p => s + p.read) 0
  let t := dpacks.foldl (fun s d => s + d.read) 0
  let mut u := 0
  for r in rpacks do u := u + (← r.read)
  IO.println s!"packs {packs.size} {s}"
  IO.println s!"dependent {dpacks.size} {t}"
  IO.println s!"refs {rpacks.size} {u}"
  -- everything is still alive here, and shares `l` and `a`
  IO.println s!"value {l.length} {a.size} {l.headD 0} {a.back?.getD 0} {packs.size + dpacks.size}"
