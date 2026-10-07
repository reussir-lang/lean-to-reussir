import Std.Data.HashMap
/-! Runtime test: a field of every kind whose type is a type parameter,
read, changed and stored back in a loop of N steps. Each structure
(`SX α` … `SH α β`) is held in a dependent field (`Dep F`: `s : F
ty.denote`, so where it is stored its element type is not known). Each
step runs two updates:
- code over the unknown element type (`uni`, a generic function called at
  `ty.denote`), which moves values of the element type around (duplicates
  a head, pushes an element again, applies a stored function);
- typed code (the branch `.nat`, where the element type is `Nat`), which
  reads the field at `Nat` and adds the step's number.
Native Lean does O(1) work and allocation per step in every mode (a list
cell, an array slot, a hash-map entry, a closure). A translation that
converts a container field between a typed and a uniform representation
at each crossing is O(N) per step: quadratic. Modes (field kinds): x
(`x y : α`), list (`List α`), array (`Array α`, updated in place), ref
(`IO.Ref α`), thunk (`Thunk α`), task (`Task α`), fn (`f : α → β`), fn2
(`g : α → α → α`), option (`Option α`), except (`Except ε α`), rows
(`Array (Array α)`), pairs (`List (α × β)`), hashmap (`Std.HashMap α β`).
Each mode prints a checksum of its final value. Arguments: MODE N
(default: every mode, N = 30). The output is checked here; the
allocations of each mode at two sizes by tests/runtime/alloc-check.sh
(RtDepFieldLoops.alloc). -/

inductive Ty | nat | str

@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .str => String

/-- A structure `F α` held where `α` is selected by a field. -/
structure Dep (F : Type → Type) where
  ty : Ty
  s : F ty.denote

-- x : α
structure SX (α : Type) where
  x : α
  y : α
  k : Nat

@[noinline] def SX.uni {α : Type} (s : SX α) : SX α := { x := s.y, y := s.x, k := s.k + 1 }

-- xs : List α
structure SL (α : Type) where
  xs : List α
  ys : List α

@[noinline] def SL.uni {α : Type} (s : SL α) : SL α :=
  match s.xs with
  | x :: _ => { s with ys := x :: s.ys }
  | [] => s

-- arr : Array α
structure SA (α : Type) where
  arr : Array α

@[noinline] def SA.uni {α : Type} (s : SA α) : SA α :=
  match s.arr.back? with
  | some v => { arr := (s.arr.push v).swapIfInBounds 0 (s.arr.size / 2) }
  | none => s

-- r : IO.Ref α (at α = List β)
structure SR (α : Type) where
  r : IO.Ref (List α)

@[noinline] def SR.uni {α : Type} (s : SR α) : IO Unit :=
  s.r.modify fun l => match l with
    | x :: _ => x :: l
    | [] => []

-- t : Thunk α (at α = List β)
structure STh (α : Type) where
  t : Thunk (List α)

@[noinline] def STh.uni {α : Type} (s : STh α) : STh α :=
  { t := Thunk.mk fun _ => match s.t.get with
      | x :: l => x :: x :: l
      | [] => [] }

-- k : Task α (at α = List β)
structure SK (α : Type) where
  k : Task (List α)

@[noinline] def SK.uni {α : Type} (s : SK α) : SK α :=
  { k := s.k.map fun l => match l with
      | x :: l => x :: x :: l
      | [] => [] }

-- f : α → β (at α = List γ, β = Nat)
structure SF (α : Type) where
  f : List α → Nat
  arg : List α
  acc : Nat

@[noinline] def SF.uni {α : Type} (s : SF α) : SF α := { s with acc := s.acc + s.f s.arg }

-- g : α → α → α (at α = List β)
structure SG (α : Type) where
  g : List α → List α → List α
  a : List α
  b : List α

@[noinline] def SG.uni {α : Type} (s : SG α) : SG α := { s with b := s.g s.a s.b }

-- opt : Option α (at α = List β)
structure SO (α : Type) where
  opt : Option (List α)

@[noinline] def SO.uni {α : Type} (s : SO α) : SO α :=
  match s.opt with
  | some (x :: l) => { opt := some (x :: x :: l) }
  | o => { opt := o }

-- e : Except ε α (at ε = String, α = List β)
structure SE (α : Type) where
  e : Except String (List α)

@[noinline] def SE.uni {α : Type} (s : SE α) : SE α :=
  match s.e with
  | .ok (x :: l) => { e := .ok (x :: x :: l) }
  | .ok [] => { e := .error "empty" }
  | er => { e := er }

-- rows : Array (Array α)
structure SAA (α : Type) where
  rows : Array (Array α)

@[noinline] def SAA.uni {α : Type} (s : SAA α) : SAA α :=
  { rows := s.rows.modify (s.rows.size - 1) fun r => match r[0]? with
      | some v => r.push v
      | none => r }

-- ps : List (α × β) (at β = Nat)
structure SP (α : Type) where
  ps : List (α × Nat)

@[noinline] def SP.uni {α : Type} (s : SP α) : SP α :=
  match s.ps with
  | p :: _ => { ps := (p.1, p.2 + 1) :: s.ps }
  | [] => s

-- m : Std.HashMap α β (at β = List α), with the key type's instances
structure SH (α : Type) [BEq α] [Hashable α] where
  m : Std.HashMap α (List α)
  k : α

instance instBEqDenote : (t : Ty) → BEq t.denote
  | .nat => inferInstanceAs (BEq Nat)
  | .str => inferInstanceAs (BEq String)

instance instHashableDenote : (t : Ty) → Hashable t.denote
  | .nat => inferInstanceAs (Hashable Nat)
  | .str => inferInstanceAs (Hashable String)

structure DH where
  ty : Ty
  s : SH ty.denote

@[noinline] def SH.uni {α : Type} [BEq α] [Hashable α] (s : SH α) : SH α :=
  match s.m.get? s.k with
  | some (x :: l) => { s with m := s.m.insert s.k (x :: x :: l) }
  | _ => s

-- The uniform steps: each calls its `uni` at `ty.denote`.
@[noinline] def Dep.uniX (d : Dep SX) : Dep SX := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniL (d : Dep SL) : Dep SL := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniA (d : Dep SA) : Dep SA := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniR (d : Dep SR) : IO Unit := d.s.uni
@[noinline] def Dep.uniT (d : Dep STh) : Dep STh := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniK (d : Dep SK) : Dep SK := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniF (d : Dep SF) : Dep SF := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniG (d : Dep SG) : Dep SG := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniO (d : Dep SO) : Dep SO := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniE (d : Dep SE) : Dep SE := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniAA (d : Dep SAA) : Dep SAA := ⟨d.ty, d.s.uni⟩
@[noinline] def Dep.uniP (d : Dep SP) : Dep SP := ⟨d.ty, d.s.uni⟩
@[noinline] def DH.uni (d : DH) : DH := ⟨d.ty, d.s.uni⟩

-- The typed steps (`.nat` branch).
@[noinline] def tX (d : Dep SX) (i : Nat) : Dep SX :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { s with x := s.x + i }⟩
  | d => d

@[noinline] def tL (d : Dep SL) (i : Nat) : Dep SL :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { s with xs := (i + s.ys.headD 0) :: s.xs }⟩
  | d => d

@[noinline] def tA (d : Dep SA) (i : Nat) : Dep SA :=
  match d with
  | ⟨.nat, s⟩ =>
    let a := s.arr.push i
    ⟨.nat, { arr := a.set! (i % a.size) (a[i % a.size]! + 1) }⟩
  | d => d

@[noinline] def tR (d : Dep SR) (i : Nat) : IO Nat :=
  match d with
  | ⟨.nat, s⟩ => do
    s.r.modify fun l => (i + l.headD 0) :: l
    return (← s.r.get).headD 0
  | _ => return 0

@[noinline] def tT (d : Dep STh) (i : Nat) : Dep STh :=
  match d with
  | ⟨.nat, s⟩ => let l := s.t.get; ⟨.nat, { t := Thunk.pure ((i + l.headD 0) :: l) }⟩
  | d => d

@[noinline] def tK (d : Dep SK) (i : Nat) : Dep SK :=
  match d with
  | ⟨.nat, s⟩ => let l := s.k.get; ⟨.nat, { k := .pure ((i + l.headD 0) :: l) }⟩
  | d => d

@[noinline] def tF (d : Dep SF) (i : Nat) : Dep SF :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { s with arg := i :: s.arg, acc := s.acc % 1000003 }⟩
  | d => d

@[noinline] def tG (d : Dep SG) (i : Nat) : Dep SG :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { s with a := i :: s.a }⟩
  | d => d

@[noinline] def tO (d : Dep SO) (i : Nat) : Dep SO :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { opt := some ((i + (s.opt.bind List.head?).getD 0) :: s.opt.getD []) }⟩
  | d => d

@[noinline] def tE (d : Dep SE) (i : Nat) : Dep SE :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { e := match s.e with
      | .ok l => if i % 50 == 49 then .error s!"e{i}" else .ok ((i + l.headD 0) :: l)
      | .error m => .ok [m.length] }⟩
  | d => d

@[noinline] def tAA (d : Dep SAA) (i : Nat) : Dep SAA :=
  match d with
  | ⟨.nat, s⟩ =>
    let rows := if i % 16 == 0 then s.rows.push #[i] else s.rows
    ⟨.nat, { rows := rows.modify (rows.size - 1) fun r => r.push (i + r.back?.getD 0) }⟩
  | d => d

@[noinline] def tP (d : Dep SP) (i : Nat) : Dep SP :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { ps := (i, i * i) :: s.ps }⟩
  | d => d

@[noinline] def tH (d : DH) (i : Nat) : DH :=
  match d with
  | ⟨.nat, s⟩ => ⟨.nat, { m := s.m.insert i [i, i + 1], k := i }⟩
  | d => d

def sumL (l : List Nat) : Nat := l.foldl (fun s x => (s * 31 + x) % 1000000007) 0

def run (mode : String) (n : Nat) : IO String := do
  match mode with
  | "x" =>
    let mut d : Dep SX := ⟨.nat, ⟨1, 2, 0⟩⟩
    for i in [0:n] do d := tX d.uniX i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.x} {s.y} {s.k}"
    | _ => return "?"
  | "list" =>
    let mut d : Dep SL := ⟨.nat, ⟨[], []⟩⟩
    for i in [0:n] do d := tL d.uniL i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.xs.length} {s.ys.length} {sumL s.xs} {sumL s.ys}"
    | _ => return "?"
  | "array" =>
    let mut d : Dep SA := ⟨.nat, ⟨#[]⟩⟩
    for i in [0:n] do d := tA d.uniA i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.arr.size} {sumL s.arr.toList}"
    | _ => return "?"
  | "ref" =>
    let d : Dep SR := ⟨.nat, ⟨← IO.mkRef []⟩⟩
    let mut h := 0
    for i in [0:n] do
      d.uniR
      h := (h + (← tR d i)) % 1000000007
    match d with
    | ⟨.nat, s⟩ => let l ← s.r.get; return s!"{h} {l.length} {sumL l}"
    | _ => return "?"
  | "thunk" =>
    let mut d : Dep STh := ⟨.nat, ⟨Thunk.pure []⟩⟩
    for i in [0:n] do d := tT d.uniT i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.t.get.length} {sumL s.t.get}"
    | _ => return "?"
  | "task" =>
    let mut d : Dep SK := ⟨.nat, ⟨.pure []⟩⟩
    for i in [0:n] do d := tK d.uniK i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.k.get.length} {sumL s.k.get}"
    | _ => return "?"
  | "fn" =>
    let mut d : Dep SF := ⟨.nat, ⟨fun l => l.headD 0 + 7, [], 0⟩⟩
    for i in [0:n] do d := tF d.uniF i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.acc} {s.arg.length} {s.f [5]}"
    | _ => return "?"
  | "fn2" =>
    let g : List Nat → List Nat → List Nat := fun a b => match a, b with
      | x :: _, y :: _ => (x + y) % 1000 :: b
      | x :: _, [] => [x]
      | [], _ => b
    let mut d : Dep SG := ⟨.nat, ⟨g, [], []⟩⟩
    for i in [0:n] do d := tG d.uniG i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.a.length} {s.b.length} {sumL s.b}"
    | _ => return "?"
  | "option" =>
    let mut d : Dep SO := ⟨.nat, ⟨none⟩⟩
    for i in [0:n] do d := tO d.uniO i
    match d with
    | ⟨.nat, s⟩ => return s!"{(s.opt.getD []).length} {sumL (s.opt.getD [])}"
    | _ => return "?"
  | "except" =>
    let mut d : Dep SE := ⟨.nat, ⟨.ok []⟩⟩
    for i in [0:n] do d := tE d.uniE i
    match d with
    | ⟨.nat, s⟩ => return match s.e with
      | .ok l => s!"ok {l.length} {sumL l}"
      | .error m => s!"error {m}"
    | _ => return "?"
  | "rows" =>
    let mut d : Dep SAA := ⟨.nat, ⟨#[#[]]⟩⟩
    for i in [0:n] do d := tAA d.uniAA i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.rows.size} {s.rows.foldl (· + ·.size) 0} {sumL (s.rows.toList.map fun r => sumL r.toList)}"
    | _ => return "?"
  | "pairs" =>
    let mut d : Dep SP := ⟨.nat, ⟨[]⟩⟩
    for i in [0:n] do d := tP d.uniP i
    match d with
    | ⟨.nat, s⟩ => return s!"{s.ps.length} {sumL (s.ps.map fun p => p.1 + p.2)}"
    | _ => return "?"
  | "hashmap" =>
    let mut d : DH := ⟨.nat, ⟨{}, 0⟩⟩
    for i in [0:n] do d := tH d.uni i
    match d with
    | ⟨.nat, s⟩ =>
      return s!"{s.m.size} {sumL ((List.range n).map fun i => sumL ((s.m.get? i).getD []))}"
    | _ => return "?"
  | m => return s!"unknown mode {m}"

def modes : List String :=
  ["x", "list", "array", "ref", "thunk", "task", "fn", "fn2", "option", "except", "rows", "pairs", "hashmap"]

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "30").toNat!
  match args.head? with
  | some m => IO.println s!"{m} {← run m n}"
  | none => for m in modes do IO.println s!"{m} {← run m n}"
