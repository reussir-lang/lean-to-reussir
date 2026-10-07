/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71Breaker2Q01`: Refinements through a proof argument passed to a callee
  (h ▸), Subtype proofs, decide.
- `D71Breaker2Q02`: A Box value reaching a typed position through a type-
  class dictionary built under refinement.
- `D71Breaker2Q03`: Box values through two levels of generics,
  Function.comp, closures stored in lists.
- `D71Breaker2Q04`: Join points whose arms refine differently and then flow
  into generics.
- `D71Breaker2Q05`: Projections with a dependent result type, read under
  refinement
- `D71Breaker2Q06`: Thunk, Task and IO.Ref holding family values,
  forced/read through generic helpers at the family type.
- `D71Breaker2Q07`: A Bool-indexed family by pattern matching, Fin-indexed
  tables, mutual recursion across the family.
- `D71Breaker2Q08`: Sigma values nested in Option and List, generic snd
  projections, readers mapped over them.
- `D71Breaker2Q09`: Subtype-refined Pkg readers, proofs carried in
  structures, decide-based dispatch.
- `D71Breaker2Q09A`: Subtype-refined Pkg readers, proofs carried in
  structures, decide-based dispatch.
- `D71Breaker2Q09B`: Subtype-refined Pkg readers, proofs carried in
  structures, decide-based dispatch. -/

namespace D71Breaker2Q01
/- Q01: refinements through a proof argument passed to a callee (h ▸), Subtype proofs, decide. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String

@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)

@[noinline] def useH (d : Bool) (h : d = true) (xs : List (if d then Nat else String)) : Nat :=
  let ys : List Nat := cast (by simp [h]) (xs)
  ys.foldl (· + ·) 0
@[noinline] def useF (d : Bool) (h : d = false) (xs : List (if d then Nat else String)) : Nat :=
  let ys : List String := cast (by simp [h]) (xs)
  ys.foldl (fun a s => a + s.length) 0

@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  if h : d = true then useH d h xs else useF d (by simpa using h) xs + 1000

@[noinline] def rdD (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  if h : d = true then useH d h xs else useF d (by simpa using h) xs

@[noinline] def rdSub (q : { p : Pkg // p.b = true }) : Nat :=
  let v : Nat := cast (by simp [q.property]) q.val.v
  v * 2
@[noinline] def rdPkg (p : Pkg) : Nat :=
  if h : p.b = true then rdSub ⟨p, h⟩ else
    let s : String := cast (by simp [h]) p.v
    s.length

@[noinline] def rdDec (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  if decide (d = true) then
    match h : d with
    | true => (cast (by simp [h]) xs : List Nat).length
    | false => 0
  else xs.length + 100

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{rdL true (mkL true n)} {rdL false (mkL false n)}"
  IO.println s!"{rdD true (mkL true n)} {rdD false (mkL false n)}"
  IO.println ((List.range (n + 2)).map (fun i => rdPkg (mk i)))
  IO.println s!"{rdDec true (mkL true n)} {rdDec false (mkL false n)}"
  let d := n % 2 == 0
  IO.println s!"{rdL d (mkL d n)} {rdD d (mkL d (n + 1))} {rdDec d (mkL d n)}"
end D71Breaker2Q01

namespace D71Breaker2Q02
/- Q02: a Box value reaching a typed position through a type-class dictionary built under refinement. -/
class Rd (α : Type) where
  rd : α → Nat
  wr : Nat → α
instance : Rd Nat := ⟨id, id⟩
instance : Rd String := ⟨String.length, fun n => String.mk (List.replicate n 'x')⟩

structure Pkg where
  b : Bool
  v : if b then Nat else String

@[noinline] def instFor : (b : Bool) → Rd (if b then Nat else String)
  | true => inferInstanceAs (Rd Nat)
  | false => inferInstanceAs (Rd String)

@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rdP (p : Pkg) : Nat := (instFor p.b).rd p.v
@[noinline] def wrP (b : Bool) (n : Nat) : Pkg := ⟨b, (instFor b).wr n⟩
@[noinline] def viaDict [inst : Rd α] (x : α) (k : Nat) : Nat := inst.rd x + inst.rd (inst.wr k)
@[noinline] def rdP2 (p : Pkg) : Nat := @viaDict _ (instFor p.b) p.v 3

structure Packed where
  {α : Type}
  [inst : Rd α]
  val : α
@[noinline] def packP (p : Pkg) : Packed := @Packed.mk _ (instFor p.b) p.v
@[noinline] def rdPacked : Packed → Nat
  | @Packed.mk _ inst v => inst.rd v + inst.rd (inst.wr 2)

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  IO.println (ps.map rdP)
  IO.println (ps.map rdP2)
  IO.println ((ps.map packP).map rdPacked)
  IO.println ((List.range (n + 2)).map (fun i => rdP (wrP (i % 2 == 0) i)))
  IO.println ((List.range (n + 2)).map (fun i => rdPacked (packP (wrP (i % 3 == 0) i))))
end D71Breaker2Q02

namespace D71Breaker2Q03
/- Q03: Box values through two levels of generics, Function.comp, closures stored in lists. -/
@[noinline] def app (f : α → β) (x : α) : β := f x
@[noinline] def app2 (f : α → β) (x : α) : β := app f x
@[noinline] def app3 (f : α → β) (g : β → γ) (x : α) : γ := app2 g (app f x)
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match d, xs with
  | true, xs => xs.foldl (· + ·) 0
  | false, xs => xs.foldl (fun a s => a + s.length) 0
@[noinline] def hd (d : Bool) (xs : List (if d then Nat else String)) : String :=
  match d, xs with
  | true, x :: _ => let y : Nat := x; toString y
  | false, x :: _ => let y : String := x; y
  | _, [] => "-"

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let d := n % 2 == 0
  IO.println s!"{app (rdL d) (mkL d n)} {app2 (rdL d) (mkL d n)} {app3 (mkL d) (rdL d) n}"
  IO.println s!"{app2 (rdL true) (mkL true n)} {app2 (rdL false) (mkL false n)}"
  IO.println s!"{(rdL d ∘ List.reverse) (mkL d n)} {(rdL d ∘ mkL d) n} {(toString ∘ rdL d ∘ List.reverse ∘ mkL d) n}"
  let fs : List ((d : Bool) → List (if d then Nat else String) → Nat) := [rdL, fun d xs => rdL d xs.reverse, fun d xs => (hd d xs).length]
  IO.println (fs.map (fun f => f d (mkL d n)))
  IO.println (fs.map (fun f => f (!d) (mkL (!d) n)))
  let gs : List (List (if d then Nat else String) → Nat) := [rdL d, fun xs => xs.length, app (rdL d)]
  IO.println (gs.map (app · (mkL d n)))
  IO.println (app3 (fun k => mkL d k) (fun xs => hd d xs) n)
end D71Breaker2Q03

namespace D71Breaker2Q04
/- Q04: join points whose arms refine differently and then flow into generics. -/
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match d, xs with
  | true, xs => xs.foldl (· + ·) 0
  | false, xs => xs.foldl (fun a s => a + s.length) 0
@[noinline] def len (xs : List α) : Nat := xs.length
@[noinline] def dup (xs : List α) : List α := xs ++ xs

@[noinline] def jp1 (d : Bool) (n : Nat) (flag : Bool) : Nat :=
  let xs : List (if d then Nat else String) :=
    if flag then
      match d with
      | true => ((List.range n).map (· * 2) : List Nat)
      | false => ((List.range n).map (fun i => s!"<{i}>") : List String)
    else mkL d n
  rdL d xs + len xs + rdL d (dup xs)

@[noinline] def jp2 (d : Bool) (n : Nat) : Nat × String :=
  let r := match d with
    | true => let xs : List Nat := List.range n; (xs.length, toString xs)
    | false => let xs : List String := (List.range n).map toString; (xs.length * 10, toString xs)
  (r.1 + 1, r.2 ++ "!")

@[noinline] def jp3 (d : Bool) (n : Nat) : Nat :=
  let ys : List (if d then Nat else String) := match n % 3 with
    | 0 => mkL d n
    | 1 => match d with | true => ([n] : List Nat) | false => (["one"] : List String)
    | _ => []
  if h : d = true then (cast (by simp [h]) ys : List Nat).foldl (· + ·) 0
  else (cast (by simp [h]) ys : List String).foldl (fun a s => a + s.length) 0

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for d in [true, false] do
    IO.println s!"{jp1 d n true} {jp1 d n false} {jp2 d n} {jp3 d n} {jp3 d (n+1)} {jp3 d (n+2)}"
end D71Breaker2Q04

namespace D71Breaker2Q05
/- Q05: projections with a dependent result type, read under refinement; nested projections. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
structure Wrap where
  p : Pkg
  tag : Nat

@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def getV (p : Pkg) : if p.b then Nat else String := p.v
@[noinline] def getVW (w : Wrap) : if w.p.b then Nat else String := w.p.v
@[noinline] def rdV (p : Pkg) : Nat :=
  match h : p.b with
  | true => let v : Nat := cast (by simp [h]) (getV p); v + 1
  | false => let s : String := cast (by simp [h]) (getV p); s.length
@[noinline] def rdVW (w : Wrap) : Nat :=
  match h : w.p.b with
  | true => let v : Nat := cast (by simp [h]) (getVW w); v + w.tag
  | false => let s : String := cast (by simp [h]) (getVW w); s.length + w.tag
@[noinline] def setV (p : Pkg) (f : (if p.b then Nat else String) → (if p.b then Nat else String)) : Pkg := ⟨p.b, f p.v⟩
@[noinline] def bump (p : Pkg) : Pkg :=
  match h : p.b with
  | true => setV p (fun v => let n : Nat := cast (by simp [h]) (v); cast (by simp [h]) (n + 1))
  | false => setV p (fun v => let s : String := cast (by simp [h]) (v); cast (by simp [h]) (s ++ "+"))

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  IO.println (ps.map rdV)
  IO.println (ps.map (fun p => rdVW ⟨p, n⟩))
  IO.println ((ps.map bump).map rdV)
  IO.println (((ps.map bump).map bump).map rdV)
end D71Breaker2Q05

namespace D71Breaker2Q06
/- Q06: Thunk, Task and IO.Ref holding family values, forced/read through generic helpers at the family type. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def forceAs (t : Thunk α) : α := t.get
@[noinline] def waitAs (t : Task α) : α := t.get
@[noinline] def readAs (r : IO.Ref α) : IO α := r.get
@[noinline] def thunkOf (p : Pkg) : Thunk (if p.b then Nat else String) := Thunk.mk (fun _ => p.v)
@[noinline] def taskOf (p : Pkg) : Task (if p.b then Nat else String) := Task.spawn (fun _ => p.v)
@[noinline] def rdT (p : Pkg) : Nat :=
  match h : p.b with
  | true => let v : Nat := cast (by simp [h]) (forceAs (thunkOf p)); v
  | false => let s : String := cast (by simp [h]) (forceAs (thunkOf p)); s.length
@[noinline] def rdK (p : Pkg) : Nat :=
  match h : p.b with
  | true => let v : Nat := cast (by simp [h]) (waitAs (taskOf p)); v * 2
  | false => let s : String := cast (by simp [h]) (waitAs (taskOf p)); s.length * 2
@[noinline] def rdR (p : Pkg) : IO Nat := do
  let r ← IO.mkRef p.v
  match h : p.b with
  | true => let v : Nat := cast (by simp [h]) ((← readAs r)); return v + 100
  | false => let s : String := cast (by simp [h]) ((← readAs r)); return s.length + 100

structure Cell where
  b : Bool
  t : Thunk (List (if b then Nat else String))
  r : IO.Ref (Option (if b then Nat else String))
@[noinline] def mkCell (n : Nat) : IO Cell :=
  if n % 2 = 0 then return ⟨true, Thunk.mk (fun _ => (List.range n : List Nat)), ← IO.mkRef (some n : Option Nat)⟩
  else return ⟨false, Thunk.mk (fun _ => ((List.range n).map toString : List String)), ← IO.mkRef (none : Option String)⟩
@[noinline] def rdCell (c : Cell) : IO Nat := do
  let xs := forceAs c.t
  let o ← readAs c.r
  match h : c.b with
  | true => let ys : List Nat := cast (by simp [h]) xs; let oo : Option Nat := cast (by simp [h]) o; return ys.foldl (· + ·) (oo.getD 0)
  | false => let ys : List String := cast (by simp [h]) xs; let oo : Option String := cast (by simp [h]) o; return ys.length + (oo.map String.length).getD 7

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  IO.println (ps.map rdT)
  IO.println (ps.map rdK)
  IO.println (← ps.mapM rdR)
  let cs ← (List.range (n + 2)).mapM mkCell
  IO.println (← cs.mapM rdCell)
end D71Breaker2Q06

namespace D71Breaker2Q07
/- Q07: a Bool-indexed family by pattern matching, Fin-indexed tables, mutual recursion across the family. -/
def T : Bool → Type
  | true => Nat
  | false => String
@[noinline] def mkT : (b : Bool) → Nat → T b
  | true, n => n
  | false, n => s!"t{n}"
@[noinline] def rdT : (b : Bool) → T b → Nat
  | true, v => let w : Nat := v; w + 1
  | false, v => let w : String := v; w.length
@[noinline] def table (n : Nat) : Fin n → (b : Bool) × T b := fun i => if i.val % 2 = 0 then ⟨true, mkT true i.val⟩ else ⟨false, mkT false i.val⟩

mutual
@[noinline] def evenT : Nat → List ((b : Bool) × T b)
  | 0 => []
  | n + 1 => ⟨true, mkT true n⟩ :: oddT n
@[noinline] def oddT : Nat → List ((b : Bool) × T b)
  | 0 => []
  | n + 1 => ⟨false, mkT false n⟩ :: evenT n
end

@[noinline] def total (xs : List ((b : Bool) × T b)) : Nat := xs.foldl (fun a p => a + rdT p.1 p.2) 0
@[noinline] def flipT : (b : Bool) × T b → (b : Bool) × T b
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, mkT false w⟩
  | ⟨false, v⟩ => let w : String := v; ⟨true, w.length⟩

def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{total (evenT n)} {total (oddT n)} {total ((evenT n).map flipT)}"
  IO.println ((List.range n).map (fun i => if h : i < n then rdT (table n ⟨i, h⟩).1 (table n ⟨i, h⟩).2 else 0))
  IO.println s!"{rdT true (mkT true n)} {rdT false (mkT false n)}"
end D71Breaker2Q07

namespace D71Breaker2Q08
/- Q08: Sigma values nested in Option and List, generic snd projections, readers mapped over them. -/
def T : Bool → Type
  | true => Nat
  | false => String
abbrev S := (b : Bool) × T b
@[noinline] def mkS (n : Nat) : S := if n % 2 = 0 then ⟨true, (n : Nat)⟩ else ⟨false, (s!"q{n}" : String)⟩
@[noinline] def sndOf (p : S) : T p.1 := p.2
@[noinline] def rdS : S → Nat
  | ⟨true, v⟩ => let w : Nat := v; w * 3
  | ⟨false, v⟩ => let w : String := v; w.length
@[noinline] def rdS2 (p : S) : Nat :=
  match h : p.1 with
  | true => let v : Nat := cast (by simp [h, T]) (sndOf p); v * 3
  | false => let s : String := cast (by simp [h, T]) (sndOf p); s.length
@[noinline] def firstNat : List S → Option Nat
  | [] => none
  | ⟨true, v⟩ :: _ => let w : Nat := v; some w
  | ⟨false, _⟩ :: r => firstNat r
@[noinline] def pick (o : Option S) (d : Nat) : Nat := match o with
  | some p => rdS p
  | none => d
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ss := (List.range (n + 3)).map mkS
  IO.println (ss.map rdS)
  IO.println (ss.map rdS2)
  IO.println s!"{firstNat ss} {firstNat ss.reverse} {firstNat (ss.filter (fun p => !p.1))}"
  IO.println s!"{pick ss.head? n} {pick (ss.drop 1).head? n} {pick (ss.drop 100).head? n}"
  let os : List (Option S) := ss.map (fun p => if rdS p > 2 then some p else none)
  IO.println (os.map (pick · 0))
end D71Breaker2Q08

namespace D71Breaker2Q09
/- Q09: Subtype-refined Pkg readers, proofs carried in structures, decide-based dispatch. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
abbrev NatPkg := { p : Pkg // p.b = true }
abbrev StrPkg := { p : Pkg // p.b = false }
@[noinline] def NatPkg.get (q : NatPkg) : Nat := cast (by simp [q.property]) q.val.v
@[noinline] def StrPkg.get (q : StrPkg) : String := cast (by simp [q.property]) q.val.v
@[noinline] def split (ps : List Pkg) : List NatPkg × List StrPkg :=
  ps.foldr (fun p (ns, ss) =>
    if h : p.b = true then (⟨p, h⟩ :: ns, ss) else (ns, ⟨p, by simpa using h⟩ :: ss)) ([], [])
structure Evidence where
  p : Pkg
  h : p.b = true
@[noinline] def Evidence.get (e : Evidence) : Nat := cast (by simp [e.h]) e.p.v
@[noinline] def evid (p : Pkg) : Option Evidence := if h : p.b = true then some ⟨p, h⟩ else none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 3)).map mk
  let (ns, ss) := split ps
  IO.println s!"{ns.map NatPkg.get} {ss.map StrPkg.get}"
  IO.println ((ps.filterMap evid).map Evidence.get)
  IO.println (ns.map (fun q => q.val.b))
end D71Breaker2Q09

namespace D71Breaker2Q09A
/- Q09: Subtype-refined Pkg readers, proofs carried in structures, decide-based dispatch. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
abbrev NatPkg := { p : Pkg // p.b = true }
abbrev StrPkg := { p : Pkg // p.b = false }
@[noinline] def NatPkg.get (q : NatPkg) : Nat := cast (by simp [q.property]) q.val.v
@[noinline] def StrPkg.get (q : StrPkg) : String := cast (by simp [q.property]) q.val.v
@[noinline] def split (ps : List Pkg) : List NatPkg × List StrPkg :=
  ps.foldr (fun p (ns, ss) =>
    if h : p.b = true then (⟨p, h⟩ :: ns, ss) else (ns, ⟨p, by simpa using h⟩ :: ss)) ([], [])
structure Evidence where
  p : Pkg
  h : p.b = true
@[noinline] def Evidence.get (e : Evidence) : Nat := cast (by simp [e.h]) e.p.v
@[noinline] def evid (p : Pkg) : Option Evidence := if h : p.b = true then some ⟨p, h⟩ else none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 3)).map mk
  let (ns, ss) := split ps
  IO.println s!"{ns.map NatPkg.get} {ss.map StrPkg.get}"
end D71Breaker2Q09A

namespace D71Breaker2Q09B
/- Q09: Subtype-refined Pkg readers, proofs carried in structures, decide-based dispatch. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
abbrev NatPkg := { p : Pkg // p.b = true }
abbrev StrPkg := { p : Pkg // p.b = false }
@[noinline] def NatPkg.get (q : NatPkg) : Nat := cast (by simp [q.property]) q.val.v
@[noinline] def StrPkg.get (q : StrPkg) : String := cast (by simp [q.property]) q.val.v
@[noinline] def split (ps : List Pkg) : List NatPkg × List StrPkg :=
  ps.foldr (fun p (ns, ss) =>
    if h : p.b = true then (⟨p, h⟩ :: ns, ss) else (ns, ⟨p, by simpa using h⟩ :: ss)) ([], [])
structure Evidence where
  p : Pkg
  h : p.b = true
@[noinline] def Evidence.get (e : Evidence) : Nat := cast (by simp [e.h]) e.p.v
@[noinline] def evid (p : Pkg) : Option Evidence := if h : p.b = true then some ⟨p, h⟩ else none
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 3)).map mk
  IO.println ((ps.filterMap evid).map Evidence.get)
end D71Breaker2Q09B

def main : IO Unit := do
  IO.println "-- D71Breaker2Q01"
  D71Breaker2Q01.caseMain ["4"]
  IO.println "-- D71Breaker2Q02"
  D71Breaker2Q02.caseMain ["4"]
  IO.println "-- D71Breaker2Q03"
  D71Breaker2Q03.caseMain ["4"]
  IO.println "-- D71Breaker2Q04"
  D71Breaker2Q04.caseMain ["4"]
  IO.println "-- D71Breaker2Q05"
  D71Breaker2Q05.caseMain ["4"]
  IO.println "-- D71Breaker2Q06"
  D71Breaker2Q06.caseMain ["4"]
  IO.println "-- D71Breaker2Q07"
  D71Breaker2Q07.caseMain ["5"]
  IO.println "-- D71Breaker2Q08"
  D71Breaker2Q08.caseMain ["4"]
  IO.println "-- D71Breaker2Q09"
  D71Breaker2Q09.caseMain ["4"]
  IO.println "-- D71Breaker2Q09A"
  D71Breaker2Q09A.caseMain ["4"]
  IO.println "-- D71Breaker2Q09B"
  D71Breaker2Q09B.caseMain ["4"]
