/-! Runtime test: cases of the shared dependent-type corpus (programs built
by another translator's team and checked against native Lean), combined:
each case keeps its code in a namespace named after its case id, and `main`
runs each with that case's arguments in this order, printing `-- <id>`
before it (and `exit <code>` after a `main : IO UInt32`). The cases, with
what each checks:
- `D71Breaker2Q09D`: Foldr with a closed ([], []) accumulator, no dependent
  types at all
- `D71Breaker2Q09E`: Foldr with ([], []) into two slots of one type, a join
  point in the lambda, no dependent types
- `D71Breaker2Q09F`: Q09E's split4 beside an unrelated dependent record (Box
  mode on)
- `D71Breaker2Q10`: Closed constants of the family type and closed lists of
  dependent records read by several readers.
- `D71Breaker2Q11`: Closures over dependent records stored and applied later
- `D71Breaker2Q12`: Family-typed lists passed through generic list and array
  combinators before a refined read.
- `D71Breaker2Q16`: Nat-indexed and Fin-indexed families read under dite /
  decide refinements.
- `D71Breaker2Q17`: Mutual recursion building a family-typed list with
  closed [] seeds, read under refinement.
- `D71Breaker2Q19`: IO.Ref of a family type written and read through generic
  helpers from refined arms.
- `D71Breaker2Q20`: Closures created in refined arms whose typed parameters
  later receive family values.
- `D71Breaker2Q21`: Closed seeds of folds in a Box-mode program -/

namespace D71Breaker2Q09D
/- Q09D: foldr with a closed ([], []) accumulator, no dependent types at all -/
@[noinline] def split3 (xs : List Nat) : List Nat × List String :=
  xs.foldr (fun x (ns, ss) => if x % 2 = 0 then (x :: ns, ss) else (ns, toString x :: ss)) ([], [])
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let (ns, ss) := split3 (List.range (n + 3))
  IO.println s!"{ns} {ss}"
end D71Breaker2Q09D

namespace D71Breaker2Q09E
/- Q09E: foldr with ([], []) into two slots of one type, a join point in the lambda, no dependent types -/
@[noinline] def split4 (xs : List Nat) : List Nat × List Nat :=
  xs.foldr (fun x (a, b) => if x % 2 = 0 then (x :: a, b) else (a, x :: b)) ([], [])
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println (split4 (List.range (n + 3)))
end D71Breaker2Q09E

namespace D71Breaker2Q09F
/- Q09F: Q09E's split4 beside an unrelated dependent record (Box mode on) -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def split4 (xs : List Nat) : List Nat × List Nat :=
  xs.foldr (fun x (a, b) => if x % 2 = 0 then (x :: a, b) else (a, x :: b)) ([], [])
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{split4 (List.range (n + 3))} {((List.range (n + 3)).map mk).map rd}"
end D71Breaker2Q09F

namespace D71Breaker2Q10
/- Q10: closed constants of the family type and closed lists of dependent records read by several readers. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
def K : Pkg := ⟨false, "const"⟩
def KN : Pkg := ⟨true, (41 : Nat)⟩
def KS : List Pkg := [⟨true, (1 : Nat)⟩, ⟨false, "a"⟩, ⟨true, (2 : Nat)⟩]
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, _⟩ => 0
@[noinline] def sz : Pkg → Nat
  | ⟨true, _⟩ => 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def showP : Pkg → String
  | ⟨true, v⟩ => let w : Nat := v; s!"N{w}"
  | ⟨false, v⟩ => let s : String := v; s!"S{s}"
@[noinline] def mapAll (f : Pkg → Nat) (ps : List Pkg) : List Nat := ps.map f
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println s!"{rd K} {sz K} {rd KN} {sz KN} {showP K} {showP KN}"
  IO.println s!"{mapAll rd KS} {mapAll sz KS} {KS.map showP}"
  let ps := KS ++ (List.range n).map (fun i => if i % 2 = 0 then KN else K)
  IO.println s!"{mapAll rd ps} {mapAll sz ps}"
  IO.println ((List.replicate n K).map showP)
end D71Breaker2Q10

namespace D71Breaker2Q11
/- Q11: closures over dependent records stored and applied later; closures returning family values. -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def swap : Pkg → Pkg
  | ⟨true, v⟩ => let w : Nat := v; ⟨false, toString w⟩
  | ⟨false, v⟩ => let s : String := v; ⟨true, s.length⟩
@[noinline] def mkGetter (p : Pkg) : Unit → (if p.b then Nat else String) := fun _ => p.v
@[noinline] def useGetter (p : Pkg) (g : Unit → (if p.b then Nat else String)) : Nat :=
  match h : p.b with
  | true => let v : Nat := cast (by simp [h]) (g ()); v
  | false => let s : String := cast (by simp [h]) (g ()); s.length * 10
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 2)).map mk
  let fs : List (Pkg → Nat) := [rd, fun p => rd (swap p), rd ∘ swap ∘ swap, fun p => if p.b then 1 else 2]
  IO.println (fs.map (fun f => ps.map f))
  let gs : List (Pkg → Pkg) := [id, swap, swap ∘ swap, fun p => if p.b then swap p else p]
  IO.println (gs.map (fun g => (ps.map g).map rd))
  IO.println (ps.map (fun p => useGetter p (mkGetter p)))
  let st := ps.foldl (fun (acc : Nat × List Pkg) p => (acc.1 + rd p, swap p :: acc.2)) (0, [])
  IO.println s!"{st.1} {st.2.map rd}"
end D71Breaker2Q11

namespace D71Breaker2Q12
/- Q12: family-typed lists passed through generic list and array combinators before a refined read. -/
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  match h : d with
  | true => (cast (by simp [h]) xs : List Nat).foldl (· + ·) 0
  | false => (cast (by simp [h]) xs : List String).foldl (fun a s => a + s.length) 0
@[noinline] def roundTrip (d : Bool) (xs : List (if d then Nat else String)) : List (if d then Nat else String) :=
  (xs.toArray.push (xs.headD (match d with | true => (0 : Nat) | false => ("z" : String)))).toList.reverse.map id
@[noinline] def viaFilter (d : Bool) (xs : List (if d then Nat else String)) : List (if d then Nat else String) :=
  (xs.filterMap some).foldr (· :: ·) [] ++ xs.take 1
@[noinline] def viaOpt (d : Bool) (xs : List (if d then Nat else String)) : Option (if d then Nat else String) :=
  xs.head?.map id
@[noinline] def rdOpt (d : Bool) (o : Option (if d then Nat else String)) : Nat :=
  match h : d, o with
  | true, some v => (cast (by simp [h]) v : Nat) + 1
  | false, some v => (cast (by simp [h]) v : String).length + 1
  | _, none => 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for d in [true, false] do
    let xs := mkL d n
    IO.println s!"{rdL d (roundTrip d xs)} {rdL d (viaFilter d xs)} {rdOpt d (viaOpt d xs)} {rdOpt d (viaOpt d (roundTrip d xs))} {(roundTrip d xs).length}"
end D71Breaker2Q12

namespace D71Breaker2Q16
/- Q16: Nat-indexed and Fin-indexed families read under dite / decide refinements. -/
def T (n : Nat) : Type := if n % 2 = 0 then Nat else String
@[noinline] def mkT (n : Nat) : T n :=
  if h : n % 2 = 0 then cast (by simp [T, h]) (n * 10) else cast (by simp [T, h]) s!"t{n}"
@[noinline] def rdT (n : Nat) (v : T n) : Nat :=
  if h : n % 2 = 0 then (cast (by simp [T, h]) v : Nat) + 1 else (cast (by simp [T, h]) v : String).length
@[noinline] def rdT2 (n : Nat) (v : T n) : String :=
  match h : decide (n % 2 = 0) with
  | true => toString (cast (by simp [T, of_decide_eq_true h]) v : Nat)
  | false => (cast (by simp [T, of_decide_eq_false h]) v : String) ++ "?"
def F : Fin 3 → Type
  | 0 => Nat
  | 1 => String
  | 2 => List Nat
@[noinline] def mkF : (i : Fin 3) → Nat → F i
  | 0, n => n
  | 1, n => s!"f{n}"
  | 2, n => List.range n
@[noinline] def rdF : (i : Fin 3) → F i → Nat
  | 0, v => let w : Nat := v; w
  | 1, v => let w : String := v; w.length
  | 2, v => let w : List Nat := v; w.foldl (· + ·) 0
structure Many where
  n : Nat
  v : T n
  i : Fin 3
  w : F i
@[noinline] def mkMany (k : Nat) : Many := ⟨k, mkT k, ⟨k % 3, Nat.mod_lt _ (by decide)⟩, mkF ⟨k % 3, Nat.mod_lt _ (by decide)⟩ k⟩
@[noinline] def rdMany (m : Many) : Nat := rdT m.n m.v + rdF m.i m.w
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  IO.println ((List.range (n + 3)).map (fun k => rdT k (mkT k)))
  IO.println ((List.range (n + 3)).map (fun k => rdT2 k (mkT k)))
  IO.println ((List.range (n + 3)).map (fun k => rdMany (mkMany k)))
  let ms := (List.range (n + 3)).map mkMany
  IO.println (ms.foldl (fun a m => a + rdMany m) 0)
end D71Breaker2Q16

namespace D71Breaker2Q17
/- Q17: mutual recursion building a family-typed list with closed [] seeds, read under refinement. -/
mutual
@[noinline] def evenL (d : Bool) : Nat → List (if d then Nat else String)
  | 0 => []
  | n + 1 => (match d with | true => ((n : Nat) :: oddL true n : List Nat) | false => (s!"e{n}" :: oddL false n : List String))
@[noinline] def oddL (d : Bool) : Nat → List (if d then Nat else String)
  | 0 => []
  | n + 1 => (match d with | true => ((n * 100 : Nat) :: evenL true n : List Nat) | false => (s!"o{n}" :: evenL false n : List String))
end
@[noinline] def rdL (d : Bool) (xs : List (if d then Nat else String)) : Nat :=
  if h : d = true then (cast (by simp [h]) xs : List Nat).foldl (· + ·) 0
  else (cast (by simp [h]) xs : List String).foldl (fun a s => a + s.length) 0
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for d in [true, false] do
    IO.println s!"{rdL d (evenL d n)} {rdL d (oddL d n)} {(evenL d n).length} {rdL d (evenL d n ++ oddL d (n + 1))}"
end D71Breaker2Q17

namespace D71Breaker2Q19
/- Q19: IO.Ref of a family type written and read through generic helpers from refined arms. -/
@[noinline] def writeAs (r : IO.Ref α) (x : α) : IO Unit := r.set x
@[noinline] def readAs (r : IO.Ref α) : IO α := r.get
@[noinline] def modAs (r : IO.Ref α) (f : α → α) : IO Unit := r.modify f
@[noinline] def wr (d : Bool) (r : IO.Ref (if d then Nat else String)) (n : Nat) : IO Unit :=
  if h : d = true then writeAs r (cast (by simp [h]) (n * 2)) else writeAs r (cast (by simp [h]) s!"w{n}")
@[noinline] def rd (d : Bool) (r : IO.Ref (if d then Nat else String)) : IO Nat := do
  let x ← readAs r
  if h : d = true then return (cast (by simp [h]) x : Nat) + 1 else return (cast (by simp [h]) x : String).length
@[noinline] def bump (d : Bool) (r : IO.Ref (if d then Nat else String)) : IO Unit :=
  if h : d = true then modAs r (fun x => cast (by simp [h]) ((cast (by simp [h]) x : Nat) + 5))
  else modAs r (fun x => cast (by simp [h]) ((cast (by simp [h]) x : String) ++ "!"))
@[noinline] def mkR (d : Bool) (n : Nat) : IO (IO.Ref (if d then Nat else String)) :=
  if h : d = true then IO.mkRef (cast (by simp [h]) n) else IO.mkRef (cast (by simp [h]) (toString n))
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for d in [true, false] do
    let r ← mkR d n
    IO.println (← rd d r)
    wr d r (n + 1); bump d r; bump d r
    IO.println (← rd d r)
    let r2 := r
    bump d r2
    IO.println s!"{← rd d r} {← rd d r2}"
end D71Breaker2Q19

namespace D71Breaker2Q20
/- Q20: closures created in refined arms whose typed parameters later receive family values. -/
@[noinline] def mkL (d : Bool) (n : Nat) : List (if d then Nat else String) :=
  match d with
  | true => (List.range n : List Nat)
  | false => ((List.range n).map toString : List String)
@[noinline] def mkK (d : Bool) : (if d then Nat else String) → Nat :=
  if h : d = true then cast (by simp [h]) (fun (n : Nat) => n + 1) else cast (by simp [h]) (fun (s : String) => s.length * 10)
@[noinline] def mkK2 (d : Bool) : (if d then Nat else String) → (if d then Nat else String) :=
  if h : d = true then cast (by simp [h]) (fun (n : Nat) => n * 2) else cast (by simp [h]) (fun (s : String) => s ++ s)
@[noinline] def useK (d : Bool) (xs : List (if d then Nat else String)) : List Nat :=
  let k := mkK d
  let k2 := mkK2 d
  xs.map k ++ (xs.map k2).map k
@[noinline] def ap (f : α → β) (x : α) : β := f x
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  for d in [true, false] do
    IO.println s!"{useK d (mkL d n)} {(mkL d n).map (ap (mkK d))} {((mkL d n).map (mkK2 d)).map (mkK d)}"
end D71Breaker2Q20

namespace D71Breaker2Q21
/- Q21: closed seeds of folds in a Box-mode program (which closed terms the shared-value rule accepts) -/
structure Pkg where
  b : Bool
  v : if b then Nat else String
@[noinline] def mk (n : Nat) : Pkg := if n % 2 = 0 then ⟨true, n⟩ else ⟨false, s!"s{n}"⟩
@[noinline] def rd : Pkg → Nat
  | ⟨true, v⟩ => let w : Nat := v; w + 1
  | ⟨false, v⟩ => let s : String := v; s.length
@[noinline] def seedList (ps : List Pkg) : List Pkg := ps.foldl (fun acc p => if p.b then p :: acc else acc) []
@[noinline] def seedArr (ps : List Pkg) : Array Pkg := ps.foldl (fun acc p => acc.push p) #[]
@[noinline] def seedOpt (ps : List Pkg) : Option Pkg := ps.foldl (fun acc p => if p.b then some p else acc) none
@[noinline] def seedPair (ps : List Pkg) : List Pkg × Nat := ps.foldl (fun (acc, k) p => (p :: acc, k + rd p)) ([], 0)
@[noinline] def seedPair2 (ps : List Pkg) : List Nat × List Pkg := ps.foldr (fun p (ns, qs) => (rd p :: ns, p :: qs)) ([], [])
@[noinline] def seedPair3 (xs : List Nat) : List Nat × List String := xs.foldr (fun x (ns, ss) => (x :: ns, toString x :: ss)) ([], [])
def caseMain (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3
  let ps := (List.range (n + 3)).map mk
  IO.println s!"{(seedList ps).map rd} {(seedArr ps).map rd} {(seedOpt ps).map rd}"
  IO.println s!"{(seedPair ps).1.map rd} {(seedPair ps).2} {(seedPair2 ps).1} {(seedPair2 ps).2.map rd} {seedPair3 (List.range n)}"
end D71Breaker2Q21

def main : IO Unit := do
  IO.println "-- D71Breaker2Q09D"
  D71Breaker2Q09D.caseMain ["4"]
  IO.println "-- D71Breaker2Q09E"
  D71Breaker2Q09E.caseMain ["4"]
  IO.println "-- D71Breaker2Q09F"
  D71Breaker2Q09F.caseMain ["4"]
  IO.println "-- D71Breaker2Q10"
  D71Breaker2Q10.caseMain ["3"]
  IO.println "-- D71Breaker2Q11"
  D71Breaker2Q11.caseMain ["4"]
  IO.println "-- D71Breaker2Q12"
  D71Breaker2Q12.caseMain ["4"]
  IO.println "-- D71Breaker2Q16"
  D71Breaker2Q16.caseMain ["5"]
  IO.println "-- D71Breaker2Q17"
  D71Breaker2Q17.caseMain ["4"]
  IO.println "-- D71Breaker2Q19"
  D71Breaker2Q19.caseMain ["4"]
  IO.println "-- D71Breaker2Q20"
  D71Breaker2Q20.caseMain ["4"]
  IO.println "-- D71Breaker2Q21"
  D71Breaker2Q21.caseMain ["4"]
