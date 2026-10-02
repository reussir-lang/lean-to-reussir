/-! Derived `BEq`, `DecidableEq` and `Ord` and a hand-written two-scrutinee
equality on a recursive inductive with 10 constructors: their wildcard arms
release the held fields out of line (`l2r_sink`; round 6 PRG6-02, Reussir
cost 22). Results, and the release of the values, as natively. -/

inductive E where
  | c0 (s : String) | c1 (a : E) (b : E) | c2 (n : Int) | c3 (xs : List E)
  | c4 (o : Option E) | c5 (f : UInt64) (e : E) | c6 | c7 (s : String) (e : E)
  | c8 (a b c : E) | c9 (n : Nat) (xs : List E)
  deriving BEq, Ord, Repr, Inhabited

inductive D where
  | d0 (s : String) | d1 (a : D) (b : D) | d2 (n : Int) | d3 (a : D) (n : Nat)
  | d4 (a : D) | d5 (e : D) | d6 | d7 (s : String) (e : D)
  | d8 (a b c : D) | d9 (n : Nat) (a : D)
  deriving DecidableEq

def E.eq : E → E → Bool
  | .c0 a, .c0 b => a == b
  | .c1 a b, .c1 c d => a.eq c && b.eq d
  | .c2 a, .c2 b => a == b
  | .c6, .c6 => true
  | .c7 s e, .c7 t f => s == t && e.eq f
  | .c9 n _, .c9 m _ => n == m
  | _, _ => false

def mk : Nat → E
  | 0 => .c6
  | n + 1 => match n % 10 with
    | 0 => .c0 s!"s{n}" | 1 => .c1 (mk n) (mk (n / 2)) | 2 => .c2 (-(n : Int))
    | 3 => .c3 [mk n, .c6] | 4 => .c4 (some (mk n)) | 5 => .c5 15 (mk n)
    | 6 => .c6 | 7 => .c7 "t" (mk n) | 8 => .c8 (mk n) .c6 (mk (n / 3))
    | _ => .c9 n [mk n]

def mkD : Nat → D
  | 0 => .d6
  | n + 1 => match n % 10 with
    | 0 => .d0 s!"s{n}" | 1 => .d1 (mkD n) (mkD (n / 2)) | 2 => .d2 (-(n : Int))
    | 3 => .d3 (mkD n) n | 4 => .d4 (mkD n) | 5 => .d5 (mkD n)
    | 6 => .d6 | 7 => .d7 "t" (mkD n) | 8 => .d8 (mkD n) .d6 (mkD (n / 3))
    | _ => .d9 n (mkD n)

def main : IO Unit := do
  let xs := (List.range 25).map mk
  let mut beq := 0; let mut heq := 0; let mut lt := 0
  for a in xs do
    for b in xs do
      if a == b then beq := beq + 1
      if a.eq b then heq := heq + 1
      if compare a b == .lt then lt := lt + 1
  IO.println s!"beq {beq} eq {heq} lt {lt}"
  let ds := (List.range 25).map mkD
  IO.println s!"deq {(ds.map fun a => (ds.filter fun b => decide (a = b)).length).foldl (· + ·) 0}"
  IO.println s!"{repr (mk 4)}"
