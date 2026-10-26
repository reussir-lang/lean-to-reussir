/-! Runtime test (memory): deep chains of closures freed whole. Each
level is a closure that captures the closure of the level below and then a
`String`, so the recursive field is not the last one: a destructor that
frees the fields in order keeps the level's state while it frees the level
below. `big`: closures of type `Nat → Nat` of 64 kinds (the closure type's
enum has 64 variants that capture a closure); `small`: closures of type
`String → Nat` of one kind. (The closures are in one-field structures, so
that Lean does not eta-expand the functions that build them.) Modes:
- `big N`, `small N`: a chain of N levels in an `IO.Ref`, freed by
  `r.set` (a free that the runtime starts);
- `bigu N`, `smallu N`: the same chain dropped by user code;
- `list N`: a `List` of N such closures, each capturing a closure of depth
  1 and a `String`, dropped whole by user code.
Natively the free is a loop over objects linked through themselves.
Arguments: MODE N (default: every mode, N = 1000). The peak memory is
checked by tests/runtime/alloc-check.sh (RtClosureChainFree.alloc). -/

structure Fn where
  f : Nat → Nat

structure SFn where
  f : String → Nat

@[noinline] def mkBig (k : Nat) (f : Fn) (s : String) : Fn :=
  match k % 64 with
  | 0 => ⟨fun x => f.f (x + 0) + s.length⟩
  | 1 => ⟨fun x => f.f (x + 1) + s.length⟩
  | 2 => ⟨fun x => f.f (x + 2) + s.length⟩
  | 3 => ⟨fun x => f.f (x + 3) + s.length⟩
  | 4 => ⟨fun x => f.f (x + 4) + s.length⟩
  | 5 => ⟨fun x => f.f (x + 5) + s.length⟩
  | 6 => ⟨fun x => f.f (x + 6) + s.length⟩
  | 7 => ⟨fun x => f.f (x + 7) + s.length⟩
  | 8 => ⟨fun x => f.f (x + 8) + s.length⟩
  | 9 => ⟨fun x => f.f (x + 9) + s.length⟩
  | 10 => ⟨fun x => f.f (x + 10) + s.length⟩
  | 11 => ⟨fun x => f.f (x + 11) + s.length⟩
  | 12 => ⟨fun x => f.f (x + 12) + s.length⟩
  | 13 => ⟨fun x => f.f (x + 13) + s.length⟩
  | 14 => ⟨fun x => f.f (x + 14) + s.length⟩
  | 15 => ⟨fun x => f.f (x + 15) + s.length⟩
  | 16 => ⟨fun x => f.f (x + 16) + s.length⟩
  | 17 => ⟨fun x => f.f (x + 17) + s.length⟩
  | 18 => ⟨fun x => f.f (x + 18) + s.length⟩
  | 19 => ⟨fun x => f.f (x + 19) + s.length⟩
  | 20 => ⟨fun x => f.f (x + 20) + s.length⟩
  | 21 => ⟨fun x => f.f (x + 21) + s.length⟩
  | 22 => ⟨fun x => f.f (x + 22) + s.length⟩
  | 23 => ⟨fun x => f.f (x + 23) + s.length⟩
  | 24 => ⟨fun x => f.f (x + 24) + s.length⟩
  | 25 => ⟨fun x => f.f (x + 25) + s.length⟩
  | 26 => ⟨fun x => f.f (x + 26) + s.length⟩
  | 27 => ⟨fun x => f.f (x + 27) + s.length⟩
  | 28 => ⟨fun x => f.f (x + 28) + s.length⟩
  | 29 => ⟨fun x => f.f (x + 29) + s.length⟩
  | 30 => ⟨fun x => f.f (x + 30) + s.length⟩
  | 31 => ⟨fun x => f.f (x + 31) + s.length⟩
  | 32 => ⟨fun x => f.f (x + 32) + s.length⟩
  | 33 => ⟨fun x => f.f (x + 33) + s.length⟩
  | 34 => ⟨fun x => f.f (x + 34) + s.length⟩
  | 35 => ⟨fun x => f.f (x + 35) + s.length⟩
  | 36 => ⟨fun x => f.f (x + 36) + s.length⟩
  | 37 => ⟨fun x => f.f (x + 37) + s.length⟩
  | 38 => ⟨fun x => f.f (x + 38) + s.length⟩
  | 39 => ⟨fun x => f.f (x + 39) + s.length⟩
  | 40 => ⟨fun x => f.f (x + 40) + s.length⟩
  | 41 => ⟨fun x => f.f (x + 41) + s.length⟩
  | 42 => ⟨fun x => f.f (x + 42) + s.length⟩
  | 43 => ⟨fun x => f.f (x + 43) + s.length⟩
  | 44 => ⟨fun x => f.f (x + 44) + s.length⟩
  | 45 => ⟨fun x => f.f (x + 45) + s.length⟩
  | 46 => ⟨fun x => f.f (x + 46) + s.length⟩
  | 47 => ⟨fun x => f.f (x + 47) + s.length⟩
  | 48 => ⟨fun x => f.f (x + 48) + s.length⟩
  | 49 => ⟨fun x => f.f (x + 49) + s.length⟩
  | 50 => ⟨fun x => f.f (x + 50) + s.length⟩
  | 51 => ⟨fun x => f.f (x + 51) + s.length⟩
  | 52 => ⟨fun x => f.f (x + 52) + s.length⟩
  | 53 => ⟨fun x => f.f (x + 53) + s.length⟩
  | 54 => ⟨fun x => f.f (x + 54) + s.length⟩
  | 55 => ⟨fun x => f.f (x + 55) + s.length⟩
  | 56 => ⟨fun x => f.f (x + 56) + s.length⟩
  | 57 => ⟨fun x => f.f (x + 57) + s.length⟩
  | 58 => ⟨fun x => f.f (x + 58) + s.length⟩
  | 59 => ⟨fun x => f.f (x + 59) + s.length⟩
  | 60 => ⟨fun x => f.f (x + 60) + s.length⟩
  | 61 => ⟨fun x => f.f (x + 61) + s.length⟩
  | 62 => ⟨fun x => f.f (x + 62) + s.length⟩
  | _ => ⟨fun x => f.f (x * 64) + s.length⟩

structure IFn where
  f : Int → Int

/-- As `mkBig`, the `String` used first, so a closure stores it before the
closure it captures. -/
@[noinline] def mkBigT (k : Nat) (f : IFn) (s : String) : IFn :=
  match k % 64 with
  | 0 => ⟨fun x => (s.length : Int) + f.f (x + 0)⟩
  | 1 => ⟨fun x => (s.length : Int) + f.f (x + 1)⟩
  | 2 => ⟨fun x => (s.length : Int) + f.f (x + 2)⟩
  | 3 => ⟨fun x => (s.length : Int) + f.f (x + 3)⟩
  | 4 => ⟨fun x => (s.length : Int) + f.f (x + 4)⟩
  | 5 => ⟨fun x => (s.length : Int) + f.f (x + 5)⟩
  | 6 => ⟨fun x => (s.length : Int) + f.f (x + 6)⟩
  | 7 => ⟨fun x => (s.length : Int) + f.f (x + 7)⟩
  | 8 => ⟨fun x => (s.length : Int) + f.f (x + 8)⟩
  | 9 => ⟨fun x => (s.length : Int) + f.f (x + 9)⟩
  | 10 => ⟨fun x => (s.length : Int) + f.f (x + 10)⟩
  | 11 => ⟨fun x => (s.length : Int) + f.f (x + 11)⟩
  | 12 => ⟨fun x => (s.length : Int) + f.f (x + 12)⟩
  | 13 => ⟨fun x => (s.length : Int) + f.f (x + 13)⟩
  | 14 => ⟨fun x => (s.length : Int) + f.f (x + 14)⟩
  | 15 => ⟨fun x => (s.length : Int) + f.f (x + 15)⟩
  | 16 => ⟨fun x => (s.length : Int) + f.f (x + 16)⟩
  | 17 => ⟨fun x => (s.length : Int) + f.f (x + 17)⟩
  | 18 => ⟨fun x => (s.length : Int) + f.f (x + 18)⟩
  | 19 => ⟨fun x => (s.length : Int) + f.f (x + 19)⟩
  | 20 => ⟨fun x => (s.length : Int) + f.f (x + 20)⟩
  | 21 => ⟨fun x => (s.length : Int) + f.f (x + 21)⟩
  | 22 => ⟨fun x => (s.length : Int) + f.f (x + 22)⟩
  | 23 => ⟨fun x => (s.length : Int) + f.f (x + 23)⟩
  | 24 => ⟨fun x => (s.length : Int) + f.f (x + 24)⟩
  | 25 => ⟨fun x => (s.length : Int) + f.f (x + 25)⟩
  | 26 => ⟨fun x => (s.length : Int) + f.f (x + 26)⟩
  | 27 => ⟨fun x => (s.length : Int) + f.f (x + 27)⟩
  | 28 => ⟨fun x => (s.length : Int) + f.f (x + 28)⟩
  | 29 => ⟨fun x => (s.length : Int) + f.f (x + 29)⟩
  | 30 => ⟨fun x => (s.length : Int) + f.f (x + 30)⟩
  | 31 => ⟨fun x => (s.length : Int) + f.f (x + 31)⟩
  | 32 => ⟨fun x => (s.length : Int) + f.f (x + 32)⟩
  | 33 => ⟨fun x => (s.length : Int) + f.f (x + 33)⟩
  | 34 => ⟨fun x => (s.length : Int) + f.f (x + 34)⟩
  | 35 => ⟨fun x => (s.length : Int) + f.f (x + 35)⟩
  | 36 => ⟨fun x => (s.length : Int) + f.f (x + 36)⟩
  | 37 => ⟨fun x => (s.length : Int) + f.f (x + 37)⟩
  | 38 => ⟨fun x => (s.length : Int) + f.f (x + 38)⟩
  | 39 => ⟨fun x => (s.length : Int) + f.f (x + 39)⟩
  | 40 => ⟨fun x => (s.length : Int) + f.f (x + 40)⟩
  | 41 => ⟨fun x => (s.length : Int) + f.f (x + 41)⟩
  | 42 => ⟨fun x => (s.length : Int) + f.f (x + 42)⟩
  | 43 => ⟨fun x => (s.length : Int) + f.f (x + 43)⟩
  | 44 => ⟨fun x => (s.length : Int) + f.f (x + 44)⟩
  | 45 => ⟨fun x => (s.length : Int) + f.f (x + 45)⟩
  | 46 => ⟨fun x => (s.length : Int) + f.f (x + 46)⟩
  | 47 => ⟨fun x => (s.length : Int) + f.f (x + 47)⟩
  | 48 => ⟨fun x => (s.length : Int) + f.f (x + 48)⟩
  | 49 => ⟨fun x => (s.length : Int) + f.f (x + 49)⟩
  | 50 => ⟨fun x => (s.length : Int) + f.f (x + 50)⟩
  | 51 => ⟨fun x => (s.length : Int) + f.f (x + 51)⟩
  | 52 => ⟨fun x => (s.length : Int) + f.f (x + 52)⟩
  | 53 => ⟨fun x => (s.length : Int) + f.f (x + 53)⟩
  | 54 => ⟨fun x => (s.length : Int) + f.f (x + 54)⟩
  | 55 => ⟨fun x => (s.length : Int) + f.f (x + 55)⟩
  | 56 => ⟨fun x => (s.length : Int) + f.f (x + 56)⟩
  | 57 => ⟨fun x => (s.length : Int) + f.f (x + 57)⟩
  | 58 => ⟨fun x => (s.length : Int) + f.f (x + 58)⟩
  | 59 => ⟨fun x => (s.length : Int) + f.f (x + 59)⟩
  | 60 => ⟨fun x => (s.length : Int) + f.f (x + 60)⟩
  | 61 => ⟨fun x => (s.length : Int) + f.f (x + 61)⟩
  | 62 => ⟨fun x => (s.length : Int) + f.f (x + 62)⟩
  | _ => ⟨fun x => (s.length : Int) + f.f (x * 64)⟩

structure UFn where
  f : UInt64 → UInt64

/-- Composition: a closure that captures two closures. -/
@[noinline] def comp (g h : UFn) : UFn := ⟨fun x => g.f (h.f x)⟩

@[noinline] def mkSmall (g : SFn) (s : String) : SFn :=
  ⟨fun t => g.f (t ++ s) + 1⟩

def chainBig (n : Nat) (f : Fn) : Fn := Id.run do
  let mut g := f
  for i in [0:n] do
    g := mkBig i g (toString i)
  return g

def chainSmall (n : Nat) (f : SFn) : SFn := Id.run do
  let mut g := f
  for i in [0:n] do
    g := mkSmall g (toString i)
  return g

def chainBigT (n : Nat) (f : IFn) : IFn := Id.run do
  let mut g := f
  for i in [0:n] do
    g := mkBigT i g (toString i)
  return g

def chainComp (n : Nat) (f : UFn) : UFn := Id.run do
  let mut g := f
  for i in [0:n] do
    g := comp g ⟨fun x => x + i.toUInt64⟩
  return g

def listOf (n : Nat) : List Fn :=
  (List.range n).map fun i => mkBig i ⟨fun x => x + i⟩ (toString i)

/-- Takes a chain and gives `n` back; the chain is dropped by user code,
here or at the call. -/
@[noinline] def keepBig (p : Fn × Nat) : Nat := p.2
@[noinline] def keepSmall (p : SFn × Nat) : Nat := p.2

def run (mode : String) (n : Nat) : IO Unit := do
  match mode with
  | "big" =>
    let r ← IO.mkRef (chainBig n ⟨fun x => x⟩)
    let c ← r.get
    IO.println s!"big {n}: {if n ≤ 1000 then c.f 1 else 0}"
    r.set ⟨fun x => x + 1⟩
    IO.println s!"freed {(← r.get).f 1}"
  | "small" =>
    let r ← IO.mkRef (chainSmall n ⟨fun t => t.length⟩)
    let c ← r.get
    IO.println s!"small {n}: {if n ≤ 100 then c.f "" else 0}"
    r.set ⟨fun t => t.length + 1⟩
    IO.println s!"freed {(← r.get).f ""}"
  | "bigu" =>
    -- Through a reference, so that the chain is built before the print;
    -- the reference gives it up first, and user code drops the last
    -- reference.
    let r ← IO.mkRef (chainBig n ⟨fun x => x⟩)
    let c ← r.get
    r.set ⟨fun x => x + 1⟩
    IO.println s!"bigu {n}: {keepBig (c, n)}"
  | "smallu" =>
    let r ← IO.mkRef (chainSmall n ⟨fun t => t.length⟩)
    let c ← r.get
    r.set ⟨fun t => t.length + 1⟩
    IO.println s!"smallu {n}: {keepSmall (c, n)}"
  | "bigt" =>
    let r ← IO.mkRef (chainBigT n ⟨fun x => x⟩)
    let c ← r.get
    IO.println s!"bigt {n}: {if n ≤ 1000 then c.f 1 else 0}"
    r.set ⟨fun x => x + 1⟩
    IO.println s!"freed {(← r.get).f 1}"
  | "comp" =>
    let r ← IO.mkRef (chainComp n ⟨fun x => x⟩)
    let c ← r.get
    IO.println s!"comp {n}: {if n ≤ 1000 then c.f 1 else 0}"
    r.set ⟨fun x => x + 1⟩
    IO.println s!"freed {(← r.get).f 1}"
  | "list" =>
    let l := listOf n
    IO.println s!"list {n}: {l.length} {if n ≤ 1000 then (l.map (·.f 1)).foldl (· + ·) 0 else 0}"
    IO.println s!"after {n}"
  | _ => IO.println s!"unknown mode {mode}"

def main (args : List String) : IO Unit := do
  match args with
  | [mode, n] => run mode n.toNat!
  | _ => for m in ["big", "small", "bigu", "smallu", "bigt", "comp", "list"] do run m 1000
