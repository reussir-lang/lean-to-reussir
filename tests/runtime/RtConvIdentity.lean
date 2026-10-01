/-! Runtime test: identity of values lean2rr converts to another
representation (plan §5.1, §9): an `Array Nat`, a `List Nat` and an
`Option (List Nat)` stored in fields of uniform type (`Array α`, `List α`)
of existential packages are the same object as the original (two packages
of the same value are `ptrEq`, and reading the value back at its type gives
the original); a fixpoint in uniform code over a typed step function stops
when the step returns its argument; an update after a conversion leaves the
original unchanged; many conversions in a loop (small and large arrays). -/
structure PkgA where
  α : Type
  a : Array α
structure PkgL where
  α : Type
  l : List α
structure PkgO where
  α : Type
  o : Option (List α)
structure PkgF where
  α : Type
  f : Array α → Array α
  x : Array α

@[noinline] unsafe def sameA (p q : PkgA) : Bool := ptrAddrUnsafe p.a == ptrAddrUnsafe q.a
@[noinline] unsafe def sameL (p q : PkgL) : Bool := ptrAddrUnsafe p.l == ptrAddrUnsafe q.l
@[noinline] unsafe def sameO (p q : PkgO) : Bool := ptrAddrUnsafe p.o == ptrAddrUnsafe q.o
@[noinline] unsafe def backA (p : PkgA) : Array Nat := unsafeCast p.a
@[noinline] unsafe def backL (p : PkgL) : List Nat := unsafeCast p.l

-- A fixpoint in uniform code: stops when a step returns its argument.
@[noinline] unsafe def fixU (p : PkgF) (fuel : Nat) : Nat := go p.x fuel 0
where go (x : Array p.α) : Nat → Nat → Nat
  | 0, n => n + 1000
  | k + 1, n => let y := p.f x; if ptrEq x y then n else go y k (n + 1)

@[noinline] def shrink (a : Array Nat) : Array Nat := if a.size > 3 then a.pop else a

-- Updates after a conversion must not change the original.
@[noinline] unsafe def pushU (p : PkgA) (v : p.α) : PkgA := ⟨p.α, p.a.push v⟩
@[noinline] unsafe def sizeU (p : PkgA) : Nat := p.a.size

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  let ar : Array Nat := #[1, 2, k, 4, 5, 6]
  let l : List Nat := [k, 2, 3]
  IO.println s!"01 arr two {sameA ⟨Nat, ar⟩ ⟨Nat, ar⟩} back {ptrEq ar (backA ⟨Nat, ar⟩)}"
  IO.println s!"02 list two {sameL ⟨Nat, l⟩ ⟨Nat, l⟩} back {ptrEq l (backL ⟨Nat, l⟩)}"
  IO.println s!"03 opt two {sameO ⟨Nat, some l⟩ ⟨Nat, some l⟩}"
  IO.println s!"04 fix {fixU ⟨Nat, shrink, ar⟩ 50}"
  let p2 := pushU ⟨Nat, ar⟩ 7
  IO.println s!"05 push {sizeU p2} orig {ar.size} {ar} other {sameA p2 ⟨Nat, ar⟩}"
  let mut acc := 0
  for i in [0:200000] do
    let big : Array Nat := Array.range (100 + i % 7)
    if sameA ⟨Nat, big⟩ ⟨Nat, big⟩ then acc := acc + 1
  IO.println s!"06 loop {acc}"
  let mut bacc := 0
  for _ in [0:300] do
    let big : Array Nat := Array.range 100000
    if sameA ⟨Nat, big⟩ ⟨Nat, big⟩ then bacc := bacc + 1
  IO.println s!"07 big loop {bacc}"
