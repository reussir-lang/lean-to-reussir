/-
lean2rr classic corpus: `nqueens` (Perceus paper benchmark: count all
solutions of the n-queens problem by building the full list of solutions).

The Koka repository has no Lean version of this benchmark (its
`test/bench/lean/` holds only rbtree, rbtree-ck, rbtree4 and deriv). This is a
line-by-line port of the Koka version
  https://github.com/koka-lang/koka/blob/cf5607640061031052c2ad6da86ce0f9ac8cd287/test/bench/koka/nqueens.kk
cross-checked against the Haskell and OCaml versions next to it
(test/bench/haskell/nqueens.hs, test/bench/ocaml/nqueens.ml).

Port notes:
- Koka's `int32` becomes Lean's `Int32`; the solutions are `List (List Int32)`.
- Koka's `div` (possibly diverging) functions become `partial def`;
  `extend` is structurally recursive.
- Koka's borrow annotation `^xs` on `safe` has no Lean counterpart (Lean
  infers borrowing).
- `main` takes the board size as an optional first argument (default: the
  original constant 13) and prints the number of solutions.
-/

abbrev Solution := List Int32
abbrev Solutions := List (List Int32)

def safe (queen : Int32) (diag : Int32) : Solution → Bool
  | q :: qs => queen != q && queen != q + diag && queen != q - diag && safe queen (diag + 1) qs
  | []      => true

partial def appendSafe (queen : Int32) (xs : Solution) (xss : Solutions) : Solutions :=
  if queen <= 0 then xss
  else if safe queen 1 xs then appendSafe (queen - 1) xs ((queen :: xs) :: xss)
  else appendSafe (queen - 1) xs xss

def extend (queen : Int32) (acc : Solutions) : Solutions → Solutions
  | xs :: rest => extend queen (appendSafe queen xs acc) rest
  | []         => acc

partial def findSolutions (n : Int32) (queen : Int32) : Solutions :=
  if queen == 0 then [[]]
  else extend n [] (findSolutions n (queen - 1))

def queens (n : Int32) : Nat :=
  (findSolutions n n).length

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 13
  IO.println (queens (Int32.ofNat n))
  pure 0
