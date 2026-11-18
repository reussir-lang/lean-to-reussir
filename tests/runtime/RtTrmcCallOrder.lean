/-
A self call whose result goes into a constructor, with other work around it.

Part 1 (order): a call written after the self call runs after it. `ordApp`
applies a traced closure after the recursion, `ordExt` calls a traced
function after it, `ordBefore` calls one before it. Native Lean recurses
first in the first two (`g2 g1 g0`, `e2 e1 e0`) and last in the third
(`b0 b1 b2`). A compiler that turns such a function into a loop (tail
recursion modulo cons) must not move the self call past the later call:
Reussir before upstream #984 printed `g0 g1 g2` and `e0 e1 e2`.

Part 2 (results): the box-only shape. The constructor takes the self call's
result and elements that are stored in a box (a `Nat`, small and big, a
`Float`, a `UInt64`, a pair, a structure, an enumeration, a `String`, a
closure, a `Unit`), in a list and in a tree with two self calls, also with
an element that the self call reads too. Only the results show.
-/

@[noinline] def ordApp : List (Nat → Nat) → List Nat
  | [] => []
  | g :: xs =>
    let rest := ordApp xs
    g 1 :: rest

@[noinline] def tr (tag : String) (i : Nat) : Nat :=
  dbgTrace s!"{tag}{i}" fun _ => i + 1

@[noinline] def ordExt : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let rest := ordExt xs
    tr "e" x :: rest

@[noinline] def ordBefore : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let y := tr "b" x
    y :: ordBefore xs

@[noinline] def incNat : List Nat → List Nat
  | [] => []
  | x :: xs => (x + 1) :: incNat xs

@[noinline] def mulBig (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (x * k) :: mulBig k xs

@[noinline] def halfF : List Float → List Float
  | [] => []
  | x :: xs => (x / 2.0) :: halfF xs

@[noinline] def shl : List UInt64 → List UInt64
  | [] => []
  | x :: xs => (x <<< 61) :: shl xs

@[noinline] def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => (x, x * x) :: pairs xs

structure P where
  a : Nat
  b : String
  deriving Repr

@[noinline] def mkP : List Nat → List P
  | [] => []
  | x :: xs => { a := x, b := toString x } :: mkP xs

inductive Col where
  | r | g | b
  deriving Repr

@[noinline] def col : List Nat → List Col
  | [] => []
  | x :: xs => (if x % 3 == 0 then Col.r else if x % 3 == 1 then Col.g else Col.b) :: col xs

@[noinline] def strs : List Nat → List String
  | [] => []
  | x :: xs => s!"<{x}>" :: strs xs

@[noinline] def fns : List Nat → List (Nat → Nat)
  | [] => []
  | x :: xs => (fun y => y + x) :: fns xs

@[noinline] def units : List Nat → List Unit
  | [] => []
  | _ :: xs => () :: units xs

/-- The element goes into the self call and into the cell. -/
@[noinline] def scan (acc : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let s := acc + x * 4294967296
    s :: scan s xs

/-- The constructor takes the same boxed element twice. -/
@[noinline] def dup : List Float → List (Float × Float)
  | [] => []
  | x :: xs =>
    let y := x * 1.5
    (y, y) :: dup xs

inductive T (α : Type) where
  | leaf
  | node (l : T α) (v : α) (r : T α)

@[noinline] def build : Nat → Nat → T Nat
  | 0, _ => .leaf
  | d + 1, k => .node (build d (2 * k)) k (build d (2 * k + 1))

@[noinline] def mapT (f : Nat → Float) : T Nat → T Float
  | .leaf => .leaf
  | .node l v r => .node (mapT f l) (f v) (mapT f r)

@[noinline] def sumT : T Float → Float
  | .leaf => 0.0
  | .node l v r => sumT l + v + sumT r

def main : IO Unit := do
  let gs := (List.range 3).map fun i => fun x => dbgTrace s!"g{i}" fun _ => x + i
  IO.println (ordApp gs)
  IO.println (ordExt (List.range 3))
  IO.println (ordBefore (List.range 3))
  let l := List.range 6
  IO.println (incNat l)
  IO.println (mulBig (2 ^ 70) l)
  IO.println (halfF (l.map Nat.toFloat))
  IO.println (shl (l.map Nat.toUInt64))
  IO.println (pairs l)
  IO.println (repr (mkP l))
  IO.println (repr (col l))
  IO.println (strs l)
  IO.println ((fns l).map (· 10))
  IO.println (units l).length
  IO.println (scan (2 ^ 63 - 2 ^ 33) l)
  IO.println (dup (l.map Nat.toFloat))
  IO.println (sumT (mapT (fun n => n.toFloat * 0.5) (build 10 1)))
  let big := List.range 200000
  IO.println ((incNat big).foldl (· + ·) 0)
  IO.println ((mulBig (2 ^ 64) big).foldl (· + ·) 0)
  IO.println ((halfF (big.map Nat.toFloat)).foldl (· + ·) 0.0)
