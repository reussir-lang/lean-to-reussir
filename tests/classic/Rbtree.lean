/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Coe
import Init.Data.Option.Basic
import Init.Data.List.BasicAux
import Init.System.IO
/-
lean2rr classic corpus: `rbtree` (Perceus paper benchmark).

Source: https://github.com/koka-lang/koka/blob/cf5607640061031052c2ad6da86ce0f9ac8cd287/test/bench/lean/rbtree.lean
        (branch `dev`, file added in commit f1e0b74b "add lean benchmarks").

Adaptations for Lean 4.33 (the algorithm is unchanged):
- the `universes u v w w'` line removed (unused; `universes` is no longer a command);
- the `{}` binder annotation on the `Leaf` constructor removed (obsolete syntax);
- `main` takes the tree size as an optional first argument (default: the
  original constant 4200000) instead of hard-coding it.
-/

set_option linter.unusedVariables false

inductive color
| Red | Black

inductive Tree
| Leaf                                                                           : Tree
| Node  (color : color) (lchild : Tree) (key : Nat) (val : Bool) (rchild : Tree) : Tree

/- variables {σ : Type w} -/
open color Nat Tree

def fold : (Nat → Bool → Nat → Nat) -> Tree → Nat → Nat
| f, Leaf, b               => b
| f, Node _ l k v r,     b => fold f r (f k v (fold f l b))

@[inline]
def balance1 : Nat → Bool → Tree → Tree → Tree
| kv, vv, t, Node _ (Node Red l kx vx r₁) ky vy r₂   => Node Red (Node Black l kx vx r₁) ky vy (Node Black r₂ kv vv t)
| kv, vv, t, Node _ l₁ ky vy (Node Red l₂ kx vx r)   => Node Red (Node Black l₁ ky vy l₂) kx vx (Node Black r kv vv t)
| kv, vv, t, Node _ l  ky vy r                       => Node Black (Node Red l ky vy r) kv vv t
| _,  _,  _,                                       _ => Leaf

@[inline]
def balance2 : Tree → Nat → Bool → Tree → Tree
| t, kv, vv, Node _ (Node Red l kx₁ vx₁ r₁) ky vy r₂    => Node Red (Node Black t kv vv l) kx₁ vx₁ (Node Black r₁ ky vy r₂)
| t, kv, vv, Node _ l₁ ky vy (Node Red l₂ kx₂ vx₂ r₂)   => Node Red (Node Black t kv vv l₁) ky vy (Node Black l₂ kx₂ vx₂ r₂)
| t, kv, vv, Node _ l ky vy r                           => Node Black t kv vv (Node Red l ky vy r)
| _, _, _,                                         _    => Leaf

def isRed : Tree → Bool
| Node Red _ _ _ _   => true
| _                  => false

def ins : Tree → Nat → Bool → Tree
| Leaf,                 kx, vx => Node Red Leaf kx vx Leaf
| Node Red a ky vy b,   kx, vx =>
   (if kx < ky then Node Red (ins a kx vx) ky vy b
    else if kx = ky then Node Red a kx vx b
    else Node Red a ky vy (ins b kx vx))
| Node Black a ky vy b,   kx, vx =>
    if kx < ky then
      (if isRed a then balance1 ky vy b (ins a kx vx)
       else Node Black (ins a kx vx) ky vy b)
    else if kx = ky then Node Black a kx vx b
    else if isRed b then balance2 a ky vy (ins b kx vx)
         else Node Black a ky vy (ins b kx vx)

def setBlack : Tree → Tree
| Node _ l k v r   => Node Black l k v r
| e                => e

def insert (t : Tree) (k : Nat) (v : Bool) : Tree :=
if isRed t then setBlack (ins t k v)
else ins t k v

def mkMapAux : Nat → Tree → Tree
| 0, m => m
| n+1,   m => mkMapAux n (insert m n (n % 10 = 0))

def mkMap (n : Nat) :=
mkMapAux n Leaf

def main (args : List String) : IO UInt32 :=
let n := (args.head?.bind String.toNat?).getD 4200000;
let m := mkMap n;
let v := fold (fun (k : Nat) (v : Bool) (r : Nat) => if v then r + 1 else r) m 0;
IO.println (toString v) *>
pure 0
