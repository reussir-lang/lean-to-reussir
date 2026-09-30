/-
lean2rr classic corpus: `cfold` (Perceus paper benchmark: constant folding
after re-association of a large expression tree).

The Koka repository has no Lean version of this benchmark; its Koka version
(https://github.com/koka-lang/koka/blob/cf5607640061031052c2ad6da86ce0f9ac8cd287/test/bench/koka/cfold.kk)
says "Adapted from https://github.com/leanprover/lean4/blob/IFL19/tests/bench/const_fold.hs",
i.e. from the Lean repository's const_fold benchmark. This file is the Lean
version of that benchmark as maintained for Lean 4.33:
  https://github.com/leanprover/lean4/blob/v4.33.0/tests/compile_bench/const_fold.lean
(so no separate `const-fold` case is needed). It computes the same thing as
cfold.kk (`max(v - 1, 0)` there is truncated `v - 1` on `Nat` here; the Koka
`main` uses n = 20 and prints the two values on separate lines).

Local change: `main` is a plain (not `unsafe`) `def` that takes the tree
depth as an optional first argument (default 20, the Koka constant) instead
of requiring exactly one argument.

Note: `appendAdd` is not tail recursive; its recursion depth is about
2^(n-1) (4M frames for n = 23). Native Lean runs `main` on a thread with a
1 GB stack (LEAN_DEFAULT_THREAD_STACK_SIZE in src/runtime/thread.cpp), which
is enough for the corpus sizes; an alternative implementation needs a
comparably deep stack.
-/

set_option linter.unusedVariables false

inductive Expr
| Var : Nat → Expr
| Val : Nat → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr

namespace Expr
open Nat

def mkExpr : Nat → Nat → Expr
| 0,     v => if v = 0 then Var 1 else Val v
| n+1,   v => Add (mkExpr n (v+1)) (mkExpr n (v-1))

def appendAdd : Expr → Expr → Expr
| Add e₁ e₂,   e₃ => Add e₁ (appendAdd e₂ e₃)
| e₁,          e₂ => Add e₁ e₂

def appendMul : Expr → Expr → Expr
| Mul e₁ e₂,   e₃ => Mul e₁ (appendMul e₂ e₃)
| e₁,          e₂ => Mul e₁ e₂

def reassoc : Expr → Expr
| Add e₁ e₂   =>
  let e₁' := reassoc e₁;
  let e₂' := reassoc e₂;
  appendAdd e₁' e₂'
| Mul e₁ e₂   =>
  let e₁' := reassoc e₁;
  let e₂' := reassoc e₂;
  appendMul e₁' e₂'
| e => e

def constFolding : Expr → Expr
| Add e₁ e₂   =>
  let e₁ := constFolding e₁;
  let e₂ := constFolding e₂;
  (match e₁, e₂ with
   | Val a, Val b         => Val (a+b)
   | Val a, Add e (Val b) => Add (Val (a+b)) e
   | Val a, Add (Val b) e => Add (Val (a+b)) e
   | _,     _             => Add e₁ e₂)
| Mul e₁ e₂   =>
  let e₁ := constFolding e₁;
  let e₂ := constFolding e₂;
  (match e₁, e₂ with
   | Val a, Val b         => Val (a*b)
   | Val a, Mul e (Val b) => Mul (Val (a*b)) e
   | Val a, Mul (Val b) e => Mul (Val (a*b)) e
   | _,     _             => Mul e₁ e₂)
| e         => e

def size : Expr → Nat
| Add l r   => size l + size r + 1
| Mul l r   => size l + size r + 1
| e         => 1

def toStringAux : Expr → String → String
| Var v,       r => r ++ "#" ++ toString v
| Val v,       r => r ++ toString v
| Add e₁ e₂,   r => (toStringAux e₂ ((toStringAux e₁ (r ++ "(")) ++ " + ")) ++ ")"
| Mul e₁ e₂,   r => (toStringAux e₂ ((toStringAux e₁ (r ++ "(")) ++ " * ")) ++ ")"

def eval : Expr → Nat
| Var x   => 0
| Val v   => v
| Add l r   => eval l + eval r
| Mul l r   => eval l * eval r

end Expr

open Expr

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 20;
  let e  := (mkExpr n 1);
  let v₁ := eval e;
  let v₂ := eval (constFolding (reassoc e));
  IO.println (toString v₁ ++ " " ++ toString v₂);
  pure 0
