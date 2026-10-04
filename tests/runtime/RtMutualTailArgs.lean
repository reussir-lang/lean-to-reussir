/-! Runtime test: tail calls through two and three mutually recursive
functions, with 4, 6 and 10 arguments (Nat, UInt64, Float, String, a list,
Bool, ...) and freshly built heap arguments, 300000 steps each; self tail
loops whose list argument is a fresh list or the scrutinee's own tail.
lean2rr's parameters are owned, so these calls are tail calls and the loops
run in constant stack: `RtMutualTailArgs.pipe` runs the lean2rr executable
with a 2 MB stack (`LEAN_STACK_SIZE_KB=2048`), where one frame of at least 16
bytes per step would need 4.8 MB. Native Lean borrows the `Nat` parameters
and releases them after the call, so its calls are not tail calls and use a
frame per step (100000 steps of the 10-argument cycle overflow an 8 MB
stack): it runs with its default stack. Also, at small sizes,
non-tail recursion through local recursive functions that capture the
enclosing function's variables or call it back, recursion under a
constructor of another inductive, mutual non-tail builders, and a
four-constructor operation loop.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/loopify_mutual_inline_temp, loopify_gap_mutual3,
loopify_mutual_countdown, mutual_loopify_acc, loopify_tail_ptr_alias,
loopify_variant_self_assign, loopify_computed_scrutinee_temp,
loopify_gap_ackermann, loopify_gap_nested_fix, inner_fix_captures_fn,
inner_fix_captures_ind, nested_fix_loopify, tmc_nested_ctor_wrap,
mutual_tmc_loopify, loopify_switch_break, loopify_nested_calls,
loopify_gap_pair_destructure, hof_tree_loopify, loopify_wrapper_receiver.
From the round-9 review, area crane (rv9/crane), program CrLoop. -/

namespace RtMutualTailArgs

inductive L | nil | cons (x : Nat) (t : L)
def L.hd : L → Nat | .nil => 0 | .cons x _ => x
@[noinline] def L.build (n : Nat) : L := Id.run do
  let mut acc := L.nil
  for i in [0:n] do acc := .cons (n - i) acc
  return acc

-- two mutually tail-recursive functions; each passes the other a fresh list
mutual
def evenStep : Nat → L → L → Nat → Nat
  | 0, _, keep, s => s + keep.hd
  | m + 1, l, keep, s => match l with
    | .nil => s
    | .cons x t => oddStep m (.cons x (.cons x .nil)) t (s + x % 7)
def oddStep : Nat → L → L → Nat → Nat
  | 0, _, keep, s => s + keep.hd
  | m + 1, l, keep, s => match l with
    | .nil => s
    | .cons x t => evenStep m (.cons (x + 1) .nil) (.cons x t) (s + keep.hd % 5)
end

-- three mutually tail-recursive functions with ten arguments of mixed kinds
mutual
def m3a : Nat → Nat → UInt64 → Float → String → L → Nat → Nat → Bool → Nat → Nat
  | 0, acc, u, f, s, l, b, c, z, d => acc + u.toNat + f.toUInt64.toNat + s.length + l.hd + b + c + (if z then 1 else 0) + d
  | n + 1, acc, u, f, s, l, b, c, z, d => m3b n (acc + 1) (u + 3) (f + 0.5) s (.cons n .nil) (b ^^^ n) c (!z) d
def m3b : Nat → Nat → UInt64 → Float → String → L → Nat → Nat → Bool → Nat → Nat
  | 0, acc, u, f, s, l, b, c, z, d => acc * 2 + u.toNat + f.toUInt64.toNat + s.length + l.hd + b + c + d + (if z then 1 else 0)
  | n + 1, acc, u, f, s, l, b, c, z, d => m3c n acc (u * 3) (f * 1.0) s l (b + 1) (c + l.hd % 3) z (d + 1)
def m3c : Nat → Nat → UInt64 → Float → String → L → Nat → Nat → Bool → Nat → Nat
  | 0, acc, u, f, s, l, b, c, z, d => acc * 3 + u.toNat + f.toUInt64.toNat + s.length + l.hd + b + c + d + (if z then 1 else 0)
  | n + 1, acc, u, f, s, l, b, c, z, d => m3a n (acc + n % 2) u f (if n % 1000 == 0 then s ++ "x" else s) l b (c % 1000) z d
end

-- three mutually tail-recursive functions with six arguments
mutual
def a6 : Nat → Nat → UInt64 → Float → String → L → Nat
  | 0, acc, u, f, s, l => acc + u.toNat + f.toUInt64.toNat + s.length + l.hd
  | n + 1, acc, u, f, s, l => b6 n (acc + 1) (u + 3) (f + 0.5) s (.cons n .nil)
def b6 : Nat → Nat → UInt64 → Float → String → L → Nat
  | 0, acc, u, f, s, l => acc * 2 + u.toNat + f.toUInt64.toNat + s.length + l.hd
  | n + 1, acc, u, f, s, l => c6 n acc (u * 3) (f * 1.0) s l
def c6 : Nat → Nat → UInt64 → Float → String → L → Nat
  | 0, acc, u, f, s, l => acc * 3 + u.toNat + f.toUInt64.toNat + s.length + l.hd
  | n + 1, acc, u, f, s, l => a6 n (acc + n % 2) u f (if n % 1000 == 0 then s ++ "x" else s) l
end

-- a tail loop whose list argument is a fresh list or the scrutinee's tail
@[noinline] def rot : Nat → L → L → Nat → Nat
  | 0, _, _, s => s
  | m + 1, l, acc, s => match l with
    | .nil => s
    | .cons 0 t => rot m (.cons 0 (.cons m .nil)) t (s + acc.hd)
    | .cons _ _ => s

inductive L3 | nil | one (k : Nat) | cons (x : Nat) (t : L3)
@[noinline] def drain : Nat → L3 → Nat → Nat
  | 0, _, s => s
  | m + 1, l, s => match l with
    | .nil => s
    | .one k => drain m (.cons k (.one (k + 1))) (s + k)
    | .cons x t => drain m t (s + x)

-- non-tail recursion over a freshly computed scrutinee
@[noinline] def wrap (m : Nat) (l : L) : L := .cons 7 (.cons m l)
def walk : Nat → L → Nat
  | 0, _ => 0
  | m + 1, l => match wrap m l with
    | .nil => 0
    | .cons x t => x + l.hd + walk m t

-- nested recursion through a local recursive function
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, n =>
    let rec ackN : Nat → Nat
      | 0 => ack m 1
      | k + 1 => ack m (ackN k)
    ackN n

-- a local recursion over the children that calls back into the outer function
inductive Rose | node (v : Nat) (cs : List Rose)
def Rose.sum : Rose → Nat
  | .node v cs =>
    let rec go : List Rose → Nat
      | [] => 0
      | c :: r => c.sum + go r
    v + go cs
@[noinline] def mkRose : Nat → Rose
  | 0 => .node 1 []
  | n + 1 => .node n [mkRose n, .node 2 [], mkRose (n / 2)]

-- inner local recursions capturing a function parameter, a pattern variable and
-- an inductive binder of the enclosing function
def walkF (f : Nat → Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | x :: r, acc =>
    let rec inner : Nat → Nat
      | 0 => f x + r.length
      | k + 1 => inner k + f k
    walkF f r (acc + inner (x % 5))

-- tail-modulo-cons under a constructor of another inductive
def spine : Nat → Rose
  | 0 => .node 0 []
  | k + 1 => .node (k + 1) [spine k]
def Rose.depth : Rose → Nat → Nat
  | .node _ (c :: _), a => c.depth (a + 1)
  | .node _ [], a => a

mutual
def evens : Nat → L
  | 0 => .nil
  | k + 1 => .cons (k + 1) (odds k)
def odds : Nat → L
  | 0 => .nil
  | k + 1 => .cons ((k + 1) * 10) (evens k)
end
def L.len : L → Nat → Nat | .nil, a => a | .cons _ t, a => t.len (a + 1)
def L.sum : L → Nat → Nat | .nil, a => a | .cons x t, a => t.sum (a + x)

-- a recursive function over an enumeration of 4 constructors
inductive Op | inc | dbl | neg | skip
def runOps : List Op → Int → Int
  | [], v => v
  | o :: r, v => match o with
    | .inc => runOps r (v + 1)
    | .dbl => runOps r (v * 2)
    | .neg => runOps r (-v)
    | .skip => runOps r v

-- a compound value computed after the recursive call; a pair result destructured
def nestedCalls : Nat → Nat
  | 0 => 1
  | n + 1 => let r := nestedCalls n; let here := r * 3 + n; here % 1000003
def swapPair : Nat → Nat × Nat
  | 0 => (1, 2)
  | n + 1 => let (a, b) := swapPair n; (b + n, a)

-- higher-order functions with two recursive calls per node
inductive T | leaf | node (l : T) (v : Nat) (r : T)
def T.mapT (f : Nat → Nat) : T → T | .leaf => .leaf | .node l v r => .node (l.mapT f) (f v) (r.mapT f)
def T.foldT (f : Nat → Nat → Nat) (z : Nat) : T → Nat | .leaf => z | .node l v r => f (l.foldT f z) (f v (r.foldT f z))
def T.filterSum (p : Nat → Bool) : T → Nat | .leaf => 0 | .node l v r => l.filterSum p + (if p v then v else 0) + r.filterSum p
def T.full : Nat → Nat → T | 0, _ => .leaf | d + 1, k => .node (T.full d (2 * k)) k (T.full d (2 * k + 1))

-- a recursive call wrapped in a one-field box constructor
inductive Bx | stop | box (b : Bx)
def mkBx : Nat → Bx | 0 => .stop | n + 1 => .box (mkBx n)
def Bx.len : Bx → Nat → Nat | .stop, a => a | .box b, a => b.len (a + 1)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 300000
  let k := args.length
  IO.println s!"mutual2: {evenStep n (L.build 4) .nil 0}"
  IO.println s!"mutual3x6: {a6 n 0 1 0.5 "s" .nil}"
  IO.println s!"mutual3x10: {m3a n 0 1 0.5 "s" .nil 0 0 false 0}"
  IO.println s!"rot: {rot n (.cons 0 (.cons 7 .nil)) .nil 0}"
  IO.println s!"drain: {drain n (.one 1) 0}"
  IO.println s!"walk: {walk (1000 + k) .nil}"
  IO.println s!"ack: {ack 2 (3 + k)} {ack 3 (3 + k)}"
  IO.println s!"rose: {(mkRose (12 + k)).sum}"
  IO.println s!"walkF: {walkF (· * 3) (List.range (20 + k)) 0}"
  IO.println s!"spine: {(spine (1000 + k)).depth 0}"
  IO.println s!"evensOdds: {(evens (1000 + k)).len 0} {(evens (1000 + k)).sum 0}"
  IO.println s!"ops: {runOps ((List.range (1000 + k)).map fun i => match i % 4 with | 0 => .inc | 1 => .dbl | 2 => .neg | _ => .skip) 1}"
  IO.println s!"nestedCalls: {nestedCalls (1000 + k)} swapPair: {swapPair (1001 + k)}"
  let t := T.full (10 + k) 1
  IO.println s!"tree: {(t.mapT (· + 1)).foldT (fun a b => (a + b) % 1000003) 0} {t.filterSum (· % 3 == 0)}"
  IO.println s!"box: {(mkBx (1000 + k)).len 0}"

end RtMutualTailArgs

def main (args : List String) : IO Unit := RtMutualTailArgs.main args
