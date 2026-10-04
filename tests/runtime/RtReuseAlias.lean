/-! Runtime test: constructors rebuilt from a scrutinee that is still live, so
its cell must not be reused in place: the new cell's tail is the old cell
(`cons x l`), the scrutinee is reachable only through a closure passed to
`map`, a field goes into the new constructor while a sibling argument walks
the scrutinee, a node is rebuilt from a computation over itself, a child is
placed twice, both versions of a list survive. And where the scrutinee is
dead, reuse that changes the tag (two constructors of one arity), the field
types and layouts (UInt8/String/Float/UInt64 fields, stepped in loops), and
the element type (`Lst Nat` to `Lst (Lst Nat)` and back).
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/reuse_self_cycle, reuse_tag_mismatch, reuse_mixed_fields,
reuse_map_type_change, reuse_lambda_capture, reuse_scrutinee,
reuse_use_after_move, reuse_move_shadow, reuse_fn_in_body, reuse_alias,
ctor_arg_move_alias, ctor_arg_move_alias_rec, update_nth_bounds,
shared_uptr_escape.
From the round-9 review, area crane (rv9/crane), program CrReuse. -/

namespace RtReuseAlias

inductive L where
  | cons (x : Nat) (t : L)
  | nil

def L.len : L → Nat
  | .cons _ t => t.len + 1
  | .nil => 0

def L.sum : L → Nat
  | .cons x t => x + t.sum
  | .nil => 0

def L.show : L → String
  | .cons x t => s!"{x}," ++ t.show
  | .nil => "."

@[noinline] def L.ofRange (lo hi : Nat) : L :=
  if lo < hi then .cons lo (L.ofRange (lo + 1) hi) else .nil
termination_by hi - lo

-- reuse_self_cycle: the new cell's tail is the old cell itself.
@[noinline] def prependSelf (l : L) (b : Bool) : L :=
  if b then (match l with | .cons x _ => .cons x l | .nil => .nil) else l

-- reuse_tag_mismatch / reuse_mixed_fields: the dead scrutinee is rebuilt as the
-- other constructor (same arity), with differently typed fields in the second type.
inductive Dir | up (n : Nat) | down (n : Nat)
@[noinline] def flip (d : Dir) (f : Bool) : Dir :=
  if f then (match d with | .up n => .down n | .down n => .up n) else d
def Dir.code : Dir → Nat | .up n => 1000 + n | .down n => 2000 + n

inductive Mix
  | small (a : UInt8) (b : Nat) (s : String)
  | wide (a : String) (b : UInt64) (s : Nat)
  | flt (a : Float) (b : Nat) (s : String)
@[noinline] def rot (m : Mix) (go : Bool) : Mix :=
  if go then
    match m with
    | .small a b s => .wide s (a.toUInt64 + 1) (b + 1)
    | .wide a b s => .flt b.toFloat (s * 2) (a ++ "w")
    | .flt a b s => .small (a.toUInt8 + 3) (b + s.length) s!"{s}f"
  else m
def Mix.show : Mix → String
  | .small a b s => s!"small {a} {b} {s}"
  | .wide a b s => s!"wide {a} {b} {s}"
  | .flt a b s => s!"flt {a} {b} {s}"

-- reuse_map_type_change: a map whose output element type differs from the input.
inductive Lst (α : Type) | nil | cons (x : α) (t : Lst α)
@[noinline] def Lst.map {α β} (f : α → β) : Lst α → Lst β
  | .nil => .nil
  | .cons x t => .cons (f x) (t.map f)
@[noinline] def Lst.build (n : Nat) (acc : Lst Nat) : Lst Nat :=
  match n with | 0 => acc | m + 1 => Lst.build m (.cons n acc)
def Lst.sumN : Lst Nat → Nat | .nil => 0 | .cons x t => x + t.sumN

-- reuse_lambda_capture: the scrutinee is reachable only through a closure.
@[noinline] def L.mapf (f : Nat → Nat) : L → L
  | .cons h t => .cons (f h) (t.mapf f)
  | .nil => .nil
@[noinline] def addLenToTail (l : L) (b : Bool) : L :=
  if b then
    match l with
    | .cons h t => .cons (h + 1) (t.mapf (fun x => x + l.len))
    | .nil => .nil
  else l

-- reuse_use_after_move / reuse_fn_in_body: the new head is computed from the whole
-- old list.
@[noinline] def headFromLen (l : L) : L :=
  match l with | .cons _ xs => .cons (l.len * 100 + l.sum) xs | .nil => .nil

-- reuse_scrutinee / reuse_move_shadow: a tree rebuilt from itself, one child
-- used twice.
inductive T | leaf | node (l : T) (v : Nat) (r : T)
def T.sum : T → Nat | .leaf => 0 | .node l v r => l.sum + v + r.sum
def T.lv : T → Nat | .node (.node _ v _) _ _ => v | _ => 0
def T.rv : T → Nat | .node _ _ (.node _ v _) => v | _ => 0
@[noinline] def selfSum (t : T) : T :=
  match t with | .leaf => .leaf | .node _ _ r => .node .leaf (t.lv + t.rv) r
@[noinline] def dupLeft (t : T) (b : Bool) : T :=
  if b then (match t with | .node lt x _ => .node lt x lt | .leaf => .leaf) else t
@[noinline] def mkT (k : Nat) : T := .node (.node .leaf (10 + k) .leaf) (20 + k) (.node .leaf (30 + k) .leaf)

-- ctor_arg_move_alias(_rec): a field goes into the new constructor while a sibling
-- argument still walks the scrutinee.
inductive In | nil | cons (x : Nat) (t : In)
def In.sum : In → Nat | .nil => 0 | .cons x t => x + t.sum
def osum : Lst In → Nat | .nil => 0 | .cons h t => h.sum + osum t
inductive Pack | pack (i : In) (s : Nat) | plist (l : Lst In)
@[noinline] def grab (o : Lst In) : Pack :=
  match o with | .nil => .plist o | .cons h _ => .pack h (osum o)
@[noinline] def annotate (o : Lst In) : Lst In :=
  match o with
  | .nil => o
  | .cons h t => .cons h (.cons (.cons (osum o) .nil) (annotate t))

-- reuse_alias: a list and its incremented copy both survive.
@[noinline] def incHead : L → L | .cons x xs => .cons (x + 1) xs | .nil => .nil
@[noinline] def bothVersions (l : L) : L × L := (incHead l, l)
@[noinline] def scrutInBranch (l : L) : L × L :=
  match l with | .nil => (.nil, .nil) | .cons _ xs => (l, xs)

-- update_nth_bounds: out of range returns the same (shared) list.
@[noinline] def updateNth {α} (n : Nat) (x : α) (l : List α) : List α :=
  if n < l.length then l.take n ++ x :: l.drop (n + 1) else l

-- shared_uptr_escape: one value used in a sharing and a non-sharing branch.
@[noinline] def condShare (t : T) (flag : Nat) : Nat :=
  match flag with
  | 0 => t.sum
  | _ => let p := (t, t); p.1.sum + p.2.sum
@[noinline] def pickSub (t : T) (w : Nat) : T :=
  match t with | .leaf => .leaf | .node l _ r => if w == 0 then l else r

-- Loop: step a unique value many times through each rebuild (in-place reuse when
-- it is unique; a copy when shared).
@[noinline] def flipLoop (n : Nat) (d : Dir) : Dir := Id.run do
  let mut d := d
  for i in [0:n] do d := flip d (i % 3 != 0)
  return d
@[noinline] def rotLoop (n : Nat) (m : Mix) : Mix := Id.run do
  let mut m := m
  for i in [0:n] do m := rot m (i % 5 != 4)
  return m

def main (args : List String) : IO Unit := do
  let k := args.length
  let l := L.ofRange (1 + k) (4 + k)
  IO.println s!"selfCycle: {(prependSelf l true).show} len {(prependSelf l true).len}"
  IO.println s!"selfCycle1: {(prependSelf (L.ofRange (42 + k) (43 + k)) true).show}"
  IO.println s!"flip: {(flip (.up (42 + k)) true).code} {(flip (.up (42 + k)) false).code} {(flip (.down (100 + k)) true).code}"
  IO.println s!"flipLoop: {(flipLoop (1000 + k) (.up k)).code}"
  IO.println s!"rot: {(rot (.small (7 + k.toUInt8) 5 "s") true).show} | {(rot (rot (.small 1 2 "x") true) true).show}"
  IO.println s!"rotLoop: {(rotLoop (101 + k) (.wide "a" 3 4)).show}"
  let base := Lst.build (5 + k) .nil
  IO.println s!"mapTy1: {(base.map (· + 1)).sumN}"
  IO.println s!"mapTy2: {((base.map (fun x => (Lst.cons x (Lst.cons x .nil)))).map Lst.sumN).sumN}"
  IO.println s!"mapTy3: {((Lst.build (4 + k) .nil).map (fun x => s!"<{x}>")).map String.length |>.sumN}"
  IO.println s!"lambdaCap: {(addLenToTail (L.ofRange (10 + k) (13 + k)) true).show}"
  IO.println s!"headFromLen: {(headFromLen (L.ofRange (1 + k) (4 + k))).show}"
  let t := mkT k
  IO.println s!"selfSum: {(selfSum (mkT k)).sum} dupLeft: {(dupLeft (mkT k) true).sum} keep: {(dupLeft t true).sum + t.sum}"
  let o : Lst In := .cons (.cons (1 + k) (.cons (2 + k) .nil)) .nil
  IO.println s!"grab: {match grab o with | .pack i s => s + i.sum | .plist l => osum l}"
  let o2 : Lst In := .cons (.cons (1 + k) .nil) (.cons (.cons (2 + k) .nil) .nil)
  IO.println s!"annotate: {osum (annotate o2)}"
  let l3 := L.ofRange (5 + k) (8 + k)
  let (a, b) := bothVersions l3
  IO.println s!"alias: {a.show} {b.show} {(incHead (incHead (incHead (L.ofRange k (2 + k))))).show}"
  let (c, d) := scrutInBranch (L.ofRange (3 + k) (6 + k))
  IO.println s!"scrutBranch: {c.show} {d.show}"
  let xs := List.range (4 + k)
  IO.println s!"updateNth: {updateNth 2 9 xs} {updateNth 9 7 xs} {(updateNth 9 7 xs).length}"
  IO.println s!"condShare: {condShare (mkT k) 0} {condShare (mkT k) 1} sub: {let s := pickSub (mkT k) 0; s.sum + s.sum}"

end RtReuseAlias

def main (args : List String) : IO Unit := RtReuseAlias.main args
