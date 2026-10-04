/-! Runtime test: a value that is fresh on some calls and shared on one reaches
an update that rebuilds it in place when it is unique (the Lean form of the
shape of Reussir bug 28, reussir-bugs/28-unique-carrying-join.md). A
self-recursive function's argument is sometimes a field of a value the caller
still holds, a global constant (a structure and a list), an element of an
array, a reference's contents, a value captured by a closure, a forced
thunk's value; also the same value passed twice, a for loop whose accumulator
is replaced by a shared list, and mutual recursion. Every holder must still
see the old value.
A coverage test from Crane's test corpus (Bloomberg's Rocq-to-C++ extractor,
whose regression tests document shapes that broke a typed, reference-counted
code generator); the code is new, the shapes are those of Crane's
tests/regression/fix_shared_ptr_field, mem_safety_probe18,
mem_safety_probe23, shared_uptr_escape, reuse_alias,
loopify_variant_self_assign, loopify_tail_ptr_alias, reuse_use_after_move.
From the round-9 review, area crane (rv9/crane), program CrUniq. -/

namespace RtSharedOnOnePath

structure B where
  v : Nat
  tag : String
  deriving Inhabited
structure P where
  b : B
  n : Nat

@[noinline] def bump (b : B) : B := { b with v := b.v + 100 }
@[noinline] def bumpL : List Nat → List Nat | x :: r => (x + 100) :: r | [] => []

-- a field of a value the caller still holds
@[noinline] def pick (a : B) (p : P) (n : Nat) : B := if n == 2 then p.b else a
def loopF (x : B) (p : P) : Nat → B
  | 0 => x
  | n + 1 => loopF (pick (bump x) p (n + 1)) p n

-- a global constant
def gB : B := ⟨1, "global"⟩
def gL : List Nat := [1, 2, 3]
@[noinline] def pickG (a : B) (n : Nat) : B := if n == 2 then gB else a
def loopG (x : B) : Nat → B
  | 0 => x
  | n + 1 => loopG (pickG (bump x) (n + 1)) n
@[noinline] def pickGL (a : List Nat) (n : Nat) : List Nat := if n == 3 then gL else a
def loopGL (x : List Nat) : Nat → List Nat
  | 0 => x
  | n + 1 => loopGL (pickGL (bumpL x) (n + 1)) n

-- an element of an array that is still used
def loopA (arr : Array B) (x : B) : Nat → B
  | 0 => x
  | n + 1 => loopA arr (if n == 1 then arr[0]! else bump x) n

-- the contents of a reference
def loopR (r : IO.Ref B) (x : B) : Nat → IO B
  | 0 => pure x
  | n + 1 => do
    let y ← if n == 2 then r.get else pure (bump x)
    loopR r y n

-- a value captured by a closure that is called afterwards
def loopC (f : Unit → B) (x : B) : Nat → B
  | 0 => x
  | n + 1 => loopC f (if n == 1 then f () else bump x) n
@[noinline] def mkCap (b : B) : Unit → B := fun _ => b

-- a forced thunk's value
def loopT (t : Thunk B) (x : B) : Nat → B
  | 0 => x
  | n + 1 => loopT t (if n == 2 then t.get else bump x) n

-- the same value twice
@[noinline] def both (a b : B) : B × B := (bump a, bump b)
@[noinline] def twice (l : List Nat) : List Nat × List Nat := (bumpL l, bumpL l)

-- a for loop whose accumulator is replaced by a shared value on one iteration
@[noinline] def forShared (keep : List Nat) (n : Nat) : List Nat := Id.run do
  let mut acc := [0, 0]
  for i in [0:n] do
    acc := if i == 3 then keep else bumpL acc
  return acc

-- mutual recursion carrying the value
mutual
def mA (p : P) (x : B) : Nat → B
  | 0 => x
  | n + 1 => mB p (if n == 3 then p.b else bump x) n
def mB (p : P) (x : B) : Nat → B
  | 0 => x
  | n + 1 => mA p (bump x) n
end

def main (args : List String) : IO Unit := do
  let k := args.length
  let p : P := ⟨⟨1 + k, "held"⟩, 7⟩
  let r := loopF ⟨5, "fresh"⟩ p 3
  IO.println s!"field: {r.v} {r.tag} | holder {p.b.v} {p.b.tag}"
  let g := loopG ⟨5 + k, "fresh"⟩ 3
  IO.println s!"global: {g.v} | gB {gB.v} {gB.tag}"
  let gl := loopGL [5 + k, 6] 4
  IO.println s!"globalList: {gl} | gL {gL}"
  let arr : Array B := #[⟨10 + k, "a0"⟩, ⟨20, "a1"⟩]
  let ra := loopA arr ⟨1, "x"⟩ 3
  IO.println s!"array: {ra.v} | arr {arr.map (·.v)}"
  let ref ← IO.mkRef (B.mk (30 + k) "ref")
  let rr ← loopR ref ⟨1, "x"⟩ 4
  IO.println s!"ref: {rr.v} | ref {(← ref.get).v}"
  let held := B.mk (40 + k) "cap"
  let f := mkCap held
  let rc := loopC f ⟨1, "x"⟩ 3
  IO.println s!"closure: {rc.v} | f {(f ()).v} held {held.v}"
  let t : Thunk B := Thunk.mk fun _ => ⟨50 + k, "thunk"⟩
  let rt := loopT t ⟨1, "x"⟩ 4
  IO.println s!"thunk: {rt.v} | t {t.get.v}"
  let one := B.mk (60 + k) "one"
  let (a, b) := both one one
  IO.println s!"sameTwice: {a.v} {b.v} | {one.v}"
  let l := [70 + k, 1]
  let (l1, l2) := twice l
  IO.println s!"listTwice: {l1} {l2} | {l}"
  let keep := [80 + k, 2]
  IO.println s!"forShared: {forShared keep 6} | keep {keep}"
  let pm : P := ⟨⟨90 + k, "m"⟩, 1⟩
  let rm := mA pm ⟨1, "x"⟩ 6
  IO.println s!"mutual: {rm.v} | holder {pm.b.v}"

end RtSharedOnOnePath

def main (args : List String) : IO Unit := RtSharedOnOnePath.main args
