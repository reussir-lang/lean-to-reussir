/-! Runtime test: a value read through `unsafeCast` as another inductive
whose constructors correspond to its own by position (a view, Lower's
`castCases`), where a constructor of the target reads fewer fields than
the corresponding constructor of the value's own type holds (translation
plan §5.5: a constructor without fields of the target is selected whatever
the source constructor at that tag holds). The `match` is on the value's
own type, so each arm's pattern binds every field of the source
constructor's record; the fields the target does not read are `_`. Found
by the layout hunt (2026-10-26): the patterns had the target's number of
fields, and rrc refused each of these programs.
- `Nullary`: `S.a` has a field, `T.a` none, and the `.a` arm returns the
  matched value itself, which `nullary-scrutinee` rebuilds only when the
  source constructor has no fields either;
- `Extra`: `T.b` reads the first of `S.b`'s two fields;
- `Lazy`: `T.a` reads the first of `S.a`'s two fields, and the arm stores
  the matched value before it uses the field, so `lazy-fields` matches the
  value again in an inner alternative (the same pattern);
- `Exc`: an `Except String Nat` read as `R`, whose `bad` has no fields;
- `Opt`: an `Option Nat` read as a two-constructor enumeration. Natively
  `some`'s object is read through the bits of its address (`lean_unbox`),
  so for it only a result that holds for every address is printed (as
  RtCastBox's `A`); `none` is `lean_box(0)`, the first constructor;
- `Rev` (the fix's review): `S.a` holds a string and an array and `S.b` a
  handle and a number that `T` does not read; a view in IO (`score`) of a
  value still used afterwards, so natively its cell is released later with
  `S`'s own layout and the handle is closed (its text flushed) when `tagS`
  is done with the value; a view inside a `for` loop followed by more code
  (a join point); a view in a self tail-recursive walk over a list of
  both constructors; and a structure read as a one-field inductive that
  Lean keeps as an object (the `.struct` path). A value matched through a
  view while it is unique is RtCastViewUnique (a documented difference). -/

namespace Nullary
inductive S where
  | a (x : Nat)
  | b (y : Nat)
  deriving Repr

inductive T where
  | a
  | b (y : Nat)

@[inline] def step (t : T) : T :=
  match (generalizing := false) t with
  | .a => t
  | .b y => .b (y + 1)

unsafe def runImpl (s : S) : S :=
  unsafeCast (step (unsafeCast s : T))

@[implemented_by runImpl] def run (s : S) : S := s
end Nullary

namespace Extra
inductive S where
  | a
  | b (u : Nat) (v : Nat)

inductive T where
  | a
  | b (y : Nat)

@[inline] def weigh (t : T) : Nat :=
  match t with
  | .a => 0
  | .b y => y + 1

unsafe def runImpl (s : S) : Nat := weigh (unsafeCast s : T)

@[implemented_by runImpl] def run (_ : S) : Nat := 0
end Extra

namespace Lazy
inductive S where
  | a (x : Nat) (z : String)
  | b

inductive T where
  | a (x : Nat)
  | b

@[noinline] def keep (t : T) (k : Nat) : T × Nat := (t, k)

@[inline] def pick (t : T) (k : Nat) : Nat × (T × Nat) :=
  match (generalizing := false) t with
  | .a x =>
    let p := keep t k
    if x > k then (x - k, p) else (k - x, p)
  | .b => (0, keep t k)

unsafe def runImpl (s : S) (k : Nat) : Nat × Nat :=
  let (n, p) := pick (unsafeCast s : T) k
  (n, p.2)

@[implemented_by runImpl] def run (_ : S) (k : Nat) : Nat × Nat := (0, k)
end Lazy

namespace Exc
inductive R where
  | bad
  | good (n : Nat)

@[noinline] unsafe def score (e : Except String Nat) : Nat :=
  match (unsafeCast e : R) with
  | .bad => 1000
  | .good n => n * 2
end Exc

namespace Opt
inductive E where
  | n
  | s

@[noinline] unsafe def tag (o : Option Nat) : String :=
  match (unsafeCast o : E) with
  | .n => "n"
  | .s => "s"
end Opt

namespace Rev
inductive S where
  | a (n : Nat) (s : String) (arr : Array Nat)
  | b (r : IO.Ref Nat) (h : IO.FS.Handle) (k : Nat)

inductive T where
  | a (n : Nat)
  | b (r : IO.Ref Nat)

@[inline] def scoreT (t : T) : IO Nat :=
  match t with
  | .a n => pure (n + 1)
  | .b r => r.get

unsafe def scoreImpl (s : S) : IO Nat := scoreT (unsafeCast s : T)
@[implemented_by scoreImpl] opaque score (s : S) : IO Nat

@[inline] def pureT (t : T) : Nat :=
  match t with
  | .a n => n
  | .b _ => 0

@[noinline] def mkA (i : Nat) : S := S.a i (toString i ++ "xyz") #[i, i + 1, i + 2]
@[noinline] def mkB (r : IO.Ref Nat) (h : IO.FS.Handle) (k : Nat) : S := S.b r h k
@[noinline] def tagS : S → Nat
  | .a n _ _ => n
  | .b _ _ k => k

unsafe def loopImpl (gen : Nat → S) (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    let s := gen i
    let v := pureT (unsafeCast s : T)
    acc := if v % 3 == 0 then acc + v else acc + 1
  return acc
@[implemented_by loopImpl] opaque loop (gen : Nat → S) (n : Nat) : Nat

unsafe def walkImpl : List S → Nat → Nat
  | [], acc => acc
  | s :: rest, acc =>
    match (unsafeCast s : T) with
    | .a n => walkImpl rest (acc + n)
    | .b _ => walkImpl rest (acc + 1000)
@[implemented_by walkImpl] opaque walk (xs : List S) (acc : Nat) : Nat

structure S2 where
  n : Nat
  s : String
  arr : Array Nat

-- a one-field inductive that Lean does not erase to its field (a mutual block)
mutual
inductive TW where
  | mk (n : Nat)
inductive TWdummy where
  | d (w : TW) (x : Option TWdummy)
end

unsafe def s2Impl (x : S2) : Nat :=
  match (unsafeCast x : TW) with
  | .mk n => n * 10
@[implemented_by s2Impl] opaque s2 (x : S2) : Nat
end Rev

unsafe def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println (repr (Nullary.run (.a (5 + k))))
  IO.println (repr (Nullary.run (.b (7 + k))))
  IO.println s!"{Extra.run (.b (10 + k) (20 + k))} {Extra.run .a}"
  IO.println s!"{Lazy.run (.a (9 + k) "zz") 4} {Lazy.run (.a (2 + k) "zz") 4} {Lazy.run .b (3 + k)}"
  IO.println s!"{Exc.score (.ok (21 + k))} {Exc.score (.error s!"no {k}")}"
  let t := Opt.tag (some (5 + k))
  IO.println s!"{Opt.tag none} {t == "n" || t == "s"}"
  let r ← IO.mkRef (41 + k)
  let h ← IO.FS.Handle.mk "RtCastViewFewer.out1" .write
  h.putStr "flushed-on-release"
  let v := Rev.mkB r h 3
  let x ← Rev.score v
  IO.println (Rev.tagS v)
  IO.println s!"shared {x} [{← IO.FS.readFile "RtCastViewFewer.out1"}]"
  IO.println (← Rev.score (Rev.mkA (7 + k)))
  IO.println (Rev.loop Rev.mkA (1000 + k))
  let r2 ← IO.mkRef 5
  let h2 ← IO.FS.Handle.mk "RtCastViewFewer.out2" .write
  IO.println (Rev.walk [Rev.mkA 1, Rev.mkB r2 h2 9, Rev.mkA (2 + k)] 0)
  IO.println (Rev.s2 { n := 4 + k, s := "four", arr := #[4, 4] })
  IO.println (← r.get, ← r2.get)
