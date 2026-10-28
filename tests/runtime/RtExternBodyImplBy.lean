/-!
The Lean definition of an `@[extern]` of the program (lean2rr runs it,
translation plan §5.8) calls functions whose `@[implemented_by]`
implementation is type-unsafe (it uses `unsafeCast`): directly (`ext`), as
a function value (`extMap`), polymorphic (`extG`), and `Array.mapM`, whose
implementation `Array.mapMUnsafe` casts too (`extMapM`). Lean replaces
every call by the implementation, so natively the `@[export]` copies of
the same bodies that the C side (`RtExternBodyImplBy.ffi.c`) calls give
`ext 101 [101, 102] 1002`. lean2rr compiles the extern's definition from
source (`Mono.recompilePasses`), whose `implemented_by` replacement kept a
call when the implementation was type-unsafe, a leftover of the
`safeSources` option: `f`'s own definition ran, `ext 2 [2, 3] 2`, and
`Array.mapM` its reference definition (a new array, not in place). A bug
hunt of the extern routing (repro R1). Also: polymorphic externs of the
program with Lean definitions at several types, as function values,
partially applied, with class parameters.
-/

unsafe def fImpl (n : Nat) : Nat := (unsafeCast n : Nat) + 100
@[implemented_by fImpl] def f (n : Nat) : Nat := n + 1

unsafe def gImpl {α : Type} (xs : List α) : Nat := (unsafeCast xs.length : Nat) + 1000
@[implemented_by gImpl] def g {α : Type} (xs : List α) : Nat := xs.length

@[extern "rt_eib_ext"] def ext (n : Nat) : Nat := f n
@[extern "rt_eib_ext_map"] def extMap (xs : List Nat) : List Nat := xs.map f
@[extern "rt_eib_ext_g"] def extG (xs : List String) : Nat := g xs
@[extern "rt_eib_mapm"] def extMapM (a : Array Nat) : Array Nat := Id.run (a.mapM fun x => pure (x + 1))

-- The same bodies, compiled by Lean (the C side calls them).
@[export rt_eib_ref] def extRef (n : Nat) : Nat := f n
@[export rt_eib_ref_map] def extMapRef (xs : List Nat) : List Nat := xs.map f
@[export rt_eib_ref_g] def extGRef (xs : List String) : Nat := g xs
@[export rt_eib_ref_mapm] def extMapMRef (a : Array Nat) : Array Nat := Id.run (a.mapM fun x => pure (x + 1))

@[extern "rt_eib_pick"] def pick {α : Type} (b : Bool) (x y : α) : α := if b then y else x
@[extern "rt_eib_sum"] def sumL {α : Type} [Add α] [OfNat α 0] (xs : @& List α) : α := xs.foldl (· + ·) 0

def main : IO Unit := do
  IO.println s!"direct {f 1} {g ["a", "b"]}"
  IO.println s!"ext {ext 1} {extMap [1, 2]} {extG ["a", "b"]}"
  IO.println s!"mapM {extMapM #[1, 2, 3]}"
  IO.println s!"pick {pick true 1 2} {pick false (3 : UInt64) 4} {pick true "a" "b"} {(pick false (· + 1) (· * 10) : Nat → Nat) 5}"
  let p := pick (α := String) false
  IO.println s!"partial {p "x" "y"} {List.zipWith (pick true) [1, 2, 3] [10, 20, 30]} {[true, false].map (pick · (7 : UInt8) 8)}"
  IO.println s!"sum {sumL [1, 2, 3]} {sumL [(1.5 : Float), 2.25]} {sumL ([] : List Int)} {sumL [(250 : UInt8), 10]}"
  IO.println s!"sumF {[[1, 2], [3]].map sumL} {(sumL : List UInt64 → UInt64) [5, 6]}"
