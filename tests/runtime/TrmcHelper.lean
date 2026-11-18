/-
The program of tests/runtime/trmc-helper-check.sh (not a runtime test: its
name does not start with `Rt`). A self call whose result goes into a
constructor that the function returns.

`boxNat`, `boxFloat`, `boxStruct`: the only work after the self call is the
box of the element (a `Nat`, a `Float`, a structure). lean2rr binds the box
before the self call, and Reussir must make the loop (a `.trmc` helper).

`callApp`, `callFn`: a traced call is written after the self call. It must
run after the recursion, so Reussir must make no loop.
-/

structure P where
  a : Nat
  b : String

@[noinline] def boxNat : List Nat → List Nat
  | [] => []
  | x :: xs => (x + 1) :: boxNat xs

@[noinline] def boxFloat : List Float → List Float
  | [] => []
  | x :: xs => (x / 2.0) :: boxFloat xs

@[noinline] def boxStruct : List Nat → List P
  | [] => []
  | x :: xs => { a := x, b := toString x } :: boxStruct xs

@[noinline] def callApp : List (Nat → Nat) → List Nat
  | [] => []
  | g :: xs =>
    let rest := callApp xs
    g 1 :: rest

@[noinline] def tr (i : Nat) : Nat :=
  dbgTrace s!"t{i}" fun _ => i + 1

@[noinline] def callFn : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let rest := callFn xs
    tr x :: rest

def main : IO Unit := do
  let l := List.range 4
  IO.println (boxNat l)
  IO.println (boxFloat (l.map Nat.toFloat))
  IO.println ((boxStruct l).map (·.b))
  IO.println (callApp (l.map fun i => fun x => dbgTrace s!"g{i}" fun _ => x + i))
  IO.println (callFn l)
