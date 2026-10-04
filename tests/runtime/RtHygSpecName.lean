/-! Runtime test (round 9, RV9S-01): a specialization of a declaration with a hygienic
name. The command macro `gen` defines `helper`, whose real name carries macro scopes
(`helper._@.RtHygSpecName.…._hyg.3`). Lean specializes it inside `runIt` (the `[Monad m]`
instance and the function argument are static) and names the specialization
`helper._@.RtHygSpecName.…._hyg.3._at_.runIt.spec_1`: the macro scopes sit in the middle.

Expected: lean2rr translates the program without a panic (run.sh runs it with
`LEAN_ABORT_ON_PANIC=1`); the executable prints what native does (`visit 1`, `visit 2`,
`visit 3`, `result [10, 20, 30]`).

Was: the executable's output was the same, but lean2rr itself panicked while
translating: it printed `Error: unreachable @ extractMainModule` and a backtrace through
`Lean.Name.append` <- `LeanToReussir.specOrigin?` <- `LeanToReussir.isMapLoop` on stderr
(exit 134 with `LEAN_ABORT_ON_PANIC=1`). `specOrigin?` (Mono.lean) rebuilt the name
before `_at_` with `Name.append`, which reads a right operand ending in `_hyg` as a
hygienic name and found no `_@` marker in the lone component `_hyg`; the origin was also
wrong (`helper.«_@».RtHygSpecName.3`). It now rebuilds the name component by component
(`nameOfComponents`, as round 6's RV6L-04 fix does for startup names). -/

macro "gen" n:ident : command => `(
  def helper {m : Type → Type} [Monad m] (f : Nat → m Nat) (xs : List Nat) : m (List Nat) :=
    xs.mapM f
  def $n (xs : List Nat) : IO (List Nat) :=
    helper (fun x => do IO.println s!"visit {x}"; pure (x * 10)) xs)

gen runIt

def main (args : List String) : IO Unit := do
  let xs := (List.range (3 + args.length)).map (· + 1)
  let r ← runIt xs
  IO.println s!"result {r}"
