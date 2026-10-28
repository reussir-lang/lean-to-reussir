/-!
Two calls of a polymorphic `@[extern]` of the program, at `Option Nat` and
at `Option String`, with the same value argument in one function (`both`).
Natively Lean's mono `cse` merges them (type arguments erased): the C side
(`RtExternBodyMerge.ffi.c`), which prints what the Lean definition's
`dbgTrace` prints, runs once per call of `both`. lean2rr runs the extern's
Lean definition (translation plan §5.8); Stage 1's search for such calls
(`Mono.erasedMerges`) left out every extern, as if it computed nothing
observable, so the two calls kept two instances and the trace printed
twice. Now an extern of the program counts as a definition. A bug hunt of
the extern routing (repro R3b).
-/

@[extern "rt_ebm_mke"] def mkE {α : Type} (n : Nat) : Option α := dbgTrace s!"mkE {n}" fun _ => none

@[noinline] def both (k : Nat) : String :=
  let a : Option Nat := mkE k
  let b : Option String := mkE k
  s!"{a.isSome} {b.isSome}"

def main (args : List String) : IO Unit := do
  let k := args.length
  IO.println (both k)
  IO.println (both (k + 1))
