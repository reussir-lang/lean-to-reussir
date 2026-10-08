/-! Runtime test: freed huge blocks go back to the OS. Reussir's runtime
builds mimalloc v2.2.4, whose delayed arena purges do not run: its
`mi_arenas_try_purge` (`src/arena.c`, line 624) tests the purge time the
wrong way round. A huge block (more than 16 MiB) or a whole segment, once
freed, stayed in the process until it was used again. On the mimalloc
versions with that test (v2.1.8 to v2.2.7), leanrt sets mimalloc's
`arena_purge_mult` to 0 at startup (`alloc::purge_arenas_at_once`), so the
arena purges such a range when it is freed.
Arguments: MODE N ROUNDS CAP, MODE one of `same`, `grow` (default: both,
N = 1000, ROUNDS = 2, CAP = 16). Each round makes a `ByteArray` with room
for CAP bytes, pushes bytes onto it (leanrt doubles a full block, so with
CAP above 16 MiB every growth frees a huge block), sums them and drops it.
Round r has N bytes (`same`) or (r + 1) * N bytes (`grow`). A smaller CAP
puts the first blocks inside segments, whose purges keep a delay of
10 ms, and the peak then varies from run to run. The output is checked
here; the peak memory by tests/runtime/alloc-check.sh (RtArenaPurge.alloc),
which runs each mode at two sizes. -/

@[noinline] def build (n seed cap : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity cap
  for i in [0:n] do
    b := b.push (i + seed).toUInt8
  return b

@[noinline] def sum (b : ByteArray) : Nat := b.foldl (fun s x => s + x.toNat) 0

def run (mode : String) (n rounds cap : Nat) : IO Unit := do
  let mut tot := 0
  for r in [0:rounds] do
    let m ← match mode with
      | "same" => pure n
      | "grow" => pure ((r + 1) * n)
      | _ => throw (IO.userError s!"unknown mode {mode}")
    tot := tot + sum (build m r cap)
  IO.println s!"{mode} {n} {rounds}: {tot}"

def main (args : List String) : IO Unit := do
  match args with
  | [mode, n, rounds, cap] => run mode n.toNat! rounds.toNat! cap.toNat!
  | _ =>
    run "same" 1000 2 16
    run "grow" 1000 2 16
