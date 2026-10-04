/-! Runtime test: limits of Lean 4.34.0's runtime that lean2rr lifts where
the result can be computed, as lean-runtime's rules do (translation plan
§10, "Lean bugs we do not reproduce"; lean-runtime's docs/lean-bugs.md):
- LB-06: `ByteArray.copySlice` with an offset or a length of 2^64 or more
  gives the Lean definition's result, where `lean_nat_to_size_t` ends with
  `INTERNAL PANIC: out of memory`;
- LB-11: `Nat.pow` with an exponent of 2^32 or more: `1 ^ e = 1` and
  `0 ^ e = 0`, where native ends with `INTERNAL PANIC: Nat.pow exponent is
  too big` (also RtInternalPanic);
- LB-05: a power above GMP's limb cap, `(2^62)^(2^32 - 1)`, ends at once
  with `INTERNAL PANIC: out of memory`, exit 1, where native's GMP raises
  SIGFPE (status 136, buffered output lost).
As natively on both sides: `3 ^ (2^40)`, whose result is above the limit
too, ends with `Nat.pow exponent is too big` (stdout flushed after it), and
`0 <<< 2^64` is 0. The `.pipe` runs one case per process; lean2rr's output
differs from native's by design, so each is compared with its own file
(RtLiftedLimits.l2r.out, RtLiftedLimits.native.out). LB-04 and LB-12 need
an operand or a result of 2^32 bits (512 MiB): lean-runtime's rows check
them through lean2rr (tests/runtime/rows-check.sh). -/

def main (args : List String) : IO Unit := do
  -- 0, at run time: the case name is the only argument
  let k := args.length - 1
  let big : Nat := 2 ^ 64 + k
  match args[0]! with
  | "copySlice" =>
    let src := ByteArray.mk #[1, 2, 3, 4, 5]
    let dst := ByteArray.mk #[10, 11, 12]
    IO.println s!"{(src.copySlice big dst 0 2).toList} {(src.copySlice 1 dst big 2).toList} {(src.copySlice 1 dst 0 big).toList} {(src.copySlice 0 dst 1 big false).toList}"
  | "pow" =>
    IO.println s!"{(1 : Nat) ^ (2 ^ 32 + k)} {(0 : Nat) ^ (2 ^ 32 + k)} {(1 : Nat) ^ big} {(0 : Nat) ^ big} {(0 : Nat) <<< big}"
  | "powTooBig" =>
    IO.println "start"
    IO.println s!"{Nat.log2 ((2 ^ 62 + k) ^ (2 ^ 32 - 1))}"
  | "powExponent" =>
    IO.println "start"
    IO.println s!"{Nat.log2 ((3 + k) ^ (2 ^ 40))}"
  | _ => IO.println "unknown case"
