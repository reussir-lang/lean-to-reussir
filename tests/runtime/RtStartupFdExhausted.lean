/-! Runtime test: startup with too few descriptors for libuv's event loop (LB-30, LB-31 in
lean-runtime's docs/lean-bugs.md; switch step 3). Lean starts libuv's default loop before any
module code; libuv opens, at the lowest free numbers, an epoll descriptor, two io_uring rings
(where the kernel gives them), the signal lock pipe, the loop's signal pipe and an eventfd. The
`.pipe` runs the program under `ulimit -n` 6, 9 and 10, then 5 and 7 with `UV_USE_IO_URING=0`.
Natively 6 and 5 leave no room for the signal lock pipe and libuv aborts (134, LB-31); 9, 10 and 7
leave room for it but not for the loop, and Lean uses libuv's NULL loop (SIGSEGV, 139, LB-30).
lean2rr's startup glue ends each with lean-runtime's `INTERNAL PANIC: Failed to initialize event
loop: too many open files`, status 1 (expectation files `RtStartupFdExhausted.native.out` and
`.l2r.out`). `main` is never reached. Host-dependent as `RtFdLimit` (io_uring rings). The
program's stderr goes to stdout, and bash's report of a death by a signal (with a pid) is
dropped. (lean-runtime's case `io/startup_fd_exhausted`.) -/
def main : IO Unit := do
  let entries ← System.FilePath.readDir "/proc/self/fd"
  let mut fds : Array Nat := #[]
  for e in entries do
    if let some n := e.fileName.toNat? then fds := fds.push n
  IO.println s!"main: open {fds.qsort (· < ·)}"
