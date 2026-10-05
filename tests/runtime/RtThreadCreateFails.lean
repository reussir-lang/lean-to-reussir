/-! Runtime test: `main`'s thread cannot be made. The run (`.pipe`) limits the
address space to about 600 MB, so the 1 GiB stack of the thread `main` runs on
cannot be mapped: natively `lean_run_main` throws `lean::exception("failed to
create thread: " << strerror(err))`, which nothing catches, so libc++ reports it
and aborts (status 134, `main` never runs). lean2rr's runtime writes the same
line (lean-runtime's `sched::thread_create_failed`, with glibc's text of
`pthread_create`'s `EAGAIN`). -/

def main : IO Unit := IO.println "main ran"
