/-! Runtime test: Lean's library initializer `IO.stdGenRef`
(`Init/Data/Random.lean`) runs at startup, before the program's own
initializers, also in a program that never uses random numbers: it reads 8
bytes from `/dev/urandom`. `RtStartupInitUrandom.pipe` runs the program as
is, then with descriptors 0 to 10 only (`ulimit -n 11`): libuv's 8 startup
descriptors take 3 to 10 (RtFdLimit), so opening `/dev/urandom` fails with
`EMFILE`, the error is reported as an uncaught exception (exit 1), and the
program's initializer and `main` do not run. lean2rr ran the library's
initializers only when the program used them, and so ran `main`. -/

initialize IO.println "program initializer"

def main : IO Unit := IO.println "main ran"
