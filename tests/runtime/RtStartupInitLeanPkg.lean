prelude
import Init.System.IO
import Lean.Data.LBool

/-! Runtime test: a program that imports a module of the `Lean` package
natively calls `lean_initialize()` before anything else, which initializes
all of `Init` and `Std`, here `IO.stdGenRef` too, although this `prelude`
program's imports do not reach `Init.Data.Random`; lean2rr ran nothing
(review RSG-02). `RtStartupInitLeanPkg.pipe` runs the program as is, then
with descriptors 0 to 10 only, where opening `/dev/urandom` fails. Natively
the error escapes `lean_initialize()` as a C++ exception and the program
aborts (`libc++abi: terminating …`, status 134); lean2rr reports it as an
uncaught exception (exit 1): an intended difference (plan §10, review
RSG-03), hence the `.native.*` and `.l2r.*` expectation files. -/

def main : IO Unit := IO.println "main ran"
