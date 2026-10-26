/-! Runtime test of the optimization `unreached-decls` (Opt/UnreachedDecls):
after Stage 2 the declarations that no code reaches from the roots (`main`,
the error printer, every startup step, the `IO.Error` builders) are not
translated. Lean's passes leave such declarations here: the instances that
specialization replaced (`List.foldl` at `main`) and the callees they
inlined. Each part below runs only through a reference that a walk of
`main`'s calls alone would miss, and prints, so a part left out wrongly
shows as a missing line or as a failed build:
- `noisyInit` is called only by the initializer of `counter` (a startup
  step), and prints at startup;
- an `initialize` action prints and registers `reportHook` in a reference;
  `reportHook` is named only there, as a function value, and `main` applies
  what the reference holds;
- `seed` is read only by the instance `Inhabited Cfg`, which `main` reaches
  through `default`;
- `triple` and `negate` are only function values in the constant `ops`,
  applied at an index from the command line (Lean cannot fold the call);
- `IO.FS.createDir` fails on a directory that exists: the lowering calls
  the `IO.Error` builder of that error by name, and no code names it. -/

def noisyInit : IO Nat := do
  IO.println "noisyInit runs at startup"
  pure 7

initialize counter : IO.Ref Nat ← do
  let n ← noisyInit
  IO.mkRef n

initialize hooks : IO.Ref (Array (Nat → IO Unit)) ← IO.mkRef #[]

def reportHook (n : Nat) : IO Unit :=
  IO.println s!"reportHook got {n}"

initialize do
  IO.println "the initialize action runs"
  counter.modify (· + 1)
  hooks.modify (·.push reportHook)

structure Cfg where
  size : Nat
  name : String

def seed : Nat := (List.range 10).foldl (· + ·) 0

instance : Inhabited Cfg := ⟨{ size := seed, name := "dflt" }⟩

def triple (n : Nat) : Nat := 3 * n
def negate (n : Nat) : Nat := 100 - n

def ops : Array (Nat → Nat) := #[triple, negate]

def main (args : List String) : IO Unit := do
  IO.println s!"counter: {← counter.get}"
  for h in ← hooks.get do h args.length
  let c : Cfg := default
  IO.println s!"cfg: {c.size} {c.name}"
  for a in args do
    let i := a.toNat! % ops.size
    IO.println s!"op {i} of {a.toNat!}: {ops[i]! a.toNat!}"
  try
    IO.FS.createDir "."
  catch e => IO.println s!"caught: {e}"
