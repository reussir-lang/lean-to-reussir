/-! Runtime test: a closed term whose evaluation prints (a trace, a panic
message: output lets a task whose sleep is over go first) while another
task needs it: natively the second thread waits for the first
(`lean_obj_once_cold` holds a lock), so the term is evaluated once. -/
def busy (ms : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) - start < ms do
    pure ()

def eStr {α} [ToString α] : Except IO.Error α → String
  | .ok v => toString v
  | .error e => s!"error {e}"

@[noinline] def traced (k : Nat) : Nat := dbgTrace s!"evaluating closed term {k}" fun _ => k * 2
@[noinline] def useTraced (x : Nat) : IO Nat := do return traced 21 + x

@[noinline] def table : Array Nat := #[1, 2, 3]
@[noinline] def usePanicky (x : Nat) : IO Nat := do return table[7]! + x

def main : IO Unit := do
  -- `a` evaluates the term after computing past the time `s` wakes up
  let s ← IO.asTask (do IO.sleep 30; return (← useTraced 2))
  let a ← IO.asTask (do IO.sleep 5; busy 60; return (← useTraced 1))
  IO.sleep 1
  IO.eprintln s!"trace: {eStr (← IO.wait s)} {eStr (← IO.wait a)}"
  let s ← IO.asTask (do IO.sleep 30; return (← usePanicky 2))
  let a ← IO.asTask (do IO.sleep 5; busy 60; return (← usePanicky 1))
  IO.sleep 1
  IO.eprintln s!"panic: {eStr (← IO.wait s)} {eStr (← IO.wait a)}"
