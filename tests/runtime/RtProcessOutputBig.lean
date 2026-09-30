/-! Runtime test: `IO.Process.output` with a child that fills its stderr
pipe before writing stdout (natively a dedicated task reads stdout while
stderr is read; neither pipe may block the other). -/

def main : IO Unit := do
  let o ← IO.Process.output { cmd := "sh", args := #["-c", "yes b 2>/dev/null | head -c 200000 >&2; yes a 2>/dev/null | head -c 300000; exit 4"] }
  IO.println s!"code {o.exitCode} stdout {o.stdout.length} stderr {o.stderr.length}"
  let o ← IO.Process.output { cmd := "sh", args := #["-c", "printf '\\377' >&2"] }
  IO.println s!"code {o.exitCode}"
