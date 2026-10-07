/-! Runtime test (lean-runtime's review RF14-07): one free drops an array
`#[stdin, p]` (inside an `Option`, released by a reference's `set`).
Natively Lean's free (`lean_del_core`) reaches the array's last element
first: it resolves the promise `p` with `none`, then closes the child's
stdin, whose last byte waits until the child reads its stdin. The child
first writes 70000 bytes to its stdout, which the reader task reads once
the promise is resolved. Natively: "reader got 70000", then "child 0".

lean2rr's free reaches the elements in the same order: the promise's
resolution is put off to the drain's end (`task::defer_promise_drop`), then
the close hands stdin's last byte to a writer thread of lean-runtime. At
the drain's end (`task::drained`) the put-off resolution runs first, and
waits only for the writers of the streams handed off before it
(lean-runtime's `run_deferred`), so the reader reads the child's output
while stdin's writer still waits; then the drain-end hook (`after_drain`)
waits for that writer. With the hook before the resolutions, the context
waited for the writer, which waited for the child, which waited for the
reader, which waited for the promise: the program hung. lean-runtime's case
`process/deferred_resolve_before_handoff`. Needs `sh`, `head`, `cat` and
the default pipe capacity (64 KiB). -/

def main : IO Unit := do
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", "head -c 70000 /dev/zero; cat > /dev/null"],
      stdin := .piped, stdout := .piped }
  let (stdin, child) ← child.takeStdin
  let p ← IO.Promise.new (α := Unit)
  let r := p.result?
  let reader ← IO.asTask do
    let _ ← IO.wait r
    let out ← child.stdout.readToEnd
    return out.length
  -- the reader runs and blocks on the promise
  IO.sleep 50
  stdin.write (ByteArray.mk (Array.replicate 65536 120))
  stdin.flush
  stdin.putStr "x"
  let cell ← IO.mkRef (some #[Sum.inl stdin, Sum.inr p] :
    Option (Array (Sum IO.FS.Handle (IO.Promise Unit))))
  cell.set none
  match ← IO.wait reader with
  | .ok n => IO.println s!"reader got {n}"
  | .error e => IO.println s!"reader error {e}"
  let st ← child.wait
  IO.println s!"child {st}"
