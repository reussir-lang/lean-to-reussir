import Std.Internal.UV
/-! Runtime test: starting a signal watcher opens no descriptor (natively
libuv's loop has its signal pipe since startup), so the descriptors the
program opens later have native's numbers. -/
open Std.Internal.UV

def fds : IO (Array Nat) := do
  let es ← System.FilePath.readDir "/proc/self/fd"
  return (es.map fun e => e.fileName.toNat!).qsort (· < ·)

def main : IO Unit := do
  let before ← fds
  let s ← Signal.mk 10 false
  let _p ← s.next
  IO.println s!"new descriptors while watching: {(← fds).filter (!before.contains ·)}"
  let h ← IO.FS.Handle.mk "/dev/null" .read
  IO.println s!"new descriptors after an open: {(← fds).filter (!before.contains ·)}"
  s.stop
  IO.println s!"new descriptors after stop: {(← fds).filter (!before.contains ·)}"
  IO.println s!"the file is a terminal: {← h.isTty}"
