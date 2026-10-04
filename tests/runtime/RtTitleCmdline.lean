import Std.Internal.UV.System
/-! Runtime test (lean-runtime's feature `proc-title`, switch step 3): `setProcessTitle` writes the
title over the process's original arguments, as libuv 1.48's `uv_set_process_title` does, so
`/proc/self/cmdline` shows it; a title as long as the arguments' memory or longer is cut to its
length less one byte; the environment after the arguments is not moved; `main`'s `args` stay.
lean-runtime's ELF constructor keeps the arguments' memory: this checks that lean2rr's build links
it into the program. (lean-runtime's case `uvsys/title_cmdline`.) -/
open Std.Internal.UV.System

def main (args : List String) : IO Unit := do
  let before ← IO.FS.readFile "/proc/self/cmdline"
  let environBefore ← IO.FS.readFile "/proc/self/environ"
  IO.println s!"cmdline before holds the argument: {decide ((before.splitOn "abcdefghijklmnop").length > 1)}"
  setProcessTitle "new-title"
  IO.println s!"title: {← getProcessTitle}"
  let c ← IO.FS.readFile "/proc/self/cmdline"
  IO.println s!"cmdline starts with the title: {c.startsWith "new-title"}"
  IO.println s!"then only NUL bytes: {(c.toList.drop 9).all (· == '\x00')}, as long as before: {c.length == before.length}"
  setProcessTitle ("".pushn 'z' (before.length + 5))
  let t ← getProcessTitle
  IO.println s!"a longer title is cut to the memory less one byte: {t.length + 1 == before.length}"
  let c2 ← IO.FS.readFile "/proc/self/cmdline"
  IO.println s!"cmdline is the cut title and one NUL: {c2 == t.push '\x00'}"
  IO.println s!"environment kept: {← IO.getEnv "TITLE_ENV"}"
  IO.println s!"environment's memory unchanged: {(← IO.FS.readFile "/proc/self/environ") == environBefore}"
  IO.println s!"args: {args}"
