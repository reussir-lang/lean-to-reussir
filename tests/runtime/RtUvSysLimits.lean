import Std.Internal.UV.System
import Std.Internal.UV.DNS
/-! Runtime test: libuv's own checks and the fixed buffers Lean passes in
`Std.Internal.UV.System` and `DNS.getAddrInfo`. `osHomedir` is `HOME` even
when it is empty, `osTmpdir` the first of `TMPDIR`, `TMP`, `TEMP`,
`TEMPDIR` that is set, even empty; a value of `PATH_MAX` (4096) bytes or
more is `ENOBUFS`, and so is a process title of 512 bytes or more;
priorities outside [-20, 19] (after the cut to an `int`), `random` of more
than 0x7FFFFFFF bytes, and an empty host name or one of 256 bytes or more
are rejected at once. `RtUvSysLimits.pipe` runs the program (mode `env`)
under several environments, then with a long argument (room for a long
title). -/
open Std.Internal.UV.System

def tryIO (label : String) (x : IO String) : IO Unit := do
  try IO.println s!"{label}: {← x}" catch e => IO.println s!"{label}: error: {e}"

def brief (s : String) : String := s!"{s.utf8ByteSize} {(s.take 12).copy.quote}"

def title (n : Nat) : IO Unit :=
  tryIO s!"title of {n}" do
    setProcessTitle (String.ofList (List.replicate n 'T'))
    return toString (← getProcessTitle).utf8ByteSize

def hosts : List (String × String) :=
  [("", ""), ("", "80"), (String.ofList (List.replicate 256 'a'), ""),
   (String.ofList (List.replicate 300 '1'), "80")]

def main (args : List String) : IO Unit := do
  tryIO "osHomedir" do return brief (← osHomedir)
  tryIO "osTmpdir" do return brief (← osTmpdir)
  if args == ["env"] then return
  let p ← osGetPriority 0
  for q in ([20, -21, 100, -100, 4294967296 + 25, 4294967296 * 5 - 30] : List Int64) do
    tryIO s!"setPriority {q}" do osSetPriority 0 q; return "ok"
  IO.println s!"priority unchanged {(← osGetPriority 0) == p}"
  title 600
  title 511
  title 512
  tryIO "random 0x80000000" do
    let r ← random 0x80000000
    return s!"started {← IO.hasFinished r.result?}"
  for (h, s) in hosts do
    tryIO s!"getAddrInfo of {h.utf8ByteSize} bytes, service {s.quote}" do
      let r ← Std.Internal.UV.DNS.getAddrInfo h s 0
      return s!"started {← IO.hasFinished r.result?}"
