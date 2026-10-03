import Std.Internal.UV
open Std.Internal.UV Std.Net

/-! Runtime test: how IO errors are decoded, as Lean 4.34's runtime does
(`decode_uv_error_impl` in io.cpp, mirrored by runtime/leanrt/src/fs.rs and
lean2rr/L2RShim.lean). Since 4.34:
- an errno error (`decode_io_error`) has libuv's message for the errno, not
  `strerror`'s: a directory opened as a file is "illegal operation on a
  directory" (4.33: "is a directory"), an existing directory "file already
  exists" (4.33: "file exists");
- an error of a libuv call (`decode_uv_error`: `removeFile`, `metadata`,
  `hardLink`, `UV.System.chdir`, sockets) stores the positive errno as its
  code: 2 for ENOENT (4.33: 4294967294, libuv's negated code), 111 for
  ECONNREFUSED.
Each error is printed raw (constructor, code, details, file) and as
`toString` shows it. EBADMSG (now a protocol error) and errnos libuv has no
name for are not reachable portably here; leanrt's unit test fs_tests.rs
checks every errno against native Lean. -/

def raw : IO.Error → String
  | .otherError c d => s!"otherError {c} {repr d}"
  | .interrupted f c d => s!"interrupted {repr f} {c} {repr d}"
  | .invalidArgument f c d => s!"invalidArgument {repr f} {c} {repr d}"
  | .noFileOrDirectory f c d => s!"noFileOrDirectory {repr f} {c} {repr d}"
  | .permissionDenied f c d => s!"permissionDenied {repr f} {c} {repr d}"
  | .resourceExhausted f c d => s!"resourceExhausted {repr f} {c} {repr d}"
  | .inappropriateType f c d => s!"inappropriateType {repr f} {c} {repr d}"
  | .noSuchThing f c d => s!"noSuchThing {repr f} {c} {repr d}"
  | .alreadyExists f c d => s!"alreadyExists {repr f} {c} {repr d}"
  | .hardwareFault c d => s!"hardwareFault {c} {repr d}"
  | .unsatisfiedConstraints c d => s!"unsatisfiedConstraints {c} {repr d}"
  | .illegalOperation c d => s!"illegalOperation {c} {repr d}"
  | .resourceVanished c d => s!"resourceVanished {c} {repr d}"
  | .protocolError c d => s!"protocolError {c} {repr d}"
  | .timeExpired c d => s!"timeExpired {c} {repr d}"
  | .resourceBusy c d => s!"resourceBusy {c} {repr d}"
  | .unsupportedOperation c d => s!"unsupportedOperation {c} {repr d}"
  | .userError m => s!"userError {repr m}"
  | .unexpectedEof => "unexpectedEof"

def tryIO (label : String) (act : IO Unit) : IO Unit := do
  try
    act
    IO.println s!"{label}: ok"
  catch e =>
    IO.println s!"{label}: {raw e}"
    IO.println s!"  {e}"

def awaitUnit (p : IO.Promise (Except IO.Error Unit)) : IO Unit := do
  match ← IO.wait p.result! with
  | .ok () => pure ()
  | .error e => throw e

def main : IO Unit := do
  let dir : System.FilePath := "rt-ioerr-tmp"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDir dir
  IO.FS.writeFile (dir / "file") "x"
  IO.FS.createDir (dir / "sub")
  IO.FS.writeFile (dir / "sub" / "inner") "y"
  -- errno errors (`decode_io_error`)
  tryIO "open a directory for writing" (discard <| IO.FS.Handle.mk dir .write)
  tryIO "read a directory as a file" (discard <| IO.FS.readFile dir)
  tryIO "open under a file" (discard <| IO.FS.Handle.mk (dir / "file" / "x") .read)
  tryIO "open a missing file" (discard <| IO.FS.Handle.mk (dir / "missing") .read)
  tryIO "create an existing directory" (IO.FS.createDir (dir / "sub"))
  tryIO "remove a non-empty directory" (IO.FS.removeDir (dir / "sub"))
  tryIO "remove a missing directory" (IO.FS.removeDir (dir / "missing"))
  tryIO "rename a missing file" (IO.FS.rename (dir / "missing") (dir / "other"))
  tryIO "realPath of a missing file" (discard <| IO.FS.realPath (dir / "missing"))
  -- libuv errors (`decode_uv_error`)
  tryIO "removeFile of a missing file" (IO.FS.removeFile (dir / "missing"))
  tryIO "removeFile of a directory" (IO.FS.removeFile (dir / "sub"))
  tryIO "metadata of a missing file" (discard <| (dir / "missing").metadata)
  tryIO "symlinkMetadata of a missing file" (discard <| (dir / "missing").symlinkMetadata)
  tryIO "hardLink of a missing file" (IO.FS.hardLink (dir / "missing") (dir / "link"))
  tryIO "hardLink onto an existing file" (IO.FS.hardLink (dir / "file") (dir / "sub" / "inner"))
  tryIO "UV.System.chdir to a missing directory" (Std.Internal.UV.System.chdir (dir / "missing").toString)
  tryIO "TCP connect refused" do
    -- a port that was just free: bound, then closed without listening
    let s ← TCP.Socket.new
    s.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
    let port := (← s.getSockName).port
    let c ← TCP.Socket.new
    awaitUnit (← c.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, port⟩))
  IO.FS.removeDirAll dir
