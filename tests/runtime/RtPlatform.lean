/-! Runtime test: the platform and toolchain queries answer as natively:
`System.Platform.target` is the target triple of the Lean toolchain
(`LEAN_PLATFORM_TARGET`, "aarch64-unknown-linux-gnu" on this host, which
the runtime picks by the target it is compiled for), the word size, the
Windows/macOS/Emscripten flags, and the version, git hash and toolchain
strings. From the round-9 runtime inventory (fix-r9-misc). -/

def main : IO Unit := do
  IO.println s!"target {System.Platform.target}"
  IO.println s!"numBits {System.Platform.numBits}"
  IO.println s!"windows {System.Platform.isWindows} osx {System.Platform.isOSX} emscripten {System.Platform.isEmscripten}"
  IO.println s!"version {Lean.versionString} githash {Lean.githash} toolchain {Lean.toolchain}"
  IO.println s!"release {Lean.version.isRelease} special '{Lean.version.specialDesc}' stage0 {Lean.Internal.isStage0 ()} llvm {Lean.Internal.hasLLVMBackend ()}"
