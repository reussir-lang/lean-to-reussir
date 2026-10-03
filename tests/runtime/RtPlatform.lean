/-! Runtime test: the platform and toolchain queries answer as natively:
`System.Platform.target` is the target triple of the Lean toolchain
(`LEAN_PLATFORM_TARGET`, "aarch64-unknown-linux-gnu" on this host, which
the runtime picks by the target it is compiled for), the word size, the
Windows/macOS/Linux/Emscripten flags (`System.Platform.isLinux`, extern
`lean_system_platform_linux`, is new in Lean 4.34), and the version, git
hash and toolchain strings of the toolchain lean2rr is built with. From the
round-9 runtime inventory (fix-r9-misc) and the Lean 4.34 port. -/

def main : IO Unit := do
  IO.println s!"target {System.Platform.target}"
  IO.println s!"numBits {System.Platform.numBits}"
  IO.println s!"windows {System.Platform.isWindows} osx {System.Platform.isOSX} emscripten {System.Platform.isEmscripten}"
  IO.println s!"linux {System.Platform.isLinux} getIsLinux {System.Platform.getIsLinux ()}"
  IO.println s!"version {Lean.versionString} githash {Lean.githash} toolchain {Lean.toolchain}"
  IO.println s!"major {Lean.version.major} minor {Lean.version.minor} patch {Lean.version.patch}"
  IO.println s!"release {Lean.version.isRelease} special '{Lean.version.specialDesc}' stage0 {Lean.Internal.isStage0 ()} llvm {Lean.Internal.hasLLVMBackend ()}"
  -- the queries are also usable in conditions
  if System.Platform.isLinux && !System.Platform.isWindows then IO.println "linux path" else IO.println "other path"
