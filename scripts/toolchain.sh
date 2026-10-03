# Sourced (bash) by the test runners: puts the Lean toolchain that lean2rr is
# pinned to first on PATH, so `lean`, `leanc` and `lake` are that toolchain's
# whatever the working directory or elan's default toolchain.
#
# L2R_LEAN_TOOLCHAIN: the toolchain directory (with bin/lean). Default: the
# elan toolchain that lean2rr/lean-toolchain names, e.g.
# ~/.elan/toolchains/leanprover--lean4---v4.34.0 (ELAN_HOME is honoured).
# lean2rr reads only .olean files of the toolchain it is built with, so a
# test's native build must use the same one.
if [ -z "${L2R_LEAN_TOOLCHAIN:-}" ]; then
  l2r_pin=$(tr -d '[:space:]' < "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/lean2rr/lean-toolchain")
  l2r_pin=${l2r_pin//\//--}
  L2R_LEAN_TOOLCHAIN=${ELAN_HOME:-$HOME/.elan}/toolchains/${l2r_pin//:/---}
  unset l2r_pin
fi
if [ ! -x "$L2R_LEAN_TOOLCHAIN/bin/lean" ]; then
  echo "no Lean toolchain at $L2R_LEAN_TOOLCHAIN (set L2R_LEAN_TOOLCHAIN, or install it with elan)" >&2
  exit 2
fi
export L2R_LEAN_TOOLCHAIN
export PATH="$L2R_LEAN_TOOLCHAIN/bin:$PATH"
