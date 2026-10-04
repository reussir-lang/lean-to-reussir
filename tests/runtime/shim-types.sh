#!/usr/bin/env bash
# Checks that each @[export] definition of lean2rr's shim (lean2rr/L2RShim.lean)
# has the type of the @[extern] declaration of the same C symbol (Lean pairs
# them by name only). Needs lean2rr built (`lake build`).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE/../../lean2rr"
exec lake env lean --run "$HERE/ShimTypes.lean"
