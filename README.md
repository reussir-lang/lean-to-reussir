# lean-to-reussir

A compiler from Lean 4 programs to [Reussir](https://github.com/reussir-lang/reussir),
an RC-based functional language with token-based memory reuse.

`lean2rr` reads the compiler's intermediate code (LCNF) of a compiled Lean
program, monomorphizes it, runs Lean's own mono-phase optimizations on it,
and lowers the result to typed Reussir source. Reussir then takes care of
ownership, reference counting and memory reuse. The design is described in
[`docs/translation-plan.md`](docs/translation-plan.md).

Status: see [`docs/implementation-status.md`](docs/implementation-status.md) (what is supported, how values are represented, test and benchmark results, known differences from native Lean).

## Requirements

- Lean v4.33.0 (via elan)
- Reussir built from source (LLVM/MLIR 23), checked out into `reussir/`

## Layout

- `lean2rr/` — the translator (a Lake package); its optional passes live in
  `lean2rr/LeanToReussir/Opt/`, listed in `Opt/Registry.lean`
  (`lean2rr --list-opts`)
- `runtime/` — the runtime: the prelude `prelude.rr` included in every
  program, and the Rust crate `leanrt` (see [`runtime/README.md`](runtime/README.md))
- `scripts/` — `l2r.py`, the driver (lean2rr, then rrc, linking the runtime)
- `reussir-patches/` — local Reussir patches (see [`docs/reussir-bugs.md`](docs/reussir-bugs.md))
- `docs/` — design documents
- `tests/` — the classic test corpus and its native-Lean oracle (see [`tests/README.md`](tests/README.md))
