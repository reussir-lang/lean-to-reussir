# lean-to-reussir

A compiler from Lean 4 programs to [Reussir](https://github.com/reussir-lang/reussir),
an RC-based functional language with token-based memory reuse.

`lean2rr` reads the compiler's intermediate code (LCNF) of a compiled Lean
program, monomorphizes it, runs Lean's own mono-phase optimizations on it,
and lowers the result to typed Reussir source. Reussir then takes care of
ownership, reference counting and memory reuse. The design is described in
[`docs/translation-plan.md`](docs/translation-plan.md).

Status: early development.

## Requirements

- Lean v4.33.0 (via elan)
- Reussir built from source (LLVM/MLIR 23), checked out into `reussir/`

## Layout

- `lean2rr/` — the translator (a Lake package)
- `docs/` — design documents
