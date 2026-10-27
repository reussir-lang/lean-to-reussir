/-! Runtime test (review of a bug hunt of the names lean2rr recognizes,
2026-10-27): a program's `@[export]` under the C symbol of one of the
shim's externs, `lean_shim_promise_is_resolved` (the shim's
`IO.Promise.isResolved` asks the runtime through it). No native runtime
has that symbol, so natively the attribute only names a C symbol and
`isResolved` answers `false`. lean2rr bound every extern of Lean's library
or the shim whose C symbol some module exported to that export, the
program's included, so `ask` called `fake` and answered `true`. Now only
the exports of Lean's library and the shim count (`Mono.libraryExportMap`;
the `IO.Error` builders too). The program's definition is still called by
its own name. -/

@[export lean_shim_promise_is_resolved]
def fake {α : Type} (_p : IO.Promise α) : BaseIO Bool := pure true

@[noinline] def ask (p : IO.Promise Nat) : BaseIO Bool := p.isResolved

def main : IO Unit := do
  let p ← IO.Promise.new (α := Nat)
  IO.println s!"resolved? {← ask p}"
  IO.println s!"fake {← fake p}"
  p.resolve 3
  IO.println s!"resolved? {← ask p}"
