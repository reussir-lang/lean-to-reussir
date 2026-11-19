// Issue 33: a decrement of a shared box without its token result, the form
// the frontend emits (before `reussir-token-instantiation`). Upstream's
// decrement expansion reads the type of the missing result: SIGSEGV in
// reussir-opt. With patch 33-a the expansion leaves the decrement as it
// is (the token pass must run first).
// Command: reussir-opt THIS --reussir-rc-decrement-expansion
!leaf = !reussir.record<compound "Leaf" { i64, f64 }>

module {
  func.func @leaf(%rc: !reussir.rc<!leaf>) {
    reussir.rc.dec(%rc : !reussir.rc<!leaf>)
    return
  }
}
