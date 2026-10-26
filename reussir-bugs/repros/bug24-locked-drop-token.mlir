// Issue 24 (bug): with the acquire/drop expansion's default options (both
// tail-recursive and retcon drops off: TPDE mode's options), the drop of a
// mutex cell releases the payload inside the critical section, and token
// reuse never frees the payload's decrement token: the payload's box leaks
// (ASan: 24 bytes for an `Arc` box of a one-word record, end to end).
//
// Command: reussir-opt bug24-locked-drop-token.mlir
//   --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true'
//   --reussir-token-reuse
// Expected: a `reussir.token.free` of the payload's token (as for the same
// box outside a cell).
// Upstream 00906e38: no `reussir.token.free` at all. With 23-e (the
// locked-drop function under every option): one, in `__reussir_locked_drop`.
!b = !reussir.record<compound "LkBox" {i64}>
module {
  func.func @locked(%ref: !reussir.ref<!reussir.cell<!reussir.rc<!b atomic> mutex>>) {
    reussir.ref.drop (%ref : !reussir.ref<!reussir.cell<!reussir.rc<!b atomic> mutex>>)
    return
  }
}
