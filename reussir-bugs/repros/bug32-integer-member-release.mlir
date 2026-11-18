// Issue 32: a recursive variant with integer members (needs a reussir-opt
// with rcgmp). Upstream treats an integer member as a cleanup whose order
// can be observed: each dead child goes on the worklist (`reussir.rc.defer`)
// and no arm continues in a child. With patch 32-a the integers are
// released in place and the `Add` arm continues in its last dead child by
// a tail release (`reussir.musttail`).
// Command: reussir-opt THIS --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true'
!expr_ = !reussir.record<variant "Expr" incomplete>
!val = !reussir.record<compound "Expr::Val" [value] { !rcgmp.mpz }>
!add = !reussir.record<compound "Expr::Add" [value] { !expr_, !rcgmp.mpz, !expr_ }>
!expr = !reussir.record<variant "Expr" { !val, !add }>
!token = !reussir.nullable<!reussir.token<align: 8, size: ?>>

module {
  func.func @expr(%rc: !reussir.rc<!expr>) {
    %token = reussir.rc.dec(%rc : !reussir.rc<!expr>) : !token
    reussir.token.free(%token : !token)
    return
  }
}
