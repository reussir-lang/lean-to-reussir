// Issue 34: the release of a box of scalars and integers from foreign
// code (`reussir.foreign_drop`: a record's FFI release). Releasing such a
// box releases its integers in place and frees it. Upstream, and the
// series before patch 34-a, make a worklist function for it and enter the
// drop worklist (`reussir.drop.join`); with 34-a the function keeps its
// body. Needs a reussir-opt with rcgmp.
// Command: reussir-opt THIS --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true'
!two = !reussir.record<compound "Two" { !rcgmp.mpz, i64, !rcgmp.mpz }>
!t32 = !reussir.nullable<!reussir.token<align: 8, size: 32>>

module {
  func.func @two(%rc: !reussir.rc<!two shared>) attributes {reussir.foreign_drop} {
    %token = reussir.rc.dec(%rc : !reussir.rc<!two shared>) : !t32
    reussir.token.free(%token : !t32)
    return
  }
}
