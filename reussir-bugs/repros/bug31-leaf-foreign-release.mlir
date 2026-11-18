// Issue 31: the release of a box whose payload has no counted member, from
// foreign code (`reussir.foreign_drop`: a record's FFI release). Releasing
// such a box only frees it. Upstream still makes a worklist function for
// it and enters the drop worklist (`reussir.drop.join`); with patch 31-a
// the function keeps its body.
// Command: reussir-opt THIS --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true'
!leaf = !reussir.record<compound "Leaf" { i64, f64 }>
!token24 = !reussir.nullable<!reussir.token<align: 8, size: 24>>

module {
  func.func @leaf(%rc: !reussir.rc<!leaf shared>) attributes {reussir.foreign_drop} {
    %token = reussir.rc.dec(%rc : !reussir.rc<!leaf shared>) : !token24
    reussir.token.free(%token : !token24)
    return
  }
}
