// Bug 33: the parser of `!reussir.rc<...>` and `!reussir.ref<...>` stops at
// the first token after the element type that is not a capability or
// atomic-kind keyword and drops the rest of the type's text: the function
// below is read as returning `!reussir.rc<i64 rigid>`, without `atomic`.
// Command: rrc THIS -x mlir --emit mlir -o OUT.mlir
// Expected: an error ("expected '>'").
// Reussir ef922049: succeeds, and OUT.mlir declares
// `func.func private @f() -> !reussir.rc<i64 rigid>`.
module {
  func.func private @f() -> !reussir.rc<i64 rigid, atomic>
}
