// Issue 30: two pairs of arms, no vector, that release different values in
// the same way. MLIR's `convert-vector-to-llvm` simplifies regions: it
// merges each pair into one block that takes the values as arguments. In a
// big function with many such arms the arguments multiply from one merge
// to the next, and rrc's time with them (the pass runs in rrc's pipeline
// on an aarch64 host with SVE). Patch 30-a's pass runs the patterns alone
// and leaves the blocks as they are.
// Command: reussir-opt THIS --convert-vector-to-llvm   (MLIR's pass)
//          reussir-opt THIS --reussir-convert-vector-to-llvm   (30-a)
func.func private @release(i64, i64)

func.func @arms(%p: i1, %a: i64, %b: i64, %c: i64) {
  cf.cond_br %p, ^left, ^right
^left:
  call @release(%a, %a) : (i64, i64) -> ()
  cf.br ^next
^right:
  call @release(%b, %c) : (i64, i64) -> ()
  cf.br ^next
^next:
  cf.cond_br %p, ^left2, ^right2
^left2:
  call @release(%c, %c) : (i64, i64) -> ()
  cf.br ^exit
^right2:
  call @release(%a, %b) : (i64, i64) -> ()
  cf.br ^exit
^exit:
  return
}
