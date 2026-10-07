/-! Runtime test (review RLF1-06): `String.ofList` (`lean_string_mk`, which
lean2rr lowers itself) makes the string at its UTF-8 size in one
allocation, as natively `lean_string_mk` does (`lean_mk_string_unchecked`
of the bytes). lean2rr pushed the characters onto `""`, which grew the
string about log2 n times (up to twice its size). A list of 1001
characters of every UTF-8 width is converted `k` times (the argument,
default 10); tests/runtime/alloc-check.sh compares the bytes requested at
two `k`s (RtStrOfListAlloc.alloc). -/
def main (args : List String) : IO Unit := do
  let k := (args.head? >>= String.toNat?).getD 10
  let cs := (List.range (1000 + args.length)).map fun i =>
    match i % 4 with
    | 0 => 'a'
    | 1 => 'é'
    | 2 => '€'
    | _ => '😀'
  let mut total := 0
  for _ in [0:k] do
    let s := String.ofList cs
    total := total + s.utf8ByteSize + s.length
  IO.println total
