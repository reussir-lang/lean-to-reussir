import Std.Data.HashMap
/-! Runtime test: a value held where its type is not known (an existential
package, `Pkg`, whose step function is one of its fields) and updated N
times by code over the unknown type: the package is consumed at each step,
so the value is unique when the step function receives it, and native Lean
updates it in place (amortized O(1) per step, no copy). Modes: `floats`
(`Array Float`: `modify` and `push`), `bytes` (`ByteArray.push`), `farr`
(`FloatArray.push` and `set!`), `string` (`String.push`), `rows`
(`Array (Array Nat)`, the last row modified in place), `ref` (an `IO.Ref
(Array Nat)` modified through `IO.Ref.modify`), `map` (`Std.HashMap.insert`),
`list` (`List.cons`, for reference). A copy at each step (a lost
uniqueness, or a conversion of the value) costs O(N) bytes per step: the
bytes grow quadratically. Arguments: MODE N (default: every mode, N = 50).
The output is checked here; the allocations and bytes of each mode at two
sizes by tests/runtime/alloc-check.sh (RtDepUnique.alloc). -/

structure Pkg where
  α : Type
  v : α
  step : α → Nat → α
  sum : α → Nat

/-- Code over the unknown type: one step, the package consumed. -/
@[noinline] def Pkg.next (p : Pkg) (i : Nat) : Pkg := ⟨p.α, p.step p.v i, p.step, p.sum⟩

/-- `Pkg` lives in `Type 1`: a tail-recursive loop rather than `for`. -/
def steps (p : Pkg) (i n : Nat) : Pkg :=
  if i < n then steps (p.next i) (i + 1) n else p
termination_by n - i

@[noinline] def loop (p : Pkg) (n : Nat) : Nat := let p := steps p 0 n; p.sum p.v

def floatsPkg : Pkg :=
  ⟨Array Float, #[], fun a i => (a.push i.toFloat).modify (i / 2) (· + 0.5),
   fun a => (a.foldl (· + ·) 0).toUInt64.toNat + a.size⟩

def bytesPkg : Pkg :=
  ⟨ByteArray, .empty, fun b i => b.push (i % 251).toUInt8, fun b => b.foldl (fun s x => s + x.toNat) b.size⟩

def farrPkg : Pkg :=
  ⟨FloatArray, .empty, fun a i => let a := a.push i.toFloat; a.set! (i / 3) (a.get! (i / 3) * 2),
   fun a => (a.foldl (· + ·) 0).toUInt64.toNat⟩

def stringPkg : Pkg :=
  ⟨String, "", fun s i => s.push (Char.ofNat (97 + i % 26)), fun s => s.length + s.foldl (fun n c => n + c.toNat) 0⟩

def rowsPkg : Pkg :=
  ⟨Array (Array Nat), #[#[]], fun r i =>
     let r := if i % 64 == 63 then r.push #[] else r
     r.modify (r.size - 1) (·.push i),
   fun r => r.foldl (fun s row => s + row.foldl (· + ·) 0 + 1) 0⟩

def mapPkg : Pkg :=
  ⟨Std.HashMap Nat Nat, {}, fun m i => m.insert i (i * i % 1000), fun m => m.fold (fun s k v => s + k + v) 0⟩

def listPkg : Pkg := ⟨List Nat, [], fun l i => i :: l, fun l => l.foldl (· + ·) 0⟩

structure RPkg where
  α : Type
  r : IO.Ref α
  step : α → Nat → α

@[noinline] def RPkg.next (p : RPkg) (i : Nat) : IO Unit := p.r.modify (p.step · i)

def run (mode : String) (n : Nat) : IO Nat := do
  match mode with
  | "floats" => return loop floatsPkg n
  | "bytes" => return loop bytesPkg n
  | "farr" => return loop farrPkg n
  | "string" => return loop stringPkg n
  | "rows" => return loop rowsPkg n
  | "map" => return loop mapPkg n
  | "list" => return loop listPkg n
  | "ref" =>
    let r ← IO.mkRef (#[] : Array Nat)
    let p : RPkg := ⟨Array Nat, r, fun a i => (a.push i).modify (i / 2) (· + 1)⟩
    for i in [0:n] do p.next i
    return (← r.get).foldl (· + ·) 0
  | _ => return 0

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "50").toNat!
  match args.head? with
  | some m => IO.println s!"{m} {← run m n}"
  | none =>
    for m in ["floats", "bytes", "farr", "string", "rows", "ref", "map", "list"] do
      IO.println s!"{m} {← run m n}"
