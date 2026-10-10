/-! Runtime test: optimization `flatten-structs` in a program that creates a
resource (it writes a file and reads it back). In such a program the pass
leaves alone every declaration with a parameter or a result that may hold a
resource: lean2rr emulates Lean's release times with Lean's borrow
inference on that code (Lower/Borrow). The loop records here have a field
whose type depends on a value (`Vector σ.Update n`, `Array lcAny` in mono
code), as lean-regex's `SearchState`; by type every `lcAny` may be a
handle, so the type rule left these loops alone in every program that
reads a file. The whole-program analysis `ResourceFlow` sees that only
numbers reach the field, so they are split as in a program without
resources (`RtFlattenResFlow.l2r-debug`: the loops are not left alone):
- `loop`: lean-regex's `εClosure` shape, a self-recursive loop over the
  record and a work list, called once per round;
- `step`: one call per step, each returning the pair of an `Option` and
  the record: with the pass no pair and no record is built
  (`RtFlattenResFlow.alloc`; natively one pair per step, the record's cell
  reused). -/

structure Strat where
  Update : Type
  empty : Update
  write : Update → Nat → Update

structure St (σ : Strat) (n : Nat) where
  count : Nat
  seen : Vector Bool n
  updates : Vector σ.Update n

@[noinline] def resLoop (σ : Strat) (n : Nat) :
    Nat → Option σ.Update → St σ n → List (σ.Update × Fin n) → Option σ.Update × St σ n
  | 0, m, st, _ => (m, st)
  | _, m, st, [] => (m, st)
  | fuel + 1, m, st, (u, x) :: xs =>
    if st.seen[x] then resLoop σ n fuel m st xs
    else
      match st with
      | ⟨count, seen, updates⟩ =>
        let m' := if x.val + 1 == n then m <|> some u else m
        let updates' := if x.val % 2 == 0 then updates.set x u else updates
        let xs' := if h : x.val + 1 < n then (σ.write u x, ⟨x.val + 1, h⟩) :: xs else xs
        resLoop σ n fuel m' ⟨count + 1, seen.set x true, updates'⟩ xs'

@[noinline] def resStep (σ : Strat) (n : Nat) (m : Option σ.Update) (st : St σ n) (u : σ.Update)
    (x : Fin n) : Option σ.Update × St σ n :=
  match st with
  | ⟨count, seen, updates⟩ =>
    let m' := if x.val + 1 == n then m <|> some u else m
    (m', ⟨count + 1, seen.set x true, if x.val % 2 == 0 then updates.set x u else updates⟩)

@[noinline] def resSteps (σ : Strat) (n : Nat) (h : 0 < n) :
    Nat → σ.Update → Option σ.Update → St σ n → Option σ.Update × St σ n
  | 0, _, m, st => (m, st)
  | k + 1, u, m, st =>
    let (m', st') := resStep σ n m st u ⟨k % n, Nat.mod_lt _ h⟩
    resSteps σ n h k (σ.write u k) m' st'

def natStrat : Strat := ⟨Nat, (0 : Nat), fun (u : Nat) x => u + x⟩
def natStrat2 : Strat := ⟨Nat, (0 : Nat), fun (u : Nat) x => u * 3 + x⟩
@[noinline] def pick (k : Nat) : Strat := if k > 5 then natStrat2 else natStrat

def main (args : List String) : IO Unit := do
  let mode := args.headD "loop"
  let k := (args[1]? >>= String.toNat?).getD 10
  let path : System.FilePath := "rtflattenresflow-tmp.txt"
  IO.FS.writeFile path "resource"
  let txt ← IO.FS.readFile path
  let σ := pick args.length
  let n := 1000
  let z : Vector Bool n := Vector.replicate n false
  if mode == "step" then
    let (m, st) := resSteps σ n (by decide) k σ.empty none ⟨0, z, Vector.replicate n σ.empty⟩
    IO.println s!"step {st.count} {m.isSome} {txt.length}"
  else
    let mut acc := 0
    for r in [0:k] do
      let (m, st) := resLoop σ n (2 * n) none ⟨0, z, Vector.replicate n σ.empty⟩ [(σ.empty, ⟨r % 7, by omega⟩)]
      acc := acc + st.count + (if m.isSome then 1 else 0)
    IO.println s!"loop {acc} {txt.length}"
