import Std.Sync.Channel
/-! Runtime test: `Selectable.one` over two channels (unbounded, bounded
and unbuffered), a receiver task against a sender that blocks until the
receiver takes each value (Lean's `async_select_channel` test, with fixed
random seeds). The receiver's continuations are tasks the sender's sends
release while the sender itself waits for a promise: a promise resolved
and released while its waiter is blocked leaves its runtime entry and its
cell's memory to new tasks, which the waiter must not take for its own
(it would run a task of the receiver's and wait for a value only it can
send). -/
open Std Async

def receiver (ch1 ch2 : Std.Channel Nat) (count : Nat) : Async Nat := do
  go ch1 ch2 count 0
where
  go (ch1 ch2 : Std.Channel Nat) (count : Nat) (acc : Nat) : Async Nat := do
    match count with
    | 0 => return acc
    | count + 1 =>
      Selectable.one #[
        .case ch1.recvSelector fun data => go ch1 ch2 count (acc + data),
        .case ch2.recvSelector fun data => go ch1 ch2 count (acc + data),
      ]

def run (capacity : Option Nat) (amount : Nat) : Async Bool := do
  let messages := Array.range amount
  let ch1 ← Std.Channel.new capacity
  let ch2 ← Std.Channel.new capacity
  let recvTask ← async (receiver ch1 ch2 amount)
  for msg in messages do
    if (← IO.rand 0 1) = 0 then
      ch1.sync.send msg
    else
      ch2.sync.send msg
  let acc ← await recvTask
  return acc == messages.sum

def main : IO Unit := do
  for cap in [none, some 0, some 1, some 128] do
    let mut ok := 0
    for seed in [1:13] do
      IO.setRandSeed seed
      if ← (run cap 100).block then ok := ok + 1
    IO.println s!"capacity {cap}: {ok} of 12 runs received every message"
