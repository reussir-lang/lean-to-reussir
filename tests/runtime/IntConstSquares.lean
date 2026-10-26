/-!
Input of tests/runtime/int-backend-check.sh (not a runtime test: no `Rt`
prefix; native Lean runs out of memory at startup, when it computes `c6`).
A chain of `Int` constants, each squaring the one before it six times, so
`c6` is 3^(2^36), a number of about 10^11 bits. `keep` stores `c6` in a
`List`, a box, in a function (not in a constant's own code), so lean2rr
asks whether the box holds `c6` as an immediate (`constIsImmediate`).
`constNumValue?` folds the chain only while every value is below 2^64 (it
gives up in `c1`, at 3^64); before that limit it computed the numbers and
ran out of memory. The check translates this program under an
address-space limit and a timeout, and expects `c6`'s box to be made once
(`boxed-consts`: a cell).
-/

def c0 : Int := 3

def c1 : Int :=
  let a := c0 * c0
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * e

def c2 : Int :=
  let a := c1 * c1
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * e

def c3 : Int :=
  let a := c2 * c2
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * e

def c4 : Int :=
  let a := c3 * c3
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * e

def c5 : Int :=
  let a := c4 * c4
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * e

def c6 : Int :=
  let a := c5 * c5
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * e

@[noinline] def keep (n : Int) : List Int := [c6, n]

def main (args : List String) : IO Unit :=
  IO.println (keep args.length).length
