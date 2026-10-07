# 39. Token reuse takes the release of a hidden alias as the donor

**Kind:** missed optimization. Not a bug: rrc's output is correct. Not
patched.

## Summary

**Kind:** missed optimization. **Status:** documented only, no patch;
lean2rr's output avoids the shape (see [What lean2rr does](#what-lean2rr-does)).

**Verdict: missed optimization, not a bug.** The output is correct, and
TokenReuse documents its choice of donor as a heuristic. A dispatch arm
takes a field `h` of the matched cell, gives it to an opaque call that
returns the same object `p` (Reussir cannot see that `p` is `h`), and
rebuilds the cell with `h`. In the rebuilding branch, Reussir releases `p`,
which it does not use there. That release gives a token of the same size
as the matched cell. TokenReuse sees two tokens of the right size for the
new cell, the matched cell's and `p`'s, and both get the same score; the
most recent producer wins, which is `p`'s release. But `h` holds another
reference to `p`, so that release never frees: the token is always null,
the new cell is allocated, and the matched cell is freed. This is the
choice of [issue 7](07-phantom-reuse-donor.md) (a release that never
frees wins the token), from another cause: in issue 7, Reussir itself
retains the matched cell's children; here, an opaque call hides an alias.
Patch 07-a does not apply, and Reussir cannot know that the release never
frees.

## Symptom and repro

Repro
[`repros/bug39-alias-release-donor.rr`](repros/bug39-alias-release-donor.rr)
(the main part):

```
#[ffi(import)]
fn same<T>(x : T) -> T [{ x }];     // an opaque identity
struct P { k : u64, v : u64 }
enum L { Nil, Cons(P, L) }
fn bump(l : L, k : u64) -> L {
    match l {
        L::Nil => { L::Nil{} },
        L::Cons(h, t) => {
            let p : P = same(h);
            let x : u64 = p.k;
            if x == k { L::Cons{P{x, p.v + 1}, t} } else { L::Cons{h, bump(t, k)} }
        }
    }
}
fn bump_b(l : L, k : u64) -> L {    // the same, but the rebuilt cell gets p
    ... else { L::Cons{p, bump_b(t, k)} } ...
}
```

Each function runs 1000 and then 4000 bumps on a new list of 64 pairs (a
bump rebuilds about 32 cells). The program counts the cells allocated
meanwhile: the link wraps Reussir's allocation entry points
(`__reussir_allocate`, `__reussir_allocate_small`). A pair cell and a list
cell are both 24 bytes.

**Command** (`run.sh bug39`): `rrc bug39-alias-release-donor.rr -O
aggressive --no-pack-record-members --reuse-across-call
--link-arg=-Wl,--wrap=__reussir_allocate,--wrap=__reussir_allocate_small`.

- *Expected*: `bump 0 0 bump_b 0 0` (each rebuilt cell reuses the matched
  cell).
- *Reussir l2r-local d79f8b70, and l2r-anybox 1eb710b4 (d79f8b70, 38-a,
  13-d)*: `bump 32020 129488 bump_b 0 0`. `run.sh` printed `issue 39
  REPRODUCES  bump allocates 32020 cells for 1000 bumps, 129488 for 4000
  (bump_b: 0, 0)`. Not checked on ef922049.

`--token-reuse-remarks` shows the choice. For `bump`'s rebuilt cell
(`L::Cons{h, bump(t, k)}`): 2 tokens available, 2 compatible, the chosen
one has score 2 and its source is the rebuilding branch (the release of
`p`). For `bump_b`'s: 1 token available, the matched cell's (source: the
`Cons` arm), score 2.

In lean2rr: `RtProbeBump`, an association list of pairs bumped in a loop
(`List (Nat × Nat)`, rebuilt up to the key; a probe of the dependent-type
work). During the dependent-type work (commit ef4a84a), with Reussir
1eb710b4, it allocates 31310 times for 1000
bumps and 125778 times for 4000 (757 KB and 3.0 MB): one list cell for
each rebuilt cell. Native Lean and lean2rr on dev 922ca03 allocate nothing
more at 4000 bumps than at 1000. The same program with the one changed
line below allocates 292 and 290 times. A list of a user constructor with
two `Nat` fields (24-byte cells too) shows the same growth (32248 and
129714); with three fields (32-byte cells: no token of the right size) the
list cells are reused (1228 and 4226, one new constructor cell for each
bump); a `List Nat` allocates nothing in the loop (162 and 164).

## Cause

Dispatch fusion works here: the arm retains `h` and `t` and then releases
the matched cell, and `RcDispatchFusion` turns that into a destructuring
decrement, whose token is the matched cell when it is unique. Because `h`
is used twice (by `same` and by the rebuilt cell), Reussir retains it once
more before `same(h)`. In the rebuilding branch, `p` has no use, so
Reussir releases it there, before the recursive call (`rc.dec` of
`same`'s result; in the IR before `TokenReuse`, an expanded decrement with
a token of 24 bytes, the size of a list cell).

`TokenReuse` (`lib/Transformation/TokenReuse/TokenReuse.cpp`) keeps the
pool of available tokens: with `--reuse-across-call`, the call between the
releases and the new cell does not flush it. The loop that serves the new
cell (`for (auto tokenVal : availableTokens)`, line 733) scores each token
with `scoreToken` and `heuristic` (lines 461 and 250). Both tokens are an
exact-size match, score 2: the bonus for a donor whose fields the new cell
reuses never applies (see "TokenReuse's locality bonus is dead code" in
the [README](README.md#other-observations)). At an equal score the loop
keeps the token with the greater `tokenOrderKey` (line 348: "prefer the
most recent producer"), and the release of `p` comes after the arm's
decrement. The new cell then gets a `token.ensure` on a token that is
always null (the count of `p` is at least 2: `h` still holds it), so it
allocates; the matched cell's token is unused and freed at the end of the
branch.

Reussir cannot know that the release of `p` never frees: `same` is an
opaque call, and its result could be a unique object. So the choice is a
heuristic that loses on this shape, not a mistake about what is known.

## What lean2rr does

lean2rr avoids the shape: a field put back into a rebuilt node is boxed
again from its unboxed value. The shape came from rule 1 with the one-word
box and lean2rr commit 3f0cb30 ("a field put back where its box was passes
that box"), now reverted:
- a field of a parameter's type is a `Box` (`T_List`'s head holds a boxed
  `T_Prod`);
- the arm unboxes it (`l2r_any_raw`, then `l2r_any_raw_take`, opaque
  calls: they play `same`);
- the rebuilt cell got the original box `f638` (`CodeCtx.fieldOf`,
  `varAt`, both removed), where the code now boxes the unboxed pair again;
- the unboxed pair was then dead in the rebuilding branch, and its release
  was the donor that never frees.

Boxing the unboxed pair again (`T_List_3::c_cons{l2r_any_of<T_Prod_607>(fv640,
19), x654}` in place of `T_List_3::c_cons{f638, x654}`) leaves no release
of the pair. `RtProbeBump` then allocates nothing in its loop, as natively
(alloc-check, 1000 -> 4000 bumps: +0 allocations; +97466 with 3f0cb30).
With the one-word box, boxing a pointer payload allocates nothing (only a
word with the payload's number); a payload that a box holds in a cell
(`Float`, `UInt64` from 2^63, an `ElemBox` around a `[value]` record) gets
a new cell. 3f0cb30 was made when a box was a heap cell, and it saved one
allocation for each rebuilt node then. The repro (`repros/bug39-alias-release-donor.rr`)
keeps the shape by hand.

## Patch

None. A patch would change `TokenReuse`'s choice, a performance decision:
- prefer, at an equal score, the token of a destructuring decrement (the
  matched cell) to the token of a plain release; or
- make the locality bonus work, so that it scores the matched cell 3
  here (the rebuilt cell's field `h` is loaded from it). The README's
  observation lists its two mistakes (with only the first one corrected,
  a dispatch without a result crashes the pass); besides, the IR that
  `TokenReuse` sees has no dispatch left (`ConvertToSTD` runs first): the
  arm reads `h` through a `reussir.record.coerce` of the scrutinee's
  borrow, which the walk would also have to step over (seen in this
  repro's IR before `TokenReuse`, made with `reussir-opt` and the
  pipeline's passes up to it).

Either one changes which token many programs reuse; issue 7 shows that
the choice between donors matters in both directions.
