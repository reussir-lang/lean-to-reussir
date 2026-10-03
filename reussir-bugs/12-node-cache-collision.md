# Patch 0012: the parser swaps syntax subtrees whose hashes collide (bug 12)

> **Audit (2026-10-02):** a real bug, in Reussir's parser dependency `cstree` (0.14; unchanged in cstree's master): the node cache is keyed on a 32-bit hash with no equality check.

Patch file: `../0012-l2r-local-bug-12-build-syntax-nodes-without-cstree-s-hash-only-node-cache.patch`
(`l2r-local` commit `42635042`). Bug section:
[docs/reussir-bugs.md, bug 12](../../docs/reussir-bugs.md#12-the-parsers-node-cache-swaps-subtrees-whose-hashes-collide).

## 1. Summary

Reussir's parser builds its syntax tree with the `cstree` library.
cstree's tree builder deduplicates small nodes: when a new node has at most
three children and the same kind, the same text length and the same 32-bit
hash of its children as an earlier node, the builder returns the earlier
node. It never compares the children. In a large file, two different
subtrees eventually collide, and the later one silently becomes a copy of
the earlier one. A literal can turn into a variable of an unrelated
function. That gives a baffling "unknown variable" error, or, if the
variable happens to be in scope, a program that compiles and computes the
wrong thing. The patch builds every syntax node directly, with no cache.
The builder is still used for tokens, whose cache compares whole tokens.

## 2. Symptom

The repro must be a large file, so `docs/reussir-bugs/` has a generator,
`bug12-node-cache-collision.py OUT.rr`:

```python
import sys

V, S = "vvvvvv", "424242"
lines = [
    "enum T {", "    One(u64)", "}", "",
    "fn get(t: T) -> u64 {", "    match t {", "        T::One(a) => a", "    }", "}", "",
]
lines += ["// a%d" % i for i in range(149330)]
lines += [f"fn first({V}: u64) -> u64 {{ get(T::One{{{V}}}) }}", ""]
lines += ["// b%d" % i for i in range(38022)]
lines += [
    f"// second(n) returns {S}; with the bug it returns n.",
    f"fn second({V}: u64) -> u64 {{ get(T::One{{{S}}}) }}",
    "",
    "#[ffi(import)]",
    'fn say(x : u64) [{ println!("{}", x) }];',
    "#[main]",
    "fn main() { say(second(7)); }",
    "",
]
open(sys.argv[1], "w").write("\n".join(lines))
```

The roughly 187,000 comment lines only use up interner keys: each comment
is a distinct token text, and keys are handed out in order of first
occurrence. The counts were found by search so that the keys of `vvvvvv`
and `424242` make the constructor-argument nodes of `T::One{vvvvvv}` and
`T::One{424242}` hash alike. Per the patch's unit test, the keys are
149353 and 187378.

Command: `rrc OUT.rr -O aggressive`.

- Expected: `424242`.
- Actual on ef922049: `7`, with no diagnostic, at every `-O` level.
  `second`'s argument `T::One{424242}` is parsed as `T::One{vvvvvv}`, and
  `vvvvvv` is `second`'s parameter. `run.sh` printed
  `bug 12   REPRODUCES  prints 7 (the literal 424242 was parsed as the variable), expected 424242`.

In lean2rr output (docs/reussir-bugs.md):

- `unknown variable x78617` on a 60,000-element list literal. The error
  was reported at an integer literal whose node had collided with a node
  holding a variable of a function 114,000 lines earlier. The patch message
  gives the literal as `368973` in a 14 MB file.
- Earlier adversarial findings: a call swapped for another function's
  call, and a match pattern swapped for another variant (a type mismatch).

## 3. Root cause

`crates/reussir-syntax/src/parser/sink.rs`, `Sink::finish`, replays the
parser's event stream (`Start`, `Token`, `Finish`) into a cstree
`GreenNodeBuilder`:

```rust
Event::Finish => {
    ...
    self.builder.finish_node();
    self.depth -= 1;
}
Event::Token => {
    self.attach_trivia();
    self.token();          // self.builder.token(token.kind, token.text(self.source))
}
...
let (green, _cache) = self.builder.finish();
```

`finish_node` ends in cstree 0.14's `NodeCache::node`
(`src/green/builder.rs` in the `cstree-0.14.0` crate):

```rust
const CHILDREN_CACHE_THRESHOLD: usize = 3;
...
let mut hasher = FxHasher::default();
for child in &all_children[offset..] {
    text_len += child.text_len();
    child.hash(&mut hasher);
}
let child_hash = hasher.finish() as u32;
let children = all_children.drain(offset..);
if children.len() <= CHILDREN_CACHE_THRESHOLD {
    self.get_cached_node(kind, children, text_len, child_hash)
} else {
    GreenNode::new_with_len_and_hash(kind, children, text_len, child_hash)
}
```

`get_cached_node` looks the node up in
`FxHashMap<GreenNodeHead, GreenNode>`, where

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct GreenNodeHead {
    kind: RawSyntaxKind, text_len: TextSize, child_hash: u32,
}
```

and returns the stored node on a hit (`entry(head).or_insert_with_key(...)`).
The key's equality is derived from those three fields, so two nodes with
equal kind, length and 32-bit child hash are "the same node", whatever
their children. The new node's children are thrown away and the earlier
subtree is used in their place.

What enters `child_hash`: a child node contributes its own head (its kind,
length and child hash), and a child token contributes its kind, length and
*interner key* (`GreenTokenData { kind, text: Option<TokenKey>, text_len }`).
Interner keys are assigned in order of first occurrence in the file, so
whether two nodes collide depends on everything before them. With a 32-bit
hash, a file with millions of small nodes of the same kind and length can
expect a collision; docs/reussir-bugs.md estimates about one per very
large file. A swapped subtree that contains a local name almost always
fails to compile, because lean2rr's local names are unique. Subtrees made
only of global names and literals (zero-argument calls, patterns without
binders, calls with literal arguments) can be swapped silently whenever
their types agree.

## 4. The fix

The sink no longer uses the builder for nodes (`sink.rs`, plus a test in
`lib.rs`).

- **State.** `Sink<'s, 'i, I>` with its `builder` and `depth` becomes
  `Sink<'s>` with `green_tokens: Vec<GreenToken>` (one per lexed token),
  `parents: Vec<(SyntaxKind, usize)>` (open nodes and the index of each
  one's first child), and `children: Vec<NodeOrToken<GreenNode,
  GreenToken>>`. `Sink::new` has the same arguments as before.
- **Start** pushes `(kind, children.len())` instead of
  `builder.start_node(kind)`.
- **Finish** builds the node itself, with no cache:

  ```rust
  let (kind, first_child) = self.parents.pop().unwrap();
  let node = GreenNode::new(kind.into_raw(), self.children.drain(first_child..));
  self.children.push(NodeOrToken::Node(node));
  ```

  At the end, exactly one child is left, and it is the root.
- **Token** pushes the pre-built `green_tokens[cursor].clone()`.
- **`green_tokens()`** creates every token up front, in source order,
  through a scratch `GreenNodeBuilder` with the same interner. It starts
  one `SourceFile` node, adds every token, finishes, and takes the tokens
  back out of the scratch node. The builder only offers tokens as children
  of a node, hence the scratch node. That single node cannot collide with
  anything.

**Why it is correct.** `GreenNode::new` computes the node's length and hash
but consults no cache, so every node holds exactly its own children.
Tokens are still shared through the builder's token cache. That cache is
sound: it is keyed on `GreenTokenData` with derived equality, which
compares kind, text key and length, so equal keys mean equal tokens.
Interning happens in the same order as before (every token, trivia
included, in source order), so token keys and spans are unchanged. The new
test `small_nodes_with_equal_hashes_stay_distinct` is the repro: it checks
that the one integer literal is `424242` under a `LiteralExpr`, and that
the tree's text equals the source (the tree is lossless). If cstree's hash
ever changes, the test no longer forces a collision, but it still checks
that the tree reproduces the source.

**Cost.** Without node sharing the parser uses somewhat more memory. The
sources measure different things:

- the patch message: a 14 MB file's HIR build uses about 40 MB (3.5%)
  more, in the same time;
- docs/reussir-bugs.md: 7-18% more parse memory (a 101 MB file: 2.1 → 2.5
  GB), and no change in rrc's peak memory on full builds;
- review round 3 (`rrc -t hir` peak RSS): +2.3% on a 127 MB file and +1.1%
  on a 178 MB one, with identical HIR. A 101 MB file (`PrgPolyM1.rr`)
  stopped with three bug-12 errors at 3.0 GB unpatched, and completed at
  5.3 GB patched.

## 5. Verification

- Review round 3 found that the sink is the only place a green tree is
  built. `parse`, `parse_with_interner` and `parse_repl` (REPL and LSP)
  all go through it, there is no incremental reparsing, and the remaining
  scratch builder builds a single node. HIR dumps (`rrc -t hir`) of 475
  sampled `.rr` files under 1 MB and all 348 files over 1 MB in the scratch
  area were compared with the unpatched parser. They were identical except
  for 13 files: 11 known bug-12 victims, where unpatched rrc reports errors
  and patched rrc none, and 2 copies of the silent demo, where unpatched
  HIR is silently wrong.
- Corpus, runtime suite and lean2rr programs with the combined stack:
  passed (round 3).
- `run.sh` on the patched build: `bug 12   FIXED       prints 424242   [-O aggressive]`.

## 6. Effect on lean2rr

lean2rr cannot avoid this bug: any shape, name or literal can collide, and
its outputs are large (tens of MB for big programs). The patch removes both
the "impossible" rrc errors on large outputs and the risk of silently wrong
code. The only cost is parse memory, as above.

## 7. Upstream note

reussir-syntax builds its green tree with cstree 0.14's `GreenNodeBuilder`,
whose node cache keys nodes of up to three children on (kind, text length,
32-bit hash of the children) and never compares the children. On a
collision, the later subtree becomes the earlier one. In large files a
literal turns into an unrelated variable (an "unknown variable" error, or
silently wrong code if it is in scope). A 1.9 MB generated repro exists.
Fix: build nodes with `GreenNode::new` (no cache), keeping the builder for
tokens. The cache behaviour may also be worth reporting to cstree.
