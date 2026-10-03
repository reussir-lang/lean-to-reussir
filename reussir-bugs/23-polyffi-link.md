# Patch 0017: the compiled polymorphic-FFI modules are linked one call each (bug 23)

Patch file: `../0017-l2r-local-bug-23-link-the-gathered-polymorphic-FFI-m.patch`
(made as commit `91da4f80` in a scratch checkout, on top of 0016; it also
applies without 0016). Bug section:
[docs/reussir-bugs.md, bug 23](../../docs/reussir-bugs.md#23-linking-the-compiled-polymorphic-ffi-modules-is-quadratic-in-their-number).

## 1. Summary

rrc compiles the Rust body of every instance of a polymorphic
`#[ffi(import)]` function (a "texture") to LLVM bitcode, one rustc process
per instance, and then links all these bitcode modules into one before the
MLIR lowering pipeline runs. It linked them with one call of the static
`llvm::Linker::linkModules` per module. Each call builds a new linker, and
the linker's constructor walks the whole module linked so far, so linking
K modules took time quadratic in K: a lean2rr program using Std.Http (8241
instances) spent 65 minutes there. The patch links all the modules through
one linker, as `llvm-link` does: 6.4 s.

## 2. Symptom

Repro `docs/reussir-bugs/bug23-polyffi-link.py K OUT.rr`: K shared records
and one import `id<T>` called at each of them, so K textures. Each texture
puts its argument through a `HashMap`, so it carries its own copy of the
hash map code (48 KB of bitcode, like lean2rr's `l2r_origin_note`
instances). The program prints K*(K-1)/2.

Command: `rrc OUT.rr -O aggressive`.

- Expected: build time linear in K.
- Actual on ef922049: the texture compiles are linear (about 0.1 s each),
  but the link that follows them is quadratic: K = 300: 4.0 s, K = 600:
  22.8 s, K = 1000: 56 s, K = 2000: 339 s (whole builds 260 s for 1000 and
  706 s for 2000). `run.sh` prints `bug 23   REPRODUCES  link of the
  gathered modules: K = 300: 4.0 s, K = 600: 22.8 s (5.70x for twice the
  instances)` on the unpatched build.

Found while fixing round-6 failure IO6-14 (Std.Http did not build). Once
lean2rr's output compiled, rrc on `adv6/io/Io6Http.lean` (a local HTTP
server and TCP clients) was still in its polymorphic-FFI phase after 35
minutes. Measured again: 788 s of texture compiles, then 3881 s of
linking. A smaller program on the same library (`Io6H1`, 281 instances)
built in about two minutes, mostly other phases.

## 3. Root cause

`lib/IR/ReussirOps.cpp`, `gatherCompiledModules`, parses each compiled
module and links it into the first one:

```c++
if (!finalModule) {
  // First module becomes the base
  finalModule = std::move(parsedModule);
} else {
  // Link subsequent modules into the final module
  if (llvm::Linker::linkModules(*finalModule, std::move(parsedModule))) {
```

`Linker::linkModules(Dest, Src)` is a convenience for a single link: it
constructs `Linker L(Dest)` and calls `L.linkInModule(Src)`. `Linker`
holds an `IRMover`, and the `IRMover` constructor prepares for linking
into `Dest`: it runs `TypeFinder::run` over all of `Dest` (every global,
function, instruction, operand and attached metadata node) to collect its
struct types, and it enters every metadata node the walk visited into its
metadata map (`SharedMDs`), mapped to itself. That costs time proportional
to the size of `Dest`, and `Dest` grows with every module linked into it.
The k-th call pays for the k-1 modules before it, so K modules cost
O(K^2) module sizes.

perf over `Io6Http`'s link phase: 96.8% of the time under
`llvm::IRMover::IRMover`: 72.6% inserting into the metadata map (with
`ReplaceableMetadataImpl::getOrCreate` and the tracking of the map's
`TrackingMDRef`s), 16.3% in `TypeFinder::run`. The work of moving the new
module's code (`linkInModule` itself) was about 1.3%.

LLVM's linker is meant to be kept for a sequence of modules. `llvm-link`
creates one `Linker` over its composite module and calls `linkInModule`
for every input file; regular LTO keeps one `IRMover` for all its inputs.
`llvm/Linker/Linker.h` describes the class as keeping "a pointer to the
merged module so far", and `llvm/Linker/IRMover.h` documents `SharedMDs`
as "A Metadata map to use for all calls to move()" (and `NamedMDNodes` as
a cache for the named-metadata merge). Nothing in Reussir needs a fresh
linker per module.

Why lean2rr hits it: each polymorphic prelude import used at a new type
is one texture, and a large program uses its imports at thousands of
types. In `Io6Http`: `l2r_origin_take` 2657, `l2r_origin_note` 2656,
`l2r_origin_back` 262, `l2r_once_get` and `l2r_once_set` 476 each,
`l2r_lcell_*` 110 each, `l2r_task_*` 67 to 109 each, `l2r_retype` 37. The
conversion-origin textures each carry their own copy of `leanrt::origin`'s
table code (generic in the two types): 91% of the 197 MB of texture
bitcode.

## 4. The fix

```c++
-  // Parse bitcode and link all modules together
+  // Parse bitcode and link all modules together, through one `llvm::Linker`
+  // for the whole gather, as `llvm-link` does. The static
+  // `Linker::linkModules` builds a new linker per call, and the linker's
+  // `IRMover` constructor walks every type and metadata node of the
+  // destination: one call per module made the gather quadratic in the number
+  // of instances (thousands of instances took more than half an hour).
   std::unique_ptr<llvm::Module> finalModule;
+  std::optional<llvm::Linker> linker;
   ...
       finalModule = std::move(parsedModule);
+      linker.emplace(*finalModule);
     } else {
       // Link subsequent modules into the final module
-      if (llvm::Linker::linkModules(*finalModule, std::move(parsedModule))) {
+      if (linker->linkInModule(std::move(parsedModule))) {
```

**Why it is correct.** Each call does the same link as before:
`linkModules` is exactly "construct a `Linker` over the destination, then
`linkInModule` with the default flags". The only difference is the state
the mover keeps between calls instead of rebuilding it from the
destination:
- the struct types of the destination: the mover adds the types each link
  creates in the destination, so its set is the one a new walk would
  find, plus types that a later link made unused, which can only make an
  isomorphic type be reused instead of a new one created (a name, not a
  meaning; LLVM's pointers are opaque);
- the metadata map: entries for the metadata of earlier source modules.
  Those modules are destroyed after their link, but metadata nodes belong
  to the `LLVMContext`, which lives until the gathered module is linked
  into the main one, and the map's `TrackingMDRef`s follow any node that
  is replaced;
- the named-metadata cache, which a new mover rebuilds from the
  destination anyway.

This is the use `llvm-link` makes of the same API, with the inputs
destroyed one by one as here. The `Linker` refers to `*finalModule`, which
it never outlives: `linker` is declared after `finalModule`, so it is
destroyed first on every return path (on success after `finalModule` has
been moved to the caller, which keeps the module alive).

## 5. Verification

- The linked module is the same. A stand-alone program linking
  `Io6Http`'s 8236 texture modules both ways: identical IR (`llvm-dis`,
  only the module name differs) for the first 2000 and the first 3500
  modules (the 3500 include about 1000 of the large origin modules).
  `Io6H1` (281 instances): objects identical up to the texture crate
  names, which come from random temporary file names and differ between
  any two builds. Generated programs with up to 2000 small instances:
  byte-identical objects.
- Times: see §2; with the patch, K = 300: 0.3 s, 600: 0.5 s, 1000: 0.9 s,
  2000: 1.9 s; `Io6Http`: 6.4 s instead of 3881 s. The stand-alone program
  (parsing excluded): 3500 modules 69-82 s one call each, 1.0-1.7 s through
  one linker; all 8236 through one linker 3.0 s (`llvm-link`: 10.4 s with
  parsing and writing).
- `docs/reussir-bugs/run.sh`: `bug 23   FIXED  link of the gathered
  modules: K = 300: 0.3 s, K = 600: 0.5 s (1.66x for twice the
  instances)`.
- Reussir's tests: the 26 lit tests that use polymorphic FFI
  (`basic/*/polyffi*`, `conversion/nested_polyffi`, `frontend/ffi_*`,
  `frontend/*ffi*_e2e`, `std/hash`, `codegen/wasm_target_features`), run
  with a hand-written lit site configuration; `cargo test -p
  reussir-backend -- --include-ignored` (14, including `polyffi_link`,
  which gathers and links a texture); `cargo test -p reussir-compiler
  --test driver` (25). All pass. No new test: the patch changes time, not
  output, and a timing test would be fragile on CI.
- lean2rr's runtime tests, 37 of them, with the patched build (arrays,
  casts and conversions, conversion origins and pointer identity, tasks,
  thunks, promises, files, processes, sockets): all pass.

## 6. Effect on lean2rr

Build time only: lean2rr's output is linked the same way, faster. Large
programs (thousands of instances, as with Std.Http) spent most of rrc's
time linking: `Io6Http` spent 65 minutes in the link alone. With the patch
it reaches MLIR's interprocedural SCCP (bug 11), where it was still
running after 50 minutes, so such programs need more than this patch to
build in reasonable time. The texture compiles stay linear, one rustc
process per instance (45 to 100 ms each, 12 minutes for `Io6Http`).
Fewer instances shrink both the compiles and the link; lean2rr's
conversion-origin calls are two thirds of them.

## 7. Upstream note

`gatherCompiledModules` (`lib/IR/ReussirOps.cpp`) links each compiled
polyffi module with the static `llvm::Linker::linkModules`, which builds a
new `Linker` (and `IRMover`) per call; the `IRMover` constructor walks the
whole destination, so gathering K modules is O(K^2) (8241 modules: 65
minutes, 97% in `IRMover::IRMover`). Fix: one `llvm::Linker` over the
first module and `linkInModule` for the others, as `llvm-link` does (6 s).
