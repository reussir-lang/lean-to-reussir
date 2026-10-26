#!/usr/bin/env bash
# No texture of runtime/prelude.rr lends the address of one of its own
# locals to a leanrt function that may stay out of line. A texture inlines
# into the Reussir function that calls it; a local whose address escapes
# into a call is a stack slot of that function, and LLVM then keeps the
# function's self tail call a real call: a Lean loop that calls the
# texture grows the stack until it overflows (see "An escaping stack slot
# blocks tail calls" in docs/implementation/reussir-workarounds/
# limitations.md). The promise, lock, timer and socket textures did this
# (`leanrt::task::promise_cell(&p)`, `leanrt::task::resolve_with(a, &mut ||
# ..)` over the texture's locals, `leanrt::sync::mutex_lock(&h)`,
# `leanrt::net::timer_next(&t, ..)`: tests RtLoopTailPromise,
# RtLoopTailSync, RtLoopTailIO); they now call by-value wrappers
# (`leanrt::task::owned`, `sync::owned`, `net::owned`, `proc::owned`,
# `fs::owned`) that take their arguments, release them and are
# `#[inline(never)]`.
# The rule checked, in every texture (`[{ ... }]`) of the prelude:
# - an argument `&x` or `&mut x` (x a name: a parameter or a local), a
#   closure by reference (`&mut || ..`, `&move || ..`: a stack temporary), or
#   a closure by value that is not `move` (`|..| ..`: its captures borrow
#   the texture's locals), of a call `leanrt::path::f(..)` needs every
#   `pub fn f` of the module's file (`runtime/leanrt/src/<first
#   segment>.rs`, lib.rs for `leanrt::f`) to be `#[inline(always)]`;
# - a method call `x.m(..)` or `(*x).m(..)` (x a name; a field's method
#   `x.f.m(..)` is not checked) of a method `m(&self ..)`
#   or `m(&mut self ..)` that leanrt defines (also in a trait's impl; unit
#   tests left out) needs each such definition to be `#[inline(always)]`.
#   Methods are matched by name: a std method of the same name counts as
#   leanrt's (a false alarm at worst).
# Not checked: a reference into a value or to a temporary (`&v[..]`,
# `x.as_slice()`, `&f(..)`), a heap address for a `Vec` or a handle's data
# but a stack slot for a Rust array (so a texture leaves such arrays to an
# out-of-line function: fs.rs's `owned::metadata`), a `move` closure by
# value (its captures are copies, passed in registers or by a pointer that
# does not escape), and calls into other crates (lean-runtime, reussir-rt,
# std).
#   tests/runtime/texture-escape-check.sh [CHECKOUT]
# CHECKOUT: the tree whose prelude and leanrt are checked (default: this
# one). Reads sources only; builds nothing.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=${1:-$(cd "$HERE/../.." && pwd)}
python3 - "$ROOT" <<'PY'
import os, re, sys
root = sys.argv[1]
src = open(f"{root}/runtime/prelude.rr").read()
base = f"{root}/runtime/leanrt/src"
rs = {}
for d, _, fs in os.walk(base):
    for f in fs:
        if f.endswith(".rs"):
            text = open(os.path.join(d, f)).read()
            # Unit tests (a `#[cfg(test)] mod`, at the end of a file) are not
            # what textures call.
            t = re.search(r"^#\[cfg\(test\)\]\s*mod ", text, re.M)
            rs[os.path.relpath(os.path.join(d, f), base)] = text[:t.start()] if t else text

def attrs(text, start):
    # The attributes right above a definition (doc comments skipped).
    out = []
    for l in reversed(text[:start].split("\n")[:-1]):
        s = l.strip()
        if s.startswith("#["):
            out.append(s.replace(" ", ""))
        elif not s.startswith("//"):
            break
    return out

def defs(name, files, method=False):
    res = []
    for f in files:
        # A free function is `pub`; a method may also be a trait impl's.
        vis = r"(?:pub(?:\([a-z]+\))? )?" if method else r"pub "
        for m in re.finditer(r"^[ \t]*" + vis + r"(?:unsafe )?(?:extern \"C\" )?fn " + re.escape(name) + r"\b[^{;]*(?=\{)", rs[f], re.M):
            if method and not re.search(r"\(\s*&(?:mut\s+)?self", m.group(0)):
                continue
            res.append((f, rs[f].count("\n", 0, m.start()) + 1, "#[inline(always)]" in attrs(rs[f], m.start())))
    return res

def textures():
    for m in re.finditer(r"\[\{", src):
        depth, i = 0, m.start()
        while i < len(src):
            if src.startswith("[{", i):
                depth += 1; i += 2
            elif src.startswith("}]", i):
                depth -= 1; i += 2
                if depth == 0:
                    break
            else:
                i += 1
        yield src.count("\n", 0, m.start()) + 1, src[m.end():i - 2]

def args(b, p):
    depth, q = 1, p
    while q < len(b) and depth:
        if b[q] in "([{": depth += 1
        elif b[q] in ")]}": depth -= 1
        q += 1
    parts, d, cur = [], 0, ""
    for ch in b[p:q - 1]:
        if ch in "([{": d += 1
        if ch in ")]}": d -= 1
        if ch == "," and d == 0:
            parts.append(cur.strip()); cur = ""
        else:
            cur += ch
    return parts + [cur.strip()]

bad, calls = [], 0
for line, b in textures():
    at = lambda m: line + b.count("\n", 0, m.start())
    for m in re.finditer(r"leanrt::((?:[a-z_0-9]+::)*)([a-z_0-9]+)(?:::<[^(]*?>)?\(", b):
        # `&x`, `&mut x`, a closure by reference (a stack temporary, `move`
        # or not), and a closure by value that is not `move` (its captures
        # are references to the texture's locals).
        refs = [" ".join(a.split())[:40] for a in args(b, m.end())
                if re.fullmatch(r"&(?:mut )?[a-z_][a-z_0-9]*", a) or re.match(r"&(?:mut )?(?:move )?\||\|", a)]
        if not refs:
            continue
        calls += 1
        mods = [x for x in m.group(1).split("::") if x]
        files = [f for f in ([mods[0] + ".rs"] if mods else ["lib.rs"]) if f in rs]
        ds = defs(m.group(2), files)
        if not ds or not all(d[2] for d in ds):
            where = ", ".join(f"{f}:{n}" for f, n, _ in ds) or "no definition found"
            bad.append(f"prelude.rr:{at(m)}: leanrt::{m.group(1)}{m.group(2)}({', '.join(refs)}, ..): not #[inline(always)] ({where})")
    for m in re.finditer(r"(?<![\w.])(\(\*[a-z_][a-z_0-9]*\)|[a-z_][a-z_0-9]*)\.([a-z_][a-z_0-9]*)\(", b):
        if m.group(1) in ("self", "std", "leanrt"):
            continue
        ds = defs(m.group(2), list(rs), method=True)
        if not ds:
            continue
        calls += 1
        if not all(d[2] for d in ds):
            where = ", ".join(f"{f}:{n}" for f, n, ok in ds if not ok)
            bad.append(f"prelude.rr:{at(m)}: {m.group(1)}.{m.group(2)}(): a leanrt method that is not #[inline(always)] ({where})")
for l in bad:
    print(l)
if bad:
    print(f"texture-escape-check: FAIL ({len(bad)} of {calls} calls lend a local to a function that may stay out of line)")
    sys.exit(1)
print(f"texture-escape-check: OK ({calls} calls that lend a texture's local, all inlined)")
PY
