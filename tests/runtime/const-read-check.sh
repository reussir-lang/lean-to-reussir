#!/usr/bin/env bash
# A constant read in a loop stays one load: builds RtConstReads (constants
# of every kind of once-cell read in loops: a startup table, a literal
# table, closed terms, a toolchain constant, a small scalar, 64-bit and
# 8-bit zeros, in a task too) through lean2rr to LLVM IR (scripts/l2r.py
# --emit llvm-ir, with the .rr) and fails when, on the hot path of a loop,
# there is
# - a call of a constant's accessor (a function whose body tests a
#   once-cell, `l2r_once_ready`: the accessor was not inlined);
# - a call of a once-cell texture that reads (`l2r_once_ready`, `_get`,
#   `_claim`, `_put`, `_has`, or its `_ffi` function): a texture LLVM did
#   not inline;
# - a call of a function of leanrt's `once` module (`claim`, `get_raw`,
#   `has`, ... not inlined), other than the standard streams' mutable-cell
#   operations (`take_raw`, `swap_raw`, `push_context`, `pop_context`, ...;
#   the task glue's loops move the streams' cells);
# - a load from leanrt's slot record `SLOTS` (a read through its vectors,
#   not through the tables at fixed addresses `FAST` and `FLAGS`).
# Symbols are recognized by their identifiers, whatever the mangling's
# prefix: each run of digits not preceded by a digit is read as a length
# and the identifier that follows (Rust's v0 scheme, which Reussir's
# symbols follow too: `_RC28l_IO_Error_toString___l2r_0_`,
# `_RNvNtCs..._6leanrt4once4FAST`).
# The blocks of a loop are those in a cycle of a function's control-flow
# graph; a block is on the hot path when a path from the function's entry
# reaches it without entering a cold block: one that ends in `unreachable`,
# calls the once-cell's slow paths (`claim_cold`, `unset`) or a panic, or is
# the "not set" side of a test of a flag loaded from `FLAGS` (`trunc f`,
# `icmp ne f, 0`, an or with such a test, and their negations). A test of a
# word from `FAST` alone marks no side cold: a word 0 may be a set slot's
# value (review PCR-05).
# It fails when the test is vacuous: no accessor in the .rr, no defined
# function of the IR whose identifier is a function of the .rr (the
# symbols are not read as expected), fewer than 6 distinct slots read from
# `FAST`. It then checks itself on mutations of the IR, with names taken
# from the IR's own symbols, each of which must fail: added to a hot loop
# block, a call of an accessor, a call of `l2r_once_claim`, a call of
# leanrt's `once::claim`, a load from `SLOTS`; added to the block where a
# constant whose word is 0 tests its flag, a call of an accessor, with the
# word's test as LLVM wrote it and written the other way (`icmp ne`,
# successors swapped).
# docs/implementation/startup/constants.md, "A read of a constant is one
# load".
#   tests/runtime/const-read-check.sh
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/const-read-check
mkdir -p "$OUT"
cd "$OUT"
t=RtConstReads
cp "$HERE/$t.lean" .
lean -o "$t.olean" "$t.lean"
python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$OUT" --emit llvm-ir -o "$OUT/$t.ll" \
  --keep-rr "$OUT/$t.rr" > "$t.build.log" 2>&1 \
  || { echo "FAIL $t: build failed (see $OUT/$t.build.log)"; exit 1; }
python3 - "$t.ll" "$t.rr" <<'PY'
import re, sys

ll_path, rr_path = sys.argv[1], sys.argv[2]
LABEL = r'(?:"[^"]+"|[A-Za-z0-9_.$\-]+)'
VAL = r'%' + LABEL
# Cold calls other than leanrt's once module's (read by identifier below).
COLD = re.compile(r'panic|index_bug|internal_panic')
TEXTURES = {f'l2r_once_{k}{s}' for k in ('ready', 'get', 'claim', 'put', 'has') for s in ('', '_ffi')}
ONCE_COLD = {'claim_cold', 'unset'}
ONCE_CELLS = {'take_raw', 'swap_raw', 'push_context', 'pop_context', 'swap_ctx_state', 'swap_cells',
              'enter_cells', 'note_mutable'}

def idents(sym):
    """The identifiers of a symbol: each run of digits not preceded by a
    digit, read as a length, and that many characters after it."""
    out = []
    for m in re.finditer(r'(?<![0-9])([1-9][0-9]*)', sym):
        n = int(m.group(1))
        out.append(sym[m.end():m.end() + n])
    return out

def once_item(sym):
    """The item of leanrt's `once` module a symbol names, or None."""
    ids = idents(sym)
    for i in range(len(ids) - 2):
        if ids[i] == 'leanrt' and ids[i + 1] == 'once':
            return ids[i + 2]
    return None

def callee(x):
    m = re.search(r'(?:call|invoke) [^@%]*@("[^"]+"|[A-Za-z0-9_.$]+)\(', x)
    return m.group(1).strip('"') if m else None

def globals_in(x):
    return [g.strip('"') for g in re.findall(r'@("[^"]+"|[A-Za-z0-9_.$]+)', x)]

def rr_functions():
    names, accs, cur = set(), set(), None
    for line in open(rr_path):
        m = re.match(r'fn ([A-Za-z0-9_]+)\(', line)
        if m:
            names.add(m.group(1))
            cur = m.group(1) if re.match(r'fn [A-Za-z0-9_]+\(\) -> ', line) else None
        elif cur and 'l2r_once_ready(' in line:
            accs.add(cur)
        if line.startswith('}'):
            cur = None
    return names, accs

def accessors():
    return rr_functions()[1]

def functions(lines):
    name, body = None, []
    for line in lines:
        if line.startswith('define '):
            m = re.search(r'@("?[^"( ]+"?)\(', line)
            name, body = m.group(1).strip('"'), []
        elif name is not None:
            if line.startswith('}'):
                yield name, body
                name = None
            else:
                body.append(line)

def blocks(body):
    out, cur, pending = [], ['%entry', []], None
    for line in body:
        m = re.match(r'^(' + LABEL + r'):', line)
        if m and not line.startswith(' '):
            out.append(cur)
            cur = ['%' + m.group(1).strip('"'), []]
            continue
        s = line.strip()
        if pending is not None:
            pending += ' ' + s
            if ']' in s:
                cur[1].append(pending)
                pending = None
            continue
        if not s or s.startswith(';'):
            continue
        if s.startswith('switch ') and ']' not in s:
            pending = s
            continue
        cur[1].append(s)
    out.append(cur)
    return [(b, i) for b, i in out if i]

def cycles(labels, edges):
    index, low, onstack, stack, res, n = {}, {}, set(), [], set(), [0]
    for root in labels:
        if root in index:
            continue
        work = [(root, iter(edges.get(root, ())))]
        index[root] = low[root] = n[0]; n[0] += 1
        stack.append(root); onstack.add(root)
        while work:
            v, it = work[-1]
            w = next(it, None)
            if w is not None:
                if w not in index:
                    index[w] = low[w] = n[0]; n[0] += 1
                    stack.append(w); onstack.add(w)
                    work.append((w, iter(edges.get(w, ()))))
                elif w in onstack:
                    low[v] = min(low[v], index[w])
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop(); onstack.discard(w); comp.append(w)
                    if w == v:
                        break
                if len(comp) > 1 or v in edges.get(v, ()):
                    res.update(comp)
    return res

def table_load(x):
    """('FAST'|'FLAGS'|'SLOTS', slot or offset, value) for a load from one of
    leanrt's once tables, else None."""
    m = re.match(r'(' + VAL + r') = load ', x)
    if not m:
        return None
    for g in globals_in(x):
        item = once_item(g)
        if item in ('FAST', 'FLAGS', 'SLOTS'):
            off = re.search(r'@"?' + re.escape(g) + r'"?, i64 (\d+)\)', x)
            k = int(off.group(1)) if off else 0
            return item, (k // 8 if item == 'FAST' else k), m.group(1)
    return None

def cold_blocks(bl):
    """Blocks that end in `unreachable` or call a cold function, and the
    "not set" sides of the tables' tests."""
    cold = set()
    for b, i in bl:
        if i[-1].startswith('unreachable'):
            cold.add(b)
        for x in i:
            c = callee(x)
            if c and (COLD.search(c) or once_item(c) in ONCE_COLD):
                cold.add(b)
    # unset[v] = b: when the i1 value v is b, the slot is not set. Only a
    # flag's test says so (its false side); a word's test alone never does
    # (a word 0 may be a set slot's value: that side is the hot path of a
    # constant whose bits are all 0, whichever way LLVM writes the test).
    # An or (logical or) is false only when its operands are: one flag
    # test's false side among them makes it a "not set" test; an and
    # likewise on its true side; xor with true negates.
    flag, unset = set(), {}
    for b, i in bl:
        for x in i:
            t = table_load(x)
            if t and t[0] == 'FLAGS':
                flag.add(t[2])
    changed = True
    while changed:
        changed = False
        for b, i in bl:
            for x in i:
                r = None
                m = re.match(r'(' + VAL + r') = trunc (?:nuw )?i8 (' + VAL + r') to i1', x)
                if m and m.group(2) in flag:
                    r = (m.group(1), False)
                m = re.match(r'(' + VAL + r') = icmp (eq|ne) i8 (' + VAL + r'), 0$', x)
                if m and m.group(3) in flag:
                    r = (m.group(1), m.group(2) == 'eq')
                m = re.match(r'(' + VAL + r') = (?:or (?:disjoint )?i1 (' + VAL + r'), (' + VAL + r')|select i1 (' + VAL + r'), i1 true, i1 (' + VAL + r'))', x)
                if m:
                    a, c = (m.group(2), m.group(3)) if m.group(2) else (m.group(4), m.group(5))
                    if unset.get(a) is False or unset.get(c) is False:
                        r = (m.group(1), False)
                m = re.match(r'(' + VAL + r') = (?:and i1 (' + VAL + r'), (' + VAL + r')|select i1 (' + VAL + r'), i1 (' + VAL + r'), i1 false)', x)
                if m:
                    a, c = (m.group(2), m.group(3)) if m.group(2) else (m.group(4), m.group(5))
                    if unset.get(a) is True or unset.get(c) is True:
                        r = (m.group(1), True)
                m = re.match(r'(' + VAL + r') = xor i1 (' + VAL + r'), true', x)
                if m and m.group(2) in unset:
                    r = (m.group(1), not unset[m.group(2)])
                if r and unset.get(r[0]) != r[1]:
                    unset[r[0]] = r[1]
                    changed = True
    for b, i in bl:
        m = re.match(r'br i1 (' + VAL + r'), label %(' + LABEL + r'), label %(' + LABEL + r')', i[-1])
        if m and m.group(1) in unset:
            cold.add('%' + (m.group(2) if unset[m.group(1)] else m.group(3)).strip('"'))
    return cold

def check(lines, accs):
    """Violations on hot loop paths, the slots read from FAST, a hot loop
    block (function, label)."""
    bad, fast_slots, a_hot_block = [], set(), None
    for name, body in functions(lines):
        bl = blocks(body)
        if not bl:
            continue
        ins = dict(bl)
        for b, i in bl:
            for x in i:
                t = table_load(x)
                if t and t[0] == 'FAST':
                    fast_slots.add(t[1])
        edges = {b: ['%' + x.strip('"') for x in re.findall(r'label %(' + LABEL + ')', i[-1])] for b, i in bl}
        edges = {b: [s for s in ss if s in ins] for b, ss in edges.items()}
        loop = cycles([b for b, _ in bl], edges)
        if not loop:
            continue
        cold = cold_blocks(bl)
        hot, work = set(), ([bl[0][0]] if bl[0][0] not in cold else [])
        while work:
            b = work.pop()
            if b in hot:
                continue
            hot.add(b)
            work += [s for s in edges.get(b, ()) if s not in cold and s not in hot]
        for b in sorted(loop & hot):
            if a_hot_block is None:
                a_hot_block = (name, b)
            for x in ins[b]:
                why = None
                c = callee(x)
                if c:
                    ids = set(idents(c))
                    item = once_item(c)
                    if ids & accs:
                        why = 'call of an accessor'
                    elif ids & TEXTURES:
                        why = 'call of a once-cell texture'
                    elif item is not None and item not in ONCE_CELLS:
                        why = f"call of leanrt's once::{item}"
                else:
                    t = table_load(x)
                    if t and t[0] == 'SLOTS':
                        why = 'load from SLOTS'
                if why:
                    bad.append(f'{name[:70]} {b}: {why}: {x[:120]}')
    return bad, fast_slots, a_hot_block

lines = open(ll_path).read().split('\n')
names, accs = rr_functions()
bad, fast_slots, hot_block = check(lines, accs)
status = 0
defined = [n for n, _ in functions(lines)]
known = {d: i for d in defined for i in idents(d) if i in names}
fast_sym = next((g for x in lines for g in globals_in(x) if once_item(g) == 'FAST'), None)
if not accs:
    print('FAIL RtConstReads: no accessor in the .rr (none tests a once-cell with l2r_once_ready)')
    status = 1
elif not known:
    print("FAIL RtConstReads: no function of the IR has a .rr function's name as an identifier: "
          'the symbols are not read as this check expects')
    status = 1
elif fast_sym is None:
    print("FAIL RtConstReads: the IR does not use leanrt's table FAST")
    status = 1
elif bad:
    print('FAIL RtConstReads: constant reads in loops that are not one load:')
    for x in bad[:40]:
        print('  ' + x)
    status = 1
elif len(fast_slots) < 6:
    print(f'FAIL RtConstReads: {len(fast_slots)} slots read from the fast table (at least 6 expected): '
          'the test no longer reads its constants through it')
    status = 1
else:
    print(f'PASS  RtConstReads ({len(accs)} accessors, {len(fast_slots)} slots read from the fast table)')
# Self-check: each mutation, with names taken from the IR's symbols, must
# be caught: four added to a hot loop block, and an accessor call added to
# the block where a constant whose word is 0 tests its flag, as LLVM wrote
# the word's test and with the test written the other way (`icmp ne`,
# successors swapped; review PCR-05).
def zero_word_block(lines):
    """(function, label of the flag's block, word test line, branch line)
    for a word test `icmp eq w, 0` whose true side, in a loop, loads a
    flag, or None."""
    for name, body in functions(lines):
        bl = blocks(body)
        ins = dict(bl)
        edges = {b: ['%' + x.strip('"') for x in re.findall(r'label %(' + LABEL + ')', i[-1])] for b, i in bl}
        edges = {b: [s for s in ss if s in ins] for b, ss in edges.items()}
        loop = cycles([b for b, _ in bl], edges)
        word, eq = set(), {}
        for b, i in bl:
            for x in i:
                t = table_load(x)
                if t and t[0] == 'FAST':
                    word.add(t[2])
                m = re.match(r'(' + VAL + r') = icmp eq i64 (' + VAL + r'), 0$', x)
                if m and m.group(2) in word:
                    eq[m.group(1)] = x
        for b, i in bl:
            m = re.match(r'br i1 (' + VAL + r'), label (%' + LABEL + r'), label (%' + LABEL + r')(.*)$', i[-1])
            if not m or m.group(1) not in eq:
                continue
            z = '%' + m.group(2)[1:].strip('"')
            if z in loop and any((table_load(x) or ('',))[0] == 'FLAGS' for x in ins.get(z, ())):
                return name, z, eq[m.group(1)], i[-1]
    return None

def mutate(lines, fn, blk, text, edits=()):
    mut, in_fn, done = [], False, False
    for line in lines:
        if in_fn:
            for old, new in edits:
                if line.strip() == old:
                    line = '  ' + new
        mut.append(line)
        if line.startswith('define ') and ('@' + fn + '(') in line.replace('"', ''):
            in_fn = True
            if blk == '%entry':
                mut.append(text); done = True
        elif in_fn and not done and re.match(r'^' + re.escape(blk[1:]) + r':', line.replace('"', '')):
            mut.append(text); done = True
        elif line.startswith('}'):
            in_fn = False
    return mut, done

if status == 0:
    def rename(sym, old, new):
        return re.sub(r'(?<![0-9])' + str(len(old)) + re.escape(old), str(len(new)) + new, sym, count=1)
    d, i = next(iter(known.items()))
    acc = sorted(accs)[0]
    acc_call = f'  %l2r_mut = tail call i64 @"{rename(d, i, acc)}"()'
    tex = next((g for x in lines for g in globals_in(x) if 'l2r_once_claim' in idents(g)), None)
    if hot_block is None:
        print('FAIL const-read-check: no hot loop block to mutate')
        status = 1
    fn, blk = hot_block or (None, None)
    mutations = [
        ('accessor call', fn, blk, acc_call, ()),
        ('l2r_once_claim call', fn, blk, tex and f'  %l2r_mut = tail call i1 @"{tex}"(i64 1)', ()),
        ('once::claim call', fn, blk, f'  %l2r_mut = tail call i1 @"{rename(fast_sym, "FAST", "claim")}"(i64 1)', ()),
        ('SLOTS load', fn, blk, f'  %l2r_mut = load i64, ptr getelementptr inbounds nuw (i8, ptr @"{rename(fast_sym, "FAST", "SLOTS")}", i64 40), align 8', ()),
    ]
    zw = zero_word_block(lines)
    if zw is None:
        print("FAIL const-read-check: no loop block where a word-0 constant's read tests its flag")
        status = 1
    else:
        zfn, zblk, icmp, br = zw
        m = re.match(r'br i1 (\S+), label (\S+), label (%[^, ]+)(.*)$', br)
        swapped = f'br i1 {m.group(1)}, label {m.group(3)}, label {m.group(2).rstrip(",")}{m.group(4)}'
        mutations += [
            ('accessor call in a word-0 flag block', zfn, zblk, acc_call, ()),
            ('accessor call in a word-0 flag block, word test as icmp ne', zfn, zblk, acc_call,
             ((icmp, icmp.replace('= icmp eq i64', '= icmp ne i64')), (br, swapped))),
        ]
    for what, f, b, text, edits in mutations:
        if status:
            break
        if not text:
            print(f'FAIL const-read-check: no symbol in the IR for the mutation "{what}"')
            status = 1
            break
        mut, done = mutate(lines, f, b, text, edits)
        bad2, _, _ = check(mut, accs)
        if not done or not bad2:
            print(f'FAIL const-read-check: a {what} ({f[:60]} {b}) was not caught')
            status = 1
if status == 0:
    print('PASS  const-read-check')
sys.exit(status)
PY
