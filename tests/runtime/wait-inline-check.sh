#!/usr/bin/env bash
# The fast paths of lean-runtime's wait cores stay inline in generated code:
# builds RtWaitInline (a program that creates tasks, with a loop of
# reference operations and a loop forcing thunks) through lean2rr to an
# executable and reads its machine code (objdump), where the linker has
# made the thread-local accesses direct. It fails when the executable has a
# TLS descriptor or module relocation (`R_AARCH64_TLSDESC`, `TLS_DTPMOD`,
# x86-64's `TLSDESC`, `DTPMOD64`: a thread-local access the linker did not
# relax), and when, in the functions that hold the loops, a fast path is
# reached through a call: `bl`, a tail branch `b`, a conditional branch
# (`b.cond`, `cbz`, `cbnz`, `tbz`, `tbnz`) to another function, or a `blr`
# or an indirect tail branch `br` whose target the function loads from the
# GOT or builds with `adrp`/`add` (the other `blr`s and `br`s go through
# data, a closure or a vtable, and are counted only). The functions checked are those that hold the
# loops, wherever LLVM inlined them: every function that calls a reference
# operation's slow path (the prelude's `l2r_ref_wait` or
# `l2r_ref_take_mark`: `modify`'s take; when Reussir inlines these small
# textures (issue 36), their callers call lean-runtime's `ref_keyed::wait`,
# `take` or `wait_taken` directly, which count the same) and every function
# that calls a thunk force's slow path (leanrt's `thunk_wait_busy`), other
# than those helpers themselves; it fails when there are none of either kind. The fast
# paths:
# - a reference point (the prelude's `l2r_ref_read_point`,
#   `l2r_ref_write_point`, `l2r_ref_swap_point`; lean-runtime's
#   `ref_keyed::read_point`, `write_point`, `swap_point`), or the polling
#   point or the publication behind them (`ref_read`, `before_publish`,
#   `writers_point`; their out-of-line parts `ref_read_poll` and
#   `join_own_writers_slow` may be called);
# - a thunk's store (the prelude's `l2r_lcell_set`) or its wake of waiters
#   (the prelude's `l2r_thunk_done`, leanrt's `on_finish`, lean-runtime's
#   `done_keyed`; its out-of-line part `done_keyed_slow` may be called);
# - `__tls_get_addr`.
# Then it checks itself: the same check on a copy of the disassembly with a
# call to `l2r_ref_read_point` added to a reference function (`bl`), a
# conditional branch to `l2r_thunk_done` added to a thunk function, or a
# `blr` through `adrp`/`add` to the prelude's `l2r_thunk_done` (the
# executable's own function), and on a copy of the relocations with a
# `R_AARCH64_TLSDESC` line added (so a change of readelf's format cannot
# leave that criterion empty), must fail on each of the four.
#   tests/runtime/wait-inline-check.sh
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/wait-inline-check
mkdir -p "$OUT"
cd "$OUT"
t=RtWaitInline
cp "$HERE/$t.lean" .
lean -o "$t.olean" "$t.lean"
python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$OUT" -o "$OUT/$t" > "$t.build.log" 2>&1 \
  || { echo "FAIL $t: build failed (see $OUT/$t.build.log)"; exit 1; }
objdump -d --no-show-raw-insn "$OUT/$t" > "$t.dis"
readelf -rW "$OUT/$t" > "$t.relocs"
python3 - "$t.dis" "$t.relocs" <<'PY'
import copy, re, sys

dis, relocs = sys.argv[1], sys.argv[2]
funcs, addr_of, cur = {}, {}, None
for line in open(dis):
    m = re.match(r'^([0-9a-f]+) <(.*)>:$', line)
    if m:
        cur = m.group(2); funcs[cur] = []; addr_of[cur] = int(m.group(1), 16); continue
    if cur is not None:
        m = re.match(r'^\s+[0-9a-f]+:\s+(\S+)\s*(.*)$', line)
        if m:
            funcs[cur].append((m.group(1), m.group(2)))
name_at = {a: f for f, a in addr_of.items()}
# GOT slots the dynamic linker fills with a known address (R_*_RELATIVE:
# offset -> addend), and the TLS relocations the linker did not relax
def tls_relocs(lines):
    """The TLS descriptor and module relocations among readelf's lines."""
    out = []
    for line in lines:
        p = line.split()
        if len(p) >= 3 and re.match(r'^[0-9a-f]+$', p[0]) and re.search(r'TLSDESC|DTPMOD', p[2]):
            out.append(p[2])
    return out

reloc_lines = open(relocs).read().splitlines()
tls = tls_relocs(reloc_lines)
got = {}
for line in reloc_lines:
    p = line.split()
    if len(p) >= 4 and re.match(r'^[0-9a-f]+$', p[0]) and p[2].endswith('RELATIVE'):
        try:
            got[int(p[0], 16)] = int(p[3], 16)
        except ValueError:
            pass

COND = ('cbz', 'cbnz', 'tbz', 'tbnz')

def targets(f, body):
    """The functions f reaches by a call or branch (not inside itself), and
    the number of indirect calls whose target it cannot tell."""
    out, unknown, regs = set(), 0, {}
    for op, args in body:
        sym = re.search(r'<([^>+]*)', args)
        if op in ('bl', 'b', 'call', 'jmp') or op.startswith('b.') or op in COND:
            if sym and sym.group(1) != f:
                out.add(sym.group(1))
            regs.clear()
            continue
        m = re.match(r'(x\d+), ([0-9a-f]+)', args)
        if op == 'adrp' and m:
            regs[m.group(1)] = int(m.group(2), 16); continue
        m = re.match(r'(x\d+), (x\d+), #(0x[0-9a-f]+|\d+)$', args)
        if op == 'add' and m and m.group(2) in regs:
            regs[m.group(1)] = regs[m.group(2)] + int(m.group(3), 0); continue
        m = re.match(r'(x\d+), \[(x\d+), #(0x[0-9a-f]+|\d+)\]$', args)
        if op == 'ldr' and m and m.group(2) in regs:
            slot = regs[m.group(2)] + int(m.group(3), 0)
            if slot in got:
                regs[m.group(1)] = got[slot]
            else:
                regs.pop(m.group(1), None)
            continue
        if op in ('blr', 'br'):
            r = args.strip()
            if r in regs and regs[r] in name_at:
                out.add(name_at[regs[r]])
            else:
                unknown += 1
            continue
        m = re.match(r'(x\d+|w\d+)\b', args)
        if m:
            regs.pop('x' + m.group(1)[1:], None)
    return out, unknown

forbidden = re.compile(r'l2r_ref_(read|write|swap)_point|read_point|write_point|swap_point'
                       r'|ref_read(?!_poll)|before_publish|writers_point'
                       r'|l2r_lcell_set|l2r_thunk_done|on_finish|done_keyed(?!_slow)|__tls_get_addr')
helper = re.compile(r'l2r_ref_wait|l2r_ref_take_mark|thunk_wait_busy|lean_runtime|6leanrt')
groups = {"reference operations": re.compile(r'l2r_ref_wait|l2r_ref_take_mark'
                                             r'|ref_keyed4wait|ref_keyed4take|ref_keyed10wait_taken'),
          "thunk forces": re.compile(r'thunk_wait_busy')}

def check(funcs, quiet=False):
    """The failures found, and the functions checked by group."""
    failures, chosen = [], {}
    for what, anchor in groups.items():
        names = [f for f in funcs if not helper.search(f)
                 and any(anchor.search(c) for c in targets(f, funcs[f])[0])]
        chosen[what] = names
        if not names:
            failures.append(f"no function holds the {what}")
            continue
        bad = sorted({(f, c) for f in names for c in targets(f, funcs[f])[0] if forbidden.search(c)})
        for f, c in bad:
            failures.append(f"a fast path of the {what} is a call: {f} -> {c}")
        if not bad and not quiet:
            unknown = sum(targets(f, funcs[f])[1] for f in names)
            print(f"PASS  {what}: inline in {', '.join(names)} ({unknown} indirect calls through data)")
    return failures, chosen

status = 0
if tls:
    print(f"FAIL wait-inline-check: TLS relocations the linker did not relax: {sorted(set(tls))}")
    status = 1
failures, chosen = check(funcs)
for msg in failures:
    print(f"FAIL wait-inline-check: {msg}")
    status = 1

# The check on three mutations of the disassembly must fail on each.
done = next((f for f in funcs if re.search(r'l2r_thunk_done$', f)), None)
if status == 0 and done is not None and chosen["reference operations"] and chosen["thunk forces"]:
    ref_f, thunk_f = chosen["reference operations"][0], chosen["thunk forces"][0]
    a = addr_of[done]
    page, off = a & ~0xfff, a & 0xfff
    mutations = {
        "a bl to l2r_ref_read_point": (ref_f, [('bl', '0 <_RC18l2r_ref_read_point>')]),
        "a cbnz to l2r_thunk_done": (thunk_f, [('cbnz', f'w0, {a:x} <{done}>')]),
        "a blr through adrp/add to l2r_thunk_done": (thunk_f, [('adrp', f'x9, {page:x} <x>'),
                                                               ('add', f'x9, x9, #0x{off:x}'),
                                                               ('blr', 'x9')]),
    }
    for what, (f, extra) in mutations.items():
        mutated = copy.deepcopy(funcs)
        mutated[f] = extra + mutated[f]
        if not check(mutated, quiet=True)[0]:
            print(f"FAIL wait-inline-check: the check misses {what} added to {f}")
            status = 1
    fake = "000000000000  000000000407 R_AARCH64_TLSDESC                         0"
    if not tls_relocs(reloc_lines + [fake]):
        print("FAIL wait-inline-check: the check misses a R_AARCH64_TLSDESC relocation added to readelf's output")
        status = 1
    if status == 0:
        print(f"PASS  the check fails on each of {len(mutations) + 1} mutations")
elif status == 0:
    print("FAIL wait-inline-check: no function to mutate for the self-check")
    status = 1
if status == 0:
    print("PASS  wait-inline-check")
sys.exit(status)
PY
