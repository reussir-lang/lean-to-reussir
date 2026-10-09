#!/usr/bin/env bash
# A state machine's entry enum is a scalar, and a jump changes only the
# slots it fills (optimization `state-machines`; docs/implementation/
# control-flow/state-machines.md, "State machines entered without
# allocation"). Builds RtSmDecode (a table-driven decoder loop, J4 with
# three variants), RtStateMachines and RtJpSlots (state machines carrying
# values of many types) through lean2rr to LLVM IR (scripts/l2r.py --emit
# llvm-ir, with the .rr), and fails when
# - an entry enum (`enum <f>_mode`) whose variants are all nullary is not a
#   `[value]` enum: a shared enum's nullary variant is a pointer, and the
#   state machine loads its tag and tests its count at every entry
#   (per output byte of lean-zip's inflate loop);
# - the mode parameter of a state machine's function (`define ... @..._sm(`,
#   its last parameter) is a pointer in the IR, for such an enum;
# - in an arm of a state machine, a call of the state machine that enters
#   variant v passes, in a slot that v does not bind, anything other than a
#   placeholder (`l2r_zero_N()`, `l2r_str_shared_empty()`) or that slot
#   itself where the arm does not bind it: a live value there would be kept
#   alive across the jump (an array updated before it shared and copied at
#   every iteration, RF-1);
# - in an arm of a state machine, a call of the state machine passes a
#   placeholder in a slot that the arm does not bind: that slot already
#   holds a placeholder, and passing the slot itself keeps it in place (no
#   constant rebuilt, no release of the old one, at every iteration).
# It fails when the test is vacuous: no state machine in RtSmDecode, none
# whose arms pass a slot on, or an IR function of none of them. It then
# checks itself on mutations of RtSmDecode's .rr, each of which must fail:
# its entry enum made shared, one passed-on slot replaced by its
# placeholder, and one placeholder of a slot that the arm binds (and the
# target does not) replaced by the arm's live variable of that slot.
#   tests/runtime/sm-slots-check.sh
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/sm-slots-check
mkdir -p "$OUT"
cd "$OUT"
status=0
for t in RtSmDecode RtStateMachines RtJpSlots; do
  cp "$HERE/$t.lean" .
  lean -o "$t.olean" "$t.lean"
  if ! python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$OUT" --emit llvm-ir -o "$OUT/$t.ll" \
      --keep-rr "$OUT/$t.rr" > "$t.build.log" 2>&1; then
    echo "FAIL $t: build failed (see $OUT/$t.build.log)"; status=1; continue
  fi
  python3 - "$t" "$t.rr" "$t.ll" <<'PY' || status=1
import re, sys

name, rr_path, ll_path = sys.argv[1], sys.argv[2], sys.argv[3]
rr = open(rr_path).read()
ll = open(ll_path).read()
PLACEHOLDER = re.compile(r'^(l2r_zero_\d+|l2r_str_shared_empty)\(\)$')

def split_args(s, i):
    """The arguments of the call whose '(' is at s[i]; the index after ')'."""
    depth, cur, args, j = 0, '', [], i + 1
    while j < len(s):
        c = s[j]
        if c in '([{':
            depth += 1
        elif c in ')]}':
            if depth == 0:
                if cur.strip(): args.append(cur.strip())
                return args, j + 1
            depth -= 1
        if c == ',' and depth == 0:
            args.append(cur.strip()); cur = ''
        else:
            cur += c
        j += 1
    raise SystemExit(f'FAIL {name}: unbalanced call in the .rr')

def body_of(s, start):
    """The text of the block whose '{' is at s[start]."""
    depth, j = 0, start
    while j < len(s):
        if s[j] == '{': depth += 1
        elif s[j] == '}':
            depth -= 1
            if depth == 0: return s[start:j + 1]
        j += 1
    raise SystemExit(f'FAIL {name}: unbalanced block in the .rr')

def check(rr, ll, quiet=False):
    errs, nsm, npass, nll = [], 0, 0, 0
    enums = {}
    for m in re.finditer(r'^enum (\[value\] )?(\w+_mode) \{\n(.*?)^\}', rr, re.M | re.S):
        vs = [v.strip().rstrip(',') for v in m.group(3).splitlines() if v.strip()]
        enums[m.group(2)] = (bool(m.group(1)), all(re.fullmatch(r'\w+', v) for v in vs))
    for m in re.finditer(r'^fn (\w+)_sm\((.*?)\) -> [^{]*\{', rr, re.M):
        fn, params = m.group(1) + '_sm', [p.strip() for p in m.group(2).split(', ')]
        mode = params[-1].split(' : ')[1]
        if mode not in enums:
            continue
        value, nullary = enums[mode]
        if not nullary:
            continue
        nsm += 1
        if not value:
            errs.append(f'{fn}: entry enum {mode} has only nullary variants but is shared')
        # The IR: the function's last parameter is not a pointer.
        dm = re.search(r'^define [^@\n]*@_R\w*?\d+' + re.escape(fn) + r'\((.*)\)[^\n]*\{$', ll, re.M)
        if dm:
            nll += 1
            last = dm.group(1).rsplit(',', 1)[-1].strip()
            if last.startswith('ptr'):
                errs.append(f'{fn}: its mode parameter is a pointer in the IR ({last})')
        slots = [p.split(' : ')[0] for p in params[:-1]]
        body = body_of(rr, m.end() - 1)
        arms = list(re.finditer(r'^\s*' + re.escape(mode) + r'::(\w+) => \{', body, re.M))
        texts = {a.group(1): body[a.end():arms[k + 1].start() if k + 1 < len(arms) else len(body)]
                 for k, a in enumerate(arms)}
        # The slots each variant's arm binds (`let x : T = s;` at its top).
        binds = {v: set(re.findall(r'^\s*let \w+ : [^=]+ = (\w+);', t, re.M)) & set(slots)
                 for v, t in texts.items()}
        for u, text in texts.items():
            bound = binds[u]
            for c in re.finditer(re.escape(fn) + r'\(', text):
                args, _ = split_args(text, c.end() - 1)
                tm = re.fullmatch(re.escape(mode) + r'::(\w+)\{\}', args[-1]) if args else None
                if not tm or tm.group(1) not in binds:
                    errs.append(f'{fn}, arm {u}: a call whose last argument is not a variant of {mode}')
                    continue
                v = tm.group(1)
                for i, (s, arg) in enumerate(zip(slots, args)):
                    if s in binds[v]:
                        continue
                    # RF-1: v does not bind s, so only a placeholder may go there.
                    if not (PLACEHOLDER.match(arg) or (arg == s and s not in bound)):
                        errs.append(f'{fn}, arm {u}: slot {s} (argument {i}), which the target {v} '
                                    f'does not bind, gets {arg}, not a placeholder')
                    elif arg == s:
                        npass += 1
                    elif s not in bound:
                        errs.append(f'{fn}, arm {u}: slot {s} (argument {i}), which the arm '
                                    f'does not bind, gets the placeholder {arg} instead of itself')
    return errs, nsm, npass, nll

errs, nsm, npass, nll = check(rr, ll)
for e in errs[:20]:
    print(f'FAIL {name}: {e}')
if errs:
    sys.exit(1)
if name == 'RtSmDecode':
    if nsm == 0 or npass == 0 or nll == 0:
        print(f'FAIL {name}: vacuous ({nsm} state machines with nullary entry enums, '
              f'{npass} slots passed on, {nll} found in the IR)')
        sys.exit(1)
    # Mutations, each of which must fail.
    m = re.search(r'^enum \[value\] (\w+_mode) \{', rr, re.M)
    mut1 = rr[:m.start()] + 'enum ' + rr[m.start() + len('enum [value] '):]
    pm = re.search(r'^fn (\w+_sm)\((.*?)\)', rr, re.M)
    ph = re.search(r'\b(l2r_zero_\d+)\(\)', rr[pm.end():])
    first = pm.group(2).split(', ')[-2].split(' : ')[0]
    i = rr.find(', ' + first + ', ', pm.end())
    if i < 0: i = rr.find(', ' + first + ')', pm.end())
    mut2 = rr[:i] + ', ' + ph.group(1) + '()' + rr[i + 2 + len(first):] if ph and i >= 0 else None
    # RF-1: in an arm that binds slot sK to x (`let x : T = sK;`), the
    # first later call that gives sK a placeholder gets x instead.
    mut3 = None
    slots = [p.split(' : ')[0] for p in pm.group(2).split(', ')[:-1]]
    for b in re.finditer(r'let (\w+) : [^=]+ = (\w+);', rr[pm.end():]):
        if b.group(2) not in slots: continue
        k, pos = slots.index(b.group(2)), pm.end() + b.end()
        c = rr.find(pm.group(1) + '(', pos)
        if c < 0: continue
        args, e = split_args(rr, c + len(pm.group(1)))
        if k < len(args) and PLACEHOLDER.match(args[k]):
            args[k] = b.group(1)
            mut3 = rr[:c] + pm.group(1) + '(' + ', '.join(args) + ')' + rr[e:]
            break
    for what, mrr in (('entry enum made shared', mut1), ('a passed-on slot given a placeholder', mut2),
                      ('a live value in a slot that the target does not bind', mut3)):
        if mrr is None or not check(mrr, ll)[0]:
            print(f'FAIL {name}: the check does not catch a mutation ({what})')
            sys.exit(1)
print(f'ok {name}: {nsm} state machines with nullary entry enums, all [value]; {npass} slots passed on; {nll} in the IR')
PY
done
exit $status
