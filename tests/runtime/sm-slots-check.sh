#!/usr/bin/env bash
# A state machine's entry point is an integer, LLVM threads its loop, and a
# jump changes only the slots it fills (optimization `state-machines`;
# docs/implementation/control-flow/state-machines.md, "State machines
# entered without allocation"). Builds RtSmDecode (a table-driven decoder
# loop, J4 with three variants), RtStateMachines and RtJpSlots (state
# machines carrying values of many types) through lean2rr to LLVM IR
# (scripts/l2r.py --emit llvm-ir, with the .rr), and fails when
# - the entry point of a state machine whose variants are all nullary is an
#   enum (`enum <f>_mode`, shared or `[value]`), not an integer: a shared
#   enum's nullary variant is a pointer, whose tag the state machine loads
#   and whose count it tests at every entry (per output byte of lean-zip's
#   inflate loop), and a `[value]` enum is a struct in LLVM, which LLVM's
#   DFAJumpThreading does not follow through the loop's phi;
# - the match of such a state machine is not one arm per variant, the
#   literals 0, 1, ... in order, then a wildcard arm that is
#   `l2r_unreachable` at the function's result type;
# - its entry point (`define ... @..._sm(`, the last parameter) is not an
#   integer in the IR;
# - in RtSmDecode, LLVM did not thread the state machine's loop: its IR
#   function has no block of DFAJumpThreading (`<name>.jt<N>`), so every
#   jump goes through the `switch` at the loop's head;
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
# checks itself on mutations of RtSmDecode's .rr and IR, each of which must
# fail: its entry point made a `[value]` enum, one passed-on slot replaced
# by its placeholder, one placeholder of a slot that the arm binds (and the
# target does not) replaced by the arm's live variable of that slot, the
# wildcard arm taken away, the IR's entry point made a struct, and the
# IR's threaded blocks renamed.
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
INT = re.compile(r'^u(8|16|32|64)$')

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
    raise SystemExit(f'FAIL {name}: unbalanced call')

def block_end(s, start):
    """The index of the '}' closing the block whose '{' is at s[start]."""
    depth, j = 0, start
    while j < len(s):
        if s[j] == '{': depth += 1
        elif s[j] == '}':
            depth -= 1
            if depth == 0: return j
        j += 1
    raise SystemExit(f'FAIL {name}: unbalanced block in the .rr')

def match_arms(s, start):
    """The arms (pattern, block text) of the `match m { ... }` that is the
    body of the function whose '{' is at s[start]; None if it is not one."""
    m = re.compile(r'\{\s*match \w+ \{').match(s, start)
    if not m:
        return None
    j, arms = m.end(), []
    while True:
        while s[j] in ' \n,': j += 1
        if s[j] == '}':
            return arms
        k = s.index(' => ', j)
        b = k + len(' => ')
        if s[b] != '{':
            raise SystemExit(f'FAIL {name}: an arm without a block in the .rr')
        e = block_end(s, b)
        arms.append((s[j:k].strip(), s[b:e + 1]))
        j = e + 1

def ir_function(ll, fn):
    """The parameters (top-level split) and the body of fn's IR definition."""
    dm = re.search(r'^define [^@\n]*@_R\w*?\d+' + re.escape(fn) + r'\((.*)\)[^\n]*\{$', ll, re.M)
    if not dm:
        return None, None
    params, _ = split_args(dm.group(1) + ')', -1)
    end = ll.find('\n}\n', dm.end())
    return params, ll[dm.end():end]

def check(rr, ll, threaded):
    errs, nsm, npass, nll = [], 0, 0, 0
    enums = {}
    for m in re.finditer(r'^enum (\[value\] )?(\w+_mode) \{\n(.*?)^\}', rr, re.M | re.S):
        vs = [v.strip().rstrip(',') for v in m.group(3).splitlines() if v.strip()]
        enums[m.group(2)] = (bool(m.group(1)), all(re.fullmatch(r'\w+', v) for v in vs))
    for m in re.finditer(r'^fn (\w+)_sm\((.*?)\) -> ([^{]*?) \{', rr, re.M):
        fn, params, ret = m.group(1) + '_sm', [p.strip() for p in m.group(2).split(', ')], m.group(3)
        mode = params[-1].split(' : ')[1]
        if mode in enums:
            value, nullary = enums[mode]
            if nullary:
                errs.append(f'{fn}: its variants are all nullary, but its entry point is '
                            f'{"a [value]" if value else "a shared"} enum ({mode}), not an integer')
            continue
        if not INT.match(mode):
            continue
        nsm += 1
        # The IR: the entry point is an integer; RtSmDecode's loop is threaded.
        ps, body_ll = ir_function(ll, fn)
        if ps is not None:
            nll += 1
            if not re.match(r'i\d+\b', ps[-1]):
                errs.append(f'{fn}: its entry point is not an integer in the IR ({ps[-1]})')
            if threaded and not re.search(r'^[\w.$-]*\.jt\d+[\w.$-]*:', body_ll, re.M):
                errs.append(f'{fn}: LLVM did not thread its loop (no DFAJumpThreading block .jtN in the IR)')
        slots = [p.split(' : ')[0] for p in params[:-1]]
        arms = match_arms(rr, m.end() - 1)
        if arms is None:
            errs.append(f'{fn}: its body is not a match on its entry point'); continue
        pats = [p for p, _ in arms]
        n = len(pats) - 1
        if pats != [str(i) for i in range(n)] + ['_'] or n < 1:
            errs.append(f'{fn}: its arms are not 0..{n - 1} in order and a wildcard last ({", ".join(pats)})'); continue
        if arms[-1][1] != '{ l2r_unreachable<' + ret + '>() }':
            errs.append(f'{fn}: its wildcard arm is not l2r_unreachable<{ret}>() ({arms[-1][1][:80]})')
        texts = dict(arms[:-1])
        # The slots each variant's arm binds (`let x : T = s;` at its top).
        binds = {v: set(re.findall(r'^\s*let \w+ : [^=]+ = (\w+);', t, re.M)) & set(slots)
                 for v, t in texts.items()}
        for u, text in texts.items():
            bound = binds[u]
            for c in re.finditer(re.escape(fn) + r'\(', text):
                args, _ = split_args(text, c.end() - 1)
                v = args[-1] if args else None
                if v not in binds:
                    errs.append(f'{fn}, arm {u}: a call whose last argument is not one of its variants ({v})')
                    continue
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

threaded = name == 'RtSmDecode'
errs, nsm, npass, nll = check(rr, ll, threaded)
for e in errs[:20]:
    print(f'FAIL {name}: {e}')
if errs:
    sys.exit(1)
if name == 'RtSmDecode':
    if nsm == 0 or npass == 0 or nll == 0:
        print(f'FAIL {name}: vacuous ({nsm} state machines with an integer entry point, '
              f'{npass} slots passed on, {nll} found in the IR)')
        sys.exit(1)
    # Mutations, each of which must fail.
    pm = re.search(r'^fn (\w+_sm)\((.*?)\)', rr, re.M)
    ps = pm.group(2).split(', ')
    # The entry point a [value] enum of nullary variants (the form before).
    mut1 = (rr[:pm.start()] + 'enum [value] X_mode {\n    e,\n    j\n}\n\n' + rr[pm.start():pm.start(2)]
            + ', '.join(ps[:-1] + [ps[-1].split(' : ')[0] + ' : X_mode']) + rr[pm.end(2):])
    ph = re.search(r'\b(l2r_zero_\d+)\(\)', rr[pm.end():])
    first = ps[-2].split(' : ')[0]
    i = rr.find(', ' + first + ', ', pm.end())
    if i < 0: i = rr.find(', ' + first + ')', pm.end())
    mut2 = rr[:i] + ', ' + ph.group(1) + '()' + rr[i + 2 + len(first):] if ph and i >= 0 else None
    # RF-1: in an arm that binds slot sK to x (`let x : T = sK;`), the
    # first later call that gives sK a placeholder gets x instead.
    mut3 = None
    slots = [p.split(' : ')[0] for p in ps[:-1]]
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
    # The wildcard arm taken away.
    w = re.compile(r',\n\s*_ => \{ l2r_unreachable<[^\n]*>\(\) \}').search(rr, pm.end())
    mut4 = rr[:w.start()] + rr[w.end():] if w else None
    # The IR's entry point a struct, and its threaded blocks renamed.
    dm = re.search(r'^define [^@\n]*@_R\w*?\d+' + re.escape(pm.group(1)) + r'\((.*)\)[^\n]*\{$', ll, re.M)
    mut5 = mut6 = None
    if dm:
        irps, _ = split_args(dm.group(1) + ')', -1)
        reg = irps[-1].split()[-1]
        mut5 = ll[:dm.start(1)] + ', '.join(irps[:-1] + ['%X_mode ' + reg]) + ll[dm.end(1):]
        end = ll.find('\n}\n', dm.end())
        mut6 = ll[:dm.end()] + ll[dm.end():end].replace('.jt', '.nt') + ll[end:]
    for what, mrr, mll in (('entry point made a [value] enum', mut1, ll),
                           ('a passed-on slot given a placeholder', mut2, ll),
                           ('a live value in a slot that the target does not bind', mut3, ll),
                           ('the wildcard arm taken away', mut4, ll),
                           ('the IR entry point made a struct', rr, mut5),
                           ('the threaded blocks renamed', rr, mut6)):
        if mrr is None or mll is None or not check(mrr, mll, threaded)[0]:
            print(f'FAIL {name}: the check does not catch a mutation ({what})')
            sys.exit(1)
print(f'ok {name}: {nsm} state machines with an integer entry point; {npass} slots passed on; {nll} in the IR'
      + ('; the loop threaded' if threaded else ''))
PY
done
exit $status
