#!/usr/bin/env bash
# Build and run the repros of the Reussir issues in reussir-bugs/ (one file
# per entry, NN-*.md; the index is reussir-bugs/README.md, whose Kind column
# says which issues are bugs and which are costs, missed optimizations or
# missing features) with one Reussir build.
#
#   reussir-bugs/repros/run.sh RRC_CHECKOUT [NN...]
#
# RRC_CHECKOUT is a Reussir checkout with a build: its build/bin/rrc compiles
# the repros, and plain .rr repros link against its build/target-rt/release.
# NN is an entry number (1, 02, ...); the default is every entry that has a
# line here: 1 to 4, 6 to 8, 12, 17, 18, 26 to 28 and 30 to 34 (numbers 5,
# 9, 11, 19 and 22 to 24 are retired). Entry 2's repros check the part of
# it that upstream fixed (a bounded stack depth). Entries 10 and 20 (missing features) have
# no repro: their patches carry their own tests; 13 needs a 32-bit target,
# 14 MLIR written by hand, 15 is shown by lean2rr's runtime test
# RtArenaPurge, and 21's patch has a lit test that shows it; 25 and 29 are
# shown by lean2rr's driver and its tests. Entries 28 and 30 to 34 need the
# checkout's reussir-opt (a build with the tests on, or its target
# reussir-opt); without it, SKIPPED. Each repro prints one line:
#
#   issue NN  REPRODUCES  the documented behaviour (the bug, the cost, ...)
#                         was seen
#   issue NN  FIXED       the expected output was seen
#   issue NN  OTHER       something else (shown)
#   issue NN  SKIPPED     a tool is missing (shown)
#   issue NN  SHOWN       a rule of the base that is no bug: the output the
#                         entry documents was seen (02's nested drop run)
#
# followed by what was seen and the rrc flags the repro needs.
#
# Plain .rr repros are built with rrc alone (--emit executable plus the
# polymorphic-FFI directories, as scripts/l2r.py passes them). Entry 2's
# Lean repro goes through scripts/l2r.py with L2R_REUSSIR set to the
# checkout; it needs the Lean toolchain lean2rr/lean-toolchain pins (or
# L2R_LEAN_TOOLCHAIN; put first on PATH by scripts/toolchain.sh) and a
# lean2rr build (`lake build` in lean2rr/, or L2R_LEAN2RR). l2r.py builds
# the runtime crate leanrt for the checkout once, under runtime/leanrt/target/.
# Entries 3 and 4 compare the sizes of two outputs (--emit mlir-llvm,
# --emit mlir); entries 6 and 17 read their LLVM IR (the
# calls left, the stack slots left), entry 18 its aarch64 assembly (stores
# through x8), entry
# 28 the exit status of two passes on a generated MLIR function, entries
# 30, 31, 32 and 34 the shape of the MLIR after one pass, entry 33 whether
# a pass crashes (entries 28 and 30 to 34 need the checkout's
# reussir-opt, in build/bin or build-tests/bin);
# entries 26 and 27 link a C driver that prints what the program saw
# (entry 27 on aarch64 only, a few seconds); entry 8
# counts the cells its program allocates (Reussir's allocation entry points
# wrapped at link time); entry 12 is a Rust test of the checkout's runtime
# sources, compiled with RUSTC. Everything takes seconds, except entry 2's
# Lean repro (a first .lean build also builds leanrt).
#
# Environment:
#   WORK    scratch directory (default: a new one under /tmp); rrc writes
#           reussir_rust_module_* files into its working directory, so every
#           build runs in WORK/run
#   RUSTC   the rustc that built Reussir's runtime (default: the toolchain
#           named in RRC_CHECKOUT/rust-toolchain.toml, else the one l2r.py
#           uses)
#   QUICK=1 skip the slow repros (none since 2026-10-19; kept for old callers)
set -u
# rrc's texture cache: a new, empty store for each run (set below, once
# WORK is known), and none that outlives a build for the Lean repros
# (L2R_POLYFFI_CACHE empty, scripts/l2r.py). rrc has no switch that turns
# its cache off, and the key of an entry is the rustc path, the texture and
# the paths of the library directories, not their bytes: with the user's
# store (~/.cache/rrc), a checkout whose runtime was rebuilt in place would
# get the textures of its older build, and rrc's time and memory would
# depend on what the store holds.
export L2R_POLYFFI_CACHE=

usage() { sed -n '2,/^set -u/p' "$0" | sed 's/^# \{0,1\}//; /^set -u/d'; exit 2; }
[ $# -ge 1 ] || usage
case "$1" in -h|--help) usage ;; esac

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
CK=$(cd "$1" && pwd) || exit 2
shift
RRC=$CK/build/bin/rrc
RT=$CK/build/target-rt/release
[ -x "$RRC" ] || { echo "no rrc at $RRC" >&2; exit 2; }

if [ -z "${RUSTC:-}" ]; then
    ch=$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$CK/rust-toolchain.toml" 2>/dev/null)
    [ -n "$ch" ] && RUSTC=$(rustup which --toolchain "$ch" rustc 2>/dev/null)
    [ -n "${RUSTC:-}" ] || RUSTC=$HOME/.rustup/toolchains/nightly-2026-08-31-aarch64-unknown-linux-gnu/bin/rustc
fi
TL=$("$RUSTC" --print target-libdir) || { echo "cannot run $RUSTC" >&2; exit 2; }
export L2R_RUSTC=$RUSTC

WORK=${WORK:-$(mktemp -d /tmp/reussir-bugs.XXXXXX)}
mkdir -p "$WORK/run" "$WORK/out" "$WORK/lean"
WORK=$(cd "$WORK" && pwd)
rm -rf "$WORK/cache"
mkdir -p "$WORK/cache/config"
export XDG_CACHE_HOME=$WORK/cache XDG_CONFIG_HOME=$WORK/cache/config
echo "rrc: $RRC"
echo "work: $WORK"
ulimit -c 0

LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
L2R_FLAGS="-O aggressive --no-pack-record-members --reuse-across-call --drop-order backward"

say_line() { # STATUS NN TEXT FLAGS
    printf 'issue %-4s %-11s %s' "$2" "$1" "$3"
    [ -n "${4:-}" ] && printf '   [%s]' "$4"
    printf '\n'
}

# rr SRC OUT FLAGS...: build a plain repro (SRC relative to this directory,
# or a generated file); sets RC (rrc's exit status), rrc's output in OUT.log.
# (The braces keep bash's "Segmentation fault" notices out of the report.)
rr() {
    local src=$1 out=$WORK/out/$2; shift 2
    case $src in /*) ;; *) src=$HERE/$src ;; esac
    { (cd "$WORK/run" && "$RRC" "$src" -o "$out" --emit executable \
        --polyffi-rust-path "$RUSTC" --polyffi-libdir "$RT" --polyffi-libdir "$RT/deps" \
        --polyffi-libdir "$TL" "$@") > "$out.log" 2>&1; } 2> /dev/null
    RC=$?
}
# timed CMD...: run CMD, set SECS (wall time)
timed() {
    local t0 t1
    t0=$(date +%s.%N); "$@"; t1=$(date +%s.%N)
    SECS=$(printf '%.1f' "$(echo "$t1 - $t0" | bc)")
}
# exe OUT ARGS...: run a built repro (60 s limit); sets OUT_TXT, ERR_TXT, EXIT
exe() {
    local b=$WORK/out/$1; shift
    { (cd "$WORK/run" && timeout 60 "$b" "$@") > "$b.stdout" 2> "$b.stderr"; } 2> /dev/null
    EXIT=$?
    OUT_TXT=$(head -c 300 "$b.stdout" | tr '\n' ' ' | sed 's/ *$//')
    ERR_TXT=$(grep -m1 -o "overflowed its stack\|Stack overflow\|Segmentation fault\|AddressSanitizer.*" "$b.stderr")
}
signame() { case $1 in 124) echo "timeout";; 134) echo "SIGABRT";; 136) echo "SIGFPE";; 137) echo "SIGKILL";; 139) echo "SIGSEGV";; *) echo "exit $1";; esac; }
build_fail() { echo "rrc $(signame "$RC"): $(grep -m1 -o "error[:=].\{0,160\}" "$WORK/out/$1.log")"; }
ratio() { echo "scale=2; $1 / $2" | bc; }
ge() { [ "$(echo "$1 >= $2" | bc)" = 1 ]; }
le() { [ "$(echo "$1 <= $2" | bc)" = 1 ]; }

# plain_value BUG NAME EXPECTED BAD FLAGS: build, run, compare one output line
plain_value() {
    local bug=$1 name=$2 exp=$3 bad=$4; shift 4
    rr "$name.rr" "$bug" "$@"
    if [ $RC != 0 ]; then say_line OTHER "$bug" "$(build_fail "$bug")" "$*"; return; fi
    exe "$bug"
    if [ "$OUT_TXT" = "$exp" ] && [ $EXIT = 0 ]; then say_line FIXED "$bug" "prints $OUT_TXT" "$*"
    elif [ -n "$bad" ] && [ "$OUT_TXT" = "$bad" ]; then say_line REPRODUCES "$bug" "prints $OUT_TXT, expected $exp" "$*"
    else say_line OTHER "$bug" "prints '$OUT_TXT' ($(signame $EXIT)), expected $exp" "$*"; fi
}

# A Reussir checkout as l2r.py sees it, whose rrc records its own time and
# peak memory in $RRC_STATS (lean2rr's memory would hide rrc's otherwise).
# It lives next to l2r.py's leanrt builds (ignored by git), so that leanrt is
# built once per checkout, not once per WORK.
WRAP=$ROOT/runtime/leanrt/target/run-sh/checkout-$(echo "$CK" | sha256sum | cut -c1-12)
mkdir -p "$WRAP/build/bin"
ln -sfn "$CK/build/target-rt" "$WRAP/build/target-rt"
# l2r.py checks the checkout's runtime sources for the patches it requires,
# and builds the interface of its core package (`Nat` and `Int`).
ln -sfn "$CK/crates" "$WRAP/crates"
ln -sfn "$CK/lib" "$WRAP/lib"
ln -sfn "$CK/library" "$WRAP/library"
cat > "$WRAP/build/bin/rrc" <<EOF
#!/bin/sh
exec /usr/bin/time -a -o "\${RRC_STATS:-/dev/null}" -f "%e %M" "$RRC" "\$@"
EOF
chmod +x "$WRAP/build/bin/rrc"

# lean_build FILE.lean MOD OUT [l2r.py flags]: compile a Lean file and build it with
# lean2rr; sets RC, and RSECS/RKB (rrc's time and peak KB, last run)
have_lean() {
    command -v lean > /dev/null || { echo "lean not on PATH"; return 1; }
    [ -x "$LEAN2RR" ] || { echo "no lean2rr build at $LEAN2RR"; return 1; }
    [ -x /usr/bin/time ] || { echo "no /usr/bin/time"; return 1; }
}
lean_build() {
    local src=$1 mod=$2 out=$WORK/out/$3; shift 3
    cp "$src" "$WORK/lean/$mod.lean"
    (cd "$WORK/lean" && lean -o "$mod.olean" "$mod.lean") > "$out.log" 2>&1 || { RC=1; return; }
    rm -f "$out.stats"
    (cd "$WORK/run" && RRC_STATS=$out.stats L2R_REUSSIR=$WRAP L2R_LEAN2RR=$LEAN2RR \
        python3 "$ROOT/scripts/l2r.py" "$mod" -o "$out" --lean-path "$WORK/lean" "$@") >> "$out.log" 2>&1
    RC=$?
    read -r RSECS RKB < <(tail -1 "$out.stats" 2>/dev/null) || true
    RSECS=$(printf '%.0f' "${RSECS:-0}")
}

bug01() {
    rr bug01-phantom-reuse-donor.rr 01 $L2R_FLAGS
    if [ $RC != 0 ]; then say_line OTHER 01 "$(build_fail 01)" "$L2R_FLAGS"; return; fi
    exe 01
    local r
    r=$(sed -n 's/^100003 100003 ratio \([0-9.]*\)$/\1/p' "$WORK/out/01.stdout")
    if [ -z "$r" ]; then say_line OTHER 01 "prints '$OUT_TXT'" "$L2R_FLAGS"
    elif ge "$r" 3; then say_line REPRODUCES 01 "insert returning t is ${r}x the rebuilding insert" "$L2R_FLAGS"
    elif le "$r" 1.6; then say_line FIXED 01 "insert returning t is ${r}x the rebuilding insert" "$L2R_FLAGS"
    else say_line OTHER 01 "time ratio $r (between 1.6 and 3)" "$L2R_FLAGS"; fi
}
bug02() {
    rr bug02-long-list-drop.rr 02 $L2R_FLAGS
    if [ $RC != 0 ]; then say_line OTHER 02 "$(build_fail 02)" "$L2R_FLAGS"; else
        local s
        for s in "0 list" "1 snoc" "2 lspine"; do
            set -- $s
            exe 02 "$1" 1000000
            if [ "$OUT_TXT" = 1000000 ]; then say_line FIXED "02" "$2, 1M cells, 8 MB stack: prints 1000000" "$L2R_FLAGS"
            elif [ -n "$ERR_TXT" ] || [ $EXIT -ge 128 ]; then say_line REPRODUCES "02" "$2, 1M cells, 8 MB stack: $ERR_TXT ($(signame $EXIT))" "$L2R_FLAGS"
            else say_line OTHER "02" "$2, 1M cells: '$OUT_TXT' ($(signame $EXIT))" "$L2R_FLAGS"; fi
        done
    fi
    bug02r
    bug02n
    local why
    if ! why=$(have_lean); then say_line SKIPPED "02" "lean2rr repro: $why"; return; fi
    lean_build "$HERE/bug02-long-list-drop.lean" LongDrop 02l
    if [ $RC != 0 ]; then say_line OTHER "02" "lean2rr build failed (see $WORK/out/02l.log)"; return; fi
    local c exp what
    for c in 0 1; do
        if [ $c = 0 ]; then exp="(some 7)"; what="List.replicate"; else exp=0; what=snoc; fi
        exe 02l $c 40000000
        if [ "$OUT_TXT" = "$exp" ]; then say_line FIXED 02 "lean2rr $what, 40M cells, 1 GiB stack: prints $OUT_TXT" "l2r.py"
        elif [ -n "$ERR_TXT" ] || [ $EXIT -ge 128 ]; then say_line REPRODUCES 02 "lean2rr $what, 40M cells, 1 GiB stack: $ERR_TXT ($(signame $EXIT))" "l2r.py"
        else say_line OTHER 02 "lean2rr $what, 40M cells: '$OUT_TXT' ($(signame $EXIT))" "l2r.py"; fi
    done
}
bug02r() {
    # Not a bug: a rule of upstream's drop scopes that entry 02 documents.
    # A drop that user code starts inside a running drop scope is a scope
    # of its own and finishes before it returns (`1 2`: the tree's tag
    # before the record's later member), where the record's own FFI release
    # joins the running scope (`2 1`, last member first). The same on
    # pristine upstream and on the series; the base before upstream's scoped
    # worklists printed `2 1` twice.
    local got
    rr bug02-nested-run-order.rr 02r -O aggressive --drop-order backward
    if [ $RC != 0 ]; then say_line OTHER 02 "$(build_fail 02r)" "-O aggressive --drop-order backward"; return; fi
    exe 02r
    got=$(echo "$OUT_TXT" | tr -s ' ')
    if [ "$got" = "1 2 2 1" ] && [ $EXIT = 0 ]; then say_line SHOWN 02 "a drop run started inside a drop scope finishes first (1 2); the FFI release joins the scope (2 1)" "-O aggressive --drop-order backward"
    else say_line OTHER 02 "nested drop run: prints '$got' ($(signame $EXIT)), expected '1 2 2 1'" "-O aggressive --drop-order backward"; fi
}
bug02n() {
    rr bug02-nullable-chain-drop.rr 02n -O default
    if [ $RC != 0 ]; then say_line OTHER 02 "$(build_fail 02n)" "-O default"; return; fi
    exe 02n
    if [ "$OUT_TXT" = 1 ] && [ $EXIT = 0 ]; then say_line FIXED 02 "1M links through Nullable, 8 MB stack: prints 1" "-O default"
    elif [ -n "$ERR_TXT" ] || [ $EXIT -ge 128 ]; then say_line REPRODUCES 02 "1M links through Nullable, 8 MB stack: ${ERR_TXT:-stack overflow} ($(signame $EXIT))" "-O default"
    else say_line OTHER 02 "prints '$OUT_TXT' ($(signame $EXIT)), expected 1" "-O default"; fi
}
bug03() {
    # The size of the LLVM-dialect module at K and K + 2: 4x when the copy
    # of the [value] record is expanded exponentially.
    local k lines=()
    for k in 8 10; do
        python3 "$HERE/bug03-value-record-dag.py" $k "$WORK/out/03-$k.rr"
        { (cd "$WORK/run" && "$RRC" "$WORK/out/03-$k.rr" -o "$WORK/out/03-$k.mlir" --emit mlir-llvm -O default \
            --polyffi-rust-path "$RUSTC" --polyffi-libdir "$RT" --polyffi-libdir "$RT/deps" \
            --polyffi-libdir "$TL") > "$WORK/out/03-$k.log" 2>&1; } 2> /dev/null
        RC=$?
        if [ $RC != 0 ]; then say_line OTHER 03 "K = $k: $(build_fail 03-$k)" "-O default"; return; fi
        lines+=("$(wc -l < "$WORK/out/03-$k.mlir")")
    done
    local r msg
    r=$(ratio "${lines[1]}" "${lines[0]}")
    msg="--emit mlir-llvm: K = 8: ${lines[0]} lines, K = 10: ${lines[1]} lines (${r}x for two more levels)"
    if ge "$r" 3; then say_line REPRODUCES 03 "$msg" "-O default"
    elif le "$r" 1.6; then say_line FIXED 03 "$msg" "-O default"
    else say_line OTHER 03 "$msg" "-O default"; fi
}
bug04() {
    # The size of the printed module at K and K + 2: 4x when exponential.
    local k sz=()
    for k in 10 12; do
        python3 "$HERE/bug04-emit-mlir-size.py" $k "$WORK/out/04-$k.rr"
        { (cd "$WORK/run" && "$RRC" "$WORK/out/04-$k.rr" --emit mlir -o "$WORK/out/04-$k.mlir") > "$WORK/out/04-$k.log" 2>&1; } 2> /dev/null
        RC=$?
        if [ $RC != 0 ]; then say_line OTHER 04 "K = $k: $(build_fail 04-$k)"; return; fi
        sz+=("$(stat -c %s "$WORK/out/04-$k.mlir")")
    done
    local r msg
    r=$(ratio "${sz[1]}" "${sz[0]}")
    msg="--emit mlir: K = 10: $((sz[0] / 1024)) KB, K = 12: $((sz[1] / 1024)) KB (${r}x for two more levels)"
    if ge "$r" 3; then say_line REPRODUCES 04 "$msg"
    elif le "$r" 1.5; then say_line FIXED 04 "$msg"
    else say_line OTHER 04 "$msg"; fi
}
bug06() {
    # The textures built as scripts/l2r.py builds them: for the CPU rrc
    # compiles for (NATIVE_FLAGS), else LLVM inlines no texture at all
    # (conflicting target features). Two call sites of `mix`: an ordinary
    # one in `main`, a cold one in `deep`.
    local d=$WORK/out/06 n
    mkdir -p "$d"
    printf '#!/bin/sh\nexec "%s" "$@" -C target-cpu=native -C target-feature=-outline-atomics\n' "$RUSTC" > "$d/rustc"
    chmod +x "$d/rustc"
    { (cd "$WORK/run" && "$RRC" "$HERE/bug06-trampoline-inline.rr" -o "$d/out.ll" --emit llvm-ir -O aggressive \
        --polyffi-rust-path "$d/rustc" --polyffi-libdir "$RT" --polyffi-libdir "$RT/deps" --polyffi-libdir "$TL") > "$d/log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER 06 "rrc $(signame "$RC"): $(grep -m1 -o "error[:=].\{0,160\}" "$d/log")" "-O aggressive"; return; fi
    n=$(grep -c 'call [^@]*@_RC3mix(' "$d/out.ll")
    if [ "$n" = 1 ]; then say_line REPRODUCES 06 "the cold call site still calls the trampoline of mix; main's call is inlined" "-O aggressive"
    elif [ "$n" = 0 ]; then say_line FIXED 06 "both calls of mix inlined" "-O aggressive"
    else say_line OTHER 06 "$n calls of mix left (expected 1, or 0 when fixed)" "-O aggressive"; fi
}
bug07() {
    rr bug07-tagged-top-bits.rr 07 -O aggressive
    if [ $RC != 0 ]; then say_line OTHER 07 "$(build_fail 07)" "-O aggressive"; return; fi
    exe 07
    if [ "$OUT_TXT" = 143 ] && [ $EXIT = 0 ]; then say_line FIXED 07 "a tagged handle with top bits copied in line: prints 143" "-O aggressive"
    elif [ $EXIT -ge 128 ]; then say_line REPRODUCES 07 "a tagged handle with top bits copied in line: killed by $(signame $EXIT)" "-O aggressive"
    else say_line OTHER 07 "prints '$OUT_TXT' ($(signame $EXIT)), expected 143" "-O aggressive"; fi
}
bug08() {
    # The cells allocated by bump (the rebuilt cell gets the original head)
    # and by bump_b (it gets the value the opaque identity returned),
    # counted by wrapping Reussir's allocation entry points at link time.
    local fl="$L2R_FLAGS --link-arg=-Wl,--wrap=__reussir_allocate,--wrap=__reussir_allocate_small"
    rr bug08-alias-release-donor.rr 08 $fl
    if [ $RC != 0 ]; then say_line OTHER 08 "$(build_fail 08)" "$L2R_FLAGS"; return; fi
    exe 08
    local a1 a2 b1 b2
    read -r a1 a2 b1 b2 < <(sed -n 's/^bump \([0-9]*\) \([0-9]*\) bump_b \([0-9]*\) \([0-9]*\)$/\1 \2 \3 \4/p' "$WORK/out/08.stdout")
    if [ -z "${b2:-}" ]; then say_line OTHER 08 "prints '$OUT_TXT' ($(signame $EXIT))" "$L2R_FLAGS"
    elif [ "$b1" = 0 ] && [ "$b2" = 0 ] && [ $((a2 - a1)) -ge 30000 ]; then
        say_line REPRODUCES 08 "bump allocates $a1 cells for 1000 bumps, $a2 for 4000 (bump_b: $b1, $b2)" "$L2R_FLAGS"
    elif [ "$a1" = 0 ] && [ "$a2" = 0 ] && [ "$b1" = 0 ] && [ "$b2" = 0 ]; then
        say_line FIXED 08 "no cell allocated by either bump" "$L2R_FLAGS"
    else say_line OTHER 08 "prints '$OUT_TXT'" "$L2R_FLAGS"; fi
}
bug12() {
    # A Rust test of the checkout's reussir-rt sources (nullable.rs, rc.rs),
    # linked as rt/ next to a copy of the repro.
    local d=$WORK/out/12 fails
    mkdir -p "$d"
    cp "$HERE/bug12-nullable-as-ref.rs" "$d/"
    ln -sfn "$CK/crates/reussir-rt/src" "$d/rt"
    { "$RUSTC" --edition 2021 --test "$d/bug12-nullable-as-ref.rs" -o "$d/t" > "$d/log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER 12 "rustc $(signame "$RC"): $(grep -m1 -o "error.\{0,160\}" "$d/log")"; return; fi
    # Only the repro's two tests (`as_ref_*`), not the modules' own.
    { (cd "$d" && timeout 60 ./t --test-threads=1 as_ref_) > "$d/out" 2>&1; } 2> /dev/null
    if grep -q '^test result: ok. 2 passed' "$d/out"; then say_line FIXED 12 "Nullable::as_ref: both tests pass"
    elif fails=$(sed -n 's/^test result: FAILED. [0-9]* passed; \([0-9]*\) failed.*/\1/p' "$d/out") && [ -n "$fails" ]; then
        say_line REPRODUCES 12 "Nullable::as_ref: $fails of 2 tests fail (the reference points to a dead copy)"
    else say_line OTHER 12 "$(tail -1 "$d/out")"; fi
}
bug17() {
    # The LLVM IR of two functions that pass a two-field [value] struct out
    # of an `if`: f_bn with a bool before a u64, f_nb with the bool last.
    local d=$WORK/out/17 n m
    mkdir -p "$d"
    { (cd "$WORK/run" && "$RRC" "$HERE/bug17-padded-member-widening.rr" -o "$d/out.ll" --emit llvm-ir -O aggressive \
        --no-pack-record-members) > "$d/log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER 17 "rrc $(signame "$RC"): $(grep -m1 -o "error[:=].\{0,160\}" "$d/log")" "-O aggressive --no-pack-record-members"; return; fi
    n=$(awk '/^define .*@_RC4f_bn\(/{p=1} p && /= alloca/{c++} p && /^}/{exit} END{print c+0}' "$d/out.ll")
    m=$(awk '/^define .*@_RC4f_nb\(/{p=1} p && /= alloca/{c++} p && /^}/{exit} END{print c+0}' "$d/out.ll")
    if [ "$m" != 0 ]; then say_line OTHER 17 "f_nb keeps $m stack slots (expected 0)" "-O aggressive --no-pack-record-members"
    elif [ "$n" -gt 0 ]; then say_line REPRODUCES 17 "f_bn (bool before u64) keeps $n stack slots for its bool; f_nb (bool last) none" "-O aggressive --no-pack-record-members"
    else say_line FIXED 17 "neither function keeps a stack slot" "-O aggressive --no-pack-record-members"; fi
}

bug18() {
    # The aarch64 assembly of two functions that return a two-field [value]
    # struct: f1's (u64, bool) has tail padding, f2's (u64, u64) none.
    local d=$WORK/out/18 n m
    mkdir -p "$d"
    { (cd "$WORK/run" && "$RRC" "$HERE/bug18-tail-padding-return.rr" -o "$d/out.s" --emit asm -O aggressive \
        --no-pack-record-members) > "$d/log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER 18 "rrc $(signame "$RC"): $(grep -m1 -o "error[:=].\{0,160\}" "$d/log")" "-O aggressive --no-pack-record-members"; return; fi
    if ! grep -q '^_RC2f1:' "$d/out.s"; then say_line SKIPPED 18 "no f1 in the assembly (not an aarch64 build?)"; return; fi
    n=$(awk '/^_RC2f1:/{p=1} p && /\[x8/{c++} p && /\.Lfunc_end/{exit} END{print c+0}' "$d/out.s")
    m=$(awk '/^_RC2f2:/{p=1} p && /\[x8/{c++} p && /\.Lfunc_end/{exit} END{print c+0}' "$d/out.s")
    if [ "$m" != 0 ]; then say_line OTHER 18 "f2 stores $m times through x8 (expected 0)" "-O aggressive --no-pack-record-members"
    elif [ "$n" -gt 0 ]; then say_line REPRODUCES 18 "f1 (u64, bool) returns in memory ($n stores through x8); f2 (u64, u64) in registers" "-O aggressive --no-pack-record-members"
    else say_line FIXED 18 "both functions return in registers" "-O aggressive --no-pack-record-members"; fi
}

# reussir_opt: the checkout's reussir-opt (its build directory, or the
# build of the test tools next to it, build-tests); empty when there is none.
reussir_opt() {
    local o
    for o in "$CK/build/bin/reussir-opt" "$CK/build-tests/bin/reussir-opt"; do
        [ -x "$o" ] && { echo "$o"; return; }
    done
}
# obj_driver NN SRC.rr DRIVER.c FLAGS...: compile a repro to an object,
# link it with a C driver and Reussir's runtime, run it (exe); returns 1
# after saying why when a step fails.
obj_driver() {
    local bug=$1 src=$HERE/$2 drv=$HERE/$3 d=$WORK/out/$1.d; shift 3
    mkdir -p "$d"
    command -v cc > /dev/null || { say_line SKIPPED "$bug" "no cc"; return 1; }
    { (cd "$WORK/run" && "$RRC" "$src" -o "$d/prog.o" --emit obj --relocation-mode pic \
        --polyffi-rust-path "$RUSTC" --polyffi-libdir "$RT" --polyffi-libdir "$RT/deps" \
        --polyffi-libdir "$TL" "$@") > "$d/log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER "$bug" "rrc $(signame "$RC"): $(grep -m1 -o "error[:=].\{0,160\}" "$d/log")" "$*"; return 1; fi
    if ! cc "$d/prog.o" "$drv" -o "$WORK/out/$bug" -L"$RT/deps" -lreussir_rt -Wl,-rpath,"$RT/deps" \
            -Wl,-rpath-link,"$TL" -lm -lpthread -ldl > "$d/cc.log" 2>&1; then
        say_line OTHER "$bug" "cc failed (see $d/cc.log)" "$*"; return 1
    fi
    exe "$bug"
    return 0
}
bug26() {
    # A self call that TRMC moves to the leaf must stay behind a release
    # that runs foreign code. `build` keeps a record with a foreign handle
    # alive across its recursive call (the record is read after it) and
    # asks at the leaf how many handles are open: 3 by the source. Upstream
    # releases each handle before the call: 0. `control` has the same order
    # and no constructor after the call, so TRMC does not apply: 3.
    obj_driver 26 bug26-trmc-observable-release.rr bug26-trmc-observable-release.c -O aggressive || return
    case "$OUT_TXT" in
        "build 0 control 3") say_line REPRODUCES 26 "handles open at the leaf of a TRMC recursion: 0, the source keeps 3 (control without TRMC: 3)" "-O aggressive" ;;
        "build 3 control 3") say_line FIXED 26 "handles open at the leaf of a TRMC recursion: 3, as the source (control: 3)" "-O aggressive" ;;
        *) say_line OTHER 26 "prints '$OUT_TXT' ($(signame $EXIT))" "-O aggressive" ;;
    esac
}
bug27() {
    # `core::object::is_unique` of a nullary constructor under the TBI
    # encoding (aarch64): the value is an immediate that stands for a
    # shared dummy box, never unique. Upstream reads the dummy's 32-bit
    # count, which 2^32 - 1 retains of the value wrap to 1: true.
    local w
    [ "$(uname -m)" = aarch64 ] || { say_line SKIPPED 27 "not aarch64 (the TBI encoding of nullary constructors)"; return; }
    obj_driver 27 bug27-is-unique-immediate.rr bug27-is-unique-immediate.c -O default || return
    w=$(sed -n 's/^is_unique(E::A) after 2^32-1 retains in total = //p' "$WORK/out/27.stdout")
    if ! grep -qx 'is_unique(E::A) = 0' "$WORK/out/27.stdout" || ! grep -qx 'is_unique(E::B{1}) = 1' "$WORK/out/27.stdout"; then
        say_line OTHER 27 "prints '$OUT_TXT' ($(signame $EXIT))" "-O default"
    elif [ "$w" = 1 ]; then say_line REPRODUCES 27 "is_unique of a nullary immediate is true after 2^32 - 1 retains (the dummy box's count wrapped to 1)" "-O default"
    elif [ "$w" = 0 ]; then say_line FIXED 27 "is_unique of a nullary immediate is false, also after 2^32 - 1 retains" "-O default"
    else say_line OTHER 27 "prints '$OUT_TXT' ($(signame $EXIT))" "-O default"; fi
}
bug28() {
    # rrc's pipeline on an aarch64 host with SVE runs a pass that makes the
    # storage of scalable vectors legal. MLIR's pass runs its patterns with
    # region simplification and takes the greedy driver's limit of 10
    # rounds for a failure: a big function with a long chain of blocks
    # (no vector in it) fails the build with `lowering pipeline failed:
    # RunPass`. At pass level, with the checkout's reussir-opt, on a chain
    # that needs more than 10 rounds: MLIR's pass (what upstream's pipeline
    # runs) fails; the pass of patch 28-a, the patterns alone, succeeds.
    # The pass-level run needs no SVE host; the pipeline reaches the pass
    # only on one.
    local opt d=$WORK/out/28 own up
    opt=$(reussir_opt)
    [ -n "$opt" ] || { say_line SKIPPED 28 "no reussir-opt in $CK/build/bin or $CK/build-tests/bin (build its target reussir-opt)"; return; }
    mkdir -p "$d"
    python3 "$HERE/bug28-sve-storage-chain.py" 3 > "$d/c3.mlir"
    python3 "$HERE/bug28-sve-storage-chain.py" 12 > "$d/c12.mlir"
    # The pass must work on a short chain, or the run says nothing.
    "$opt" "$d/c3.mlir" --arm-sve-legalize-vector-storage > /dev/null 2> "$d/c3.log" \
        || { say_line OTHER 28 "MLIR's pass fails a chain of 3 blocks: $(head -c 160 "$d/c3.log")"; return; }
    "$opt" "$d/c12.mlir" --arm-sve-legalize-vector-storage > /dev/null 2> "$d/up.log"; up=$?
    if "$opt" --help | grep -q -- '--reussir-legalize-vector-storage'; then
        "$opt" "$d/c12.mlir" --reussir-legalize-vector-storage > "$d/own.mlir" 2> "$d/own.log"; own=$?
        if [ $own = 0 ] && [ $up != 0 ]; then say_line FIXED 28 "a chain of 13 blocks: the pipeline's storage pass succeeds (MLIR's own pass still fails it, exit $up)"
        else say_line OTHER 28 "a chain of 13 blocks: the pipeline's storage pass exits $own, MLIR's pass $up"; fi
    elif [ $up != 0 ]; then say_line REPRODUCES 28 "a chain of 13 blocks: MLIR's storage pass, which the pipeline runs on SVE hosts, fails (exit $up, no message)"
    else say_line OTHER 28 "a chain of 13 blocks: MLIR's storage pass succeeds, and the checkout has no pass of its own"; fi
}
# expanded NN FILE: the checkout's reussir-opt on FILE with the acquire/drop
# expansion (worklist drops, as rrc's pipeline); the result in
# $WORK/out/NN.mlir. Returns 1 after saying why when it cannot.
expanded() {
    local opt
    opt=$(reussir_opt)
    [ -n "$opt" ] || { say_line SKIPPED "$1" "no reussir-opt in $CK/build/bin or $CK/build-tests/bin (build its target reussir-opt)"; return 1; }
    { "$opt" "$HERE/$2" --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true' \
        > "$WORK/out/$1.mlir" 2> "$WORK/out/$1.log"; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER "$1" "reussir-opt $(signame "$RC"): $(grep -m1 -o "error.\{0,160\}" "$WORK/out/$1.log")"; return 1; fi
    return 0
}
bug30() {
    # A cost of rrc's own time, on an aarch64 host with SVE: the pipeline
    # lowers the vector dialect with MLIR's pass, whose region
    # simplification merges arms that differ only in their values into
    # blocks with arguments; in a big function the arguments multiply (one
    # lean2rr program: about 16 minutes in rrc). Shown at pass level by the
    # shape, not by a time: two pairs of such arms come out as two blocks
    # with arguments from MLIR's pass, and unchanged from 30-a's pass.
    local opt up own
    opt=$(reussir_opt)
    [ -n "$opt" ] || { say_line SKIPPED 30 "no reussir-opt in $CK/build/bin or $CK/build-tests/bin (build its target reussir-opt)"; return; }
    up=$("$opt" "$HERE/bug30-vector-lowering-merge.mlir" --convert-vector-to-llvm 2> "$WORK/out/30.log" | grep -c '^ *\^bb[0-9]*(')
    if "$opt" --help | grep -q -- '--reussir-convert-vector-to-llvm'; then
        own=$("$opt" "$HERE/bug30-vector-lowering-merge.mlir" --reussir-convert-vector-to-llvm 2>> "$WORK/out/30.log" | grep -c '^ *\^bb[0-9]*(')
        if [ "$own" = 0 ] && [ "$up" = 2 ]; then say_line FIXED 30 "the pipeline's vector lowering leaves the arms as they are (MLIR's own pass merges them into $up blocks with arguments)"
        else say_line OTHER 30 "blocks with arguments: $own from the pipeline's vector lowering, $up from MLIR's pass (expected 0 and 2)"; fi
    elif [ "$up" = 2 ]; then say_line REPRODUCES 30 "MLIR's vector lowering, which the pipeline runs on SVE hosts, merges the arms into $up blocks with arguments"
    else say_line OTHER 30 "MLIR's vector lowering gives $up blocks with arguments (expected 2), and the checkout has no pass of its own"; fi
}
bug31() {
    # A cost: the FFI release of a box with no counted member enters the
    # drop worklist to do nothing but free the box.
    local n
    expanded 31 bug31-leaf-foreign-release.mlir || return
    n=$(grep -c 'reussir.drop.join' "$WORK/out/31.mlir")
    if ! grep -q 'reussir.token.free' "$WORK/out/31.mlir"; then say_line OTHER 31 "the release does not free the box (see $WORK/out/31.mlir)"
    elif [ "$n" = 0 ]; then say_line FIXED 31 "the foreign release of a leaf record frees the box directly (no drop.join)"
    else say_line REPRODUCES 31 "the foreign release of a leaf record enters the drop worklist ($n drop.join)"; fi
}
bug32() {
    # A cost: integer members make every dead child of a record a worklist
    # entry, and no arm continues in a child.
    local t r
    expanded 32 bug32-integer-member-release.mlir || return
    t=$(grep -c 'reussir.musttail' "$WORK/out/32.mlir")
    r=$(grep -c 'rcgmp.release' "$WORK/out/32.mlir")
    if [ "$r" = 0 ]; then say_line OTHER 32 "no rcgmp.release in the drop functions (see $WORK/out/32.mlir)"
    elif [ "$t" = 0 ]; then say_line REPRODUCES 32 "a variant with integer members: every dead child is deferred, no tail release"
    else say_line FIXED 32 "a variant with integer members: integers released in place, the last dead child by a tail release ($t musttail)"; fi
}
bug34() {
    # A cost, as entry 31's, for a box that also holds integers: its FFI
    # release enters the drop worklist where it can release the integers
    # in place and free the box.
    local n
    expanded 34 bug34-integer-leaf-foreign-release.mlir || return
    n=$(grep -c 'reussir.drop.join' "$WORK/out/34.mlir")
    if ! grep -q 'reussir.token.free' "$WORK/out/34.mlir"; then say_line OTHER 34 "the release does not free the box (see $WORK/out/34.mlir)"
    elif [ "$n" = 0 ]; then say_line FIXED 34 "the foreign release of a box of two integers releases them in place (no drop.join)"
    else say_line REPRODUCES 34 "the foreign release of a box of two integers enters the drop worklist ($n drop.join)"; fi
}
bug33() {
    # A crash of reussir-opt, not of rrc: `reussir.rc.dec` of a shared box
    # is valid without its token result (the form the frontend emits), and
    # the decrement expansion read that result's type without a test. rrc's
    # pipeline makes the tokens first and never has this input.
    local opt n
    opt=$(reussir_opt)
    [ -n "$opt" ] || { say_line SKIPPED 33 "no reussir-opt in $CK/build/bin or $CK/build-tests/bin (build its target reussir-opt)"; return; }
    { "$opt" "$HERE/bug33-tokenless-rc-dec.mlir" --reussir-rc-decrement-expansion \
        > "$WORK/out/33.mlir" 2> "$WORK/out/33.log"; } 2> /dev/null
    RC=$?
    n=$(grep -c 'reussir.expanded_decrement' "$WORK/out/33.mlir")
    if [ $RC -ge 128 ]; then say_line REPRODUCES 33 "the decrement expansion of a decrement without a token result: reussir-opt $(signame $RC)"
    elif [ $RC = 0 ] && [ "$n" = 1 ] && ! grep -q 'reussir.rc.dec' "$WORK/out/33.mlir"; then say_line FIXED 33 "a decrement without a token result is expanded (its token made first)"
    else say_line OTHER 33 "reussir-opt $(signame $RC), $n expanded decrements: $(grep -m1 -o "error.\{0,160\}" "$WORK/out/33.log")"; fi
}

ALL="01 02 03 04 06 07 08 12 17 18 26 27 28 30 31 32 33 34"
SLOW=" "
[ $# -gt 0 ] && ALL=$*
for b in $ALL; do
    # One part of an entry by its function's name (02r, 02n).
    if [[ $b =~ ^[0-9]+[a-z]$ ]] && declare -f "bug$b" > /dev/null; then "bug$b"; continue; fi
    b=$(printf '%02d' "$((10#${b%%[ab]}))")
    if [ "${QUICK:-0}" = 1 ] && [[ $SLOW == *" $b "* ]]; then say_line SKIPPED "$b" "slow (QUICK=1)"; continue; fi
    if declare -f "bug$b" > /dev/null; then "bug$b"; else echo "no repro for issue $b" >&2; fi
done
