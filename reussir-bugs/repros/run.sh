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
# line here: 1 to 4, 6 to 8, 12, 17 to 19, 23 and 24 (numbers 5, 9, 11 and
# 22 are retired). Entry 2's repros check the part of it that upstream
# fixed (a bounded stack depth). Entries 10 and 20 (missing features) have
# no repro: their patches carry their own tests; 13 needs a 32-bit target,
# 14 MLIR written by hand, 15 is shown by lean2rr's runtime test
# RtArenaPurge, and 21's patch has a lit test that shows it. Entry 24
# needs RRC_CHECKOUT/build/bin/reussir-opt (a build with the tests on, or
# its target reussir-opt); without it, SKIPPED. Each repro prints one line:
#
#   issue NN  REPRODUCES  the documented behaviour (the bug, the cost, ...)
#                         was seen
#   issue NN  FIXED       the expected output was seen
#   issue NN  OTHER       something else (shown)
#   issue NN  SKIPPED     a tool is missing (shown)
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
# Entries 3, 4 and 19 compare the sizes of two outputs (--emit mlir-llvm,
# --emit mlir, --emit mlir-llvm); entries 6 and 17 read their LLVM IR (the
# calls left, the stack slots left), entry 18 its aarch64 assembly (stores
# through x8), entry 24 the MLIR after two passes (the token frees); entry
# 23 links a C driver (cc) that measures peak RSS around each free; entry 8
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
# rrc's texture cache off: with it, rrc's time and memory would depend on
# what the caller's cache holds (l2r.py turns the cache on unless the
# variable is set; empty is off).
export REUSSIR_FFI_CACHE_DIR=

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
echo "rrc: $RRC"
echo "work: $WORK"
ulimit -c 0

LEAN2RR=${L2R_LEAN2RR:-$ROOT/lean2rr/.lake/build/bin/lean2rr}
L2R_FLAGS="-O aggressive --no-pack-record-members --reuse-across-call"

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
# l2r.py checks the checkout's runtime sources for the patches it requires.
ln -sfn "$CK/crates" "$WRAP/crates"
ln -sfn "$CK/lib" "$WRAP/lib"
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
    # The leanrt representation of `Nat` and `Int` (lean2rr's default until
    # 2026-10-25): the repros do not depend on it, and it needs none of
    # entry 20's patches (rcgmp, the default since, needs 20-a and 20-b and
    # the checkout's core library, which $WRAP does not link).
    (cd "$WORK/run" && RRC_STATS=$out.stats L2R_REUSSIR=$WRAP L2R_LEAN2RR=$LEAN2RR L2R_INT_BACKEND=leanrt \
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

bug19() {
    # The size of the LLVM-dialect module at N = 3 and N = 4 nested types:
    # about 4x when exponential (upstream), about 1.4x with patch 19-a. With
    # 23-f rrc makes no retcon destructors, so the size grows little too.
    local n sz=()
    for n in 3 4; do
        python3 "$HERE/bug19-retcon-direct-arms.py" $n "$WORK/out/19-$n.rr"
        { (cd "$WORK/run" && "$RRC" "$WORK/out/19-$n.rr" --emit mlir-llvm -O none -o "$WORK/out/19-$n.mlir") > "$WORK/out/19-$n.log" 2>&1; } 2> /dev/null
        RC=$?
        if [ $RC != 0 ]; then say_line OTHER 19 "N = $n: $(build_fail 19-$n)" "-O none"; return; fi
        sz+=("$(stat -c %s "$WORK/out/19-$n.mlir")")
    done
    local r msg
    r=$(ratio "${sz[1]}" "${sz[0]}")
    msg="--emit mlir-llvm: N = 3: $((sz[0] / 1024)) KB, N = 4: $((sz[1] / 1024)) KB (${r}x for one more level)"
    if ge "$r" 3; then say_line REPRODUCES 19 "$msg" "-O none"
    elif le "$r" 2; then say_line FIXED 19 "$msg" "-O none"
    else say_line OTHER 19 "$msg" "-O none"; fi
}
bug23() {
    # Peak RSS growth (KiB) during the free of four values of 10^6 levels,
    # measured by the C driver: about 85 bytes per level (left-deep tree:
    # 84 MiB) with upstream's retcon drops, below 16 MiB each when fixed.
    local d=$WORK/out/23 l r c f
    mkdir -p "$d"
    command -v cc > /dev/null || { say_line SKIPPED 23 "no cc"; return; }
    { (cd "$WORK/run" && "$RRC" "$HERE/bug23-deep-free.rr" -o "$d/deep.o" --emit obj --relocation-mode pic -O aggressive) > "$d/log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER 23 "rrc $(signame "$RC"): $(grep -m1 -o "error[:=].\{0,160\}" "$d/log")" "-O aggressive"; return; fi
    if ! cc "$d/deep.o" "$HERE/bug23-deep-free.c" -o "$d/deep" -L"$RT/deps" -lreussir_rt -Wl,-rpath,"$RT/deps" -Wl,-rpath-link,"$TL" > "$d/cc.log" 2>&1; then
        say_line OTHER 23 "cc failed (see $d/cc.log)" "-O aggressive"; return
    fi
    local k g=()
    for k in 0 1 2 3; do
        { (cd "$WORK/run" && timeout 120 "$d/deep" 1000000 $k) > "$d/stdout$k" 2> "$d/stderr$k"; } 2> /dev/null
        EXIT=$?
        g+=("$(sed -n 's/^grew \([0-9]*\)$/\1/p' "$d/stdout$k")")
        [ -n "${g[$k]}" ] || { say_line OTHER 23 "shape $k prints '$(head -c 200 "$d/stdout$k")' ($(signame $EXIT))" "-O aggressive"; return; }
    done
    read -r l r c f <<< "${g[*]}"
    local msg="peak RSS growth during the free of 10^6 levels: left-deep tree $l KiB, right-deep $r, 64-arm chain $c, compositions $f"
    if [ "$l" -ge 32768 ]; then say_line REPRODUCES 23 "$msg" "-O aggressive"
    elif [ "$l" -lt 16384 ] && [ "$r" -lt 16384 ] && [ "$c" -lt 16384 ] && [ "$f" -lt 16384 ]; then say_line FIXED 23 "$msg" "-O aggressive"
    else say_line OTHER 23 "$msg" "-O aggressive"; fi
}
bug24() {
    # The token frees after the acquire/drop expansion with its default
    # options (TPDE mode's) and token reuse: none when the payload's token
    # leaks (upstream), one with 23-e.
    local opt=$CK/build/bin/reussir-opt d=$WORK/out/24 n
    [ -x "$opt" ] || { say_line SKIPPED 24 "no reussir-opt in $CK/build/bin (build its target reussir-opt)"; return; }
    mkdir -p "$d"
    { "$opt" "$HERE/bug24-locked-drop-token.mlir" --reussir-acquire-drop-expansion='outline-record=true expand-decrement=true' \
        --reussir-token-reuse > "$d/out.mlir" 2> "$d/log"; } 2> /dev/null
    RC=$?
    if [ $RC != 0 ]; then say_line OTHER 24 "reussir-opt $(signame "$RC"): $(grep -m1 -o "error.\{0,160\}" "$d/log")"; return; fi
    n=$(grep -c 'reussir.token.free' "$d/out.mlir")
    if [ "$n" = 0 ]; then say_line REPRODUCES 24 "a mutex cell's drop, TPDE options: the payload's token is never freed (no token.free)"
    elif grep -q '@__reussir_locked_drop' "$d/out.mlir"; then say_line FIXED 24 "a mutex cell's drop, TPDE options: the payload's token is freed ($n token.free, in the locked-drop function)"
    else say_line OTHER 24 "$n token.free, no locked-drop function"; fi
}

ALL="01 02 03 04 06 07 08 12 17 18 19 23 24"
SLOW=" "
[ $# -gt 0 ] && ALL=$*
for b in $ALL; do
    b=$(printf '%02d' "$((10#${b%%[ab]}))")
    if [ "${QUICK:-0}" = 1 ] && [[ $SLOW == *" $b "* ]]; then say_line SKIPPED "$b" "slow (QUICK=1)"; continue; fi
    if declare -f "bug$b" > /dev/null; then "bug$b"; else echo "no repro for issue $b" >&2; fi
done
