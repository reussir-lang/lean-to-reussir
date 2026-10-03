#!/usr/bin/env bash
# Build and run the repros of the Reussir bugs in reussir-bugs/ (one file
# per entry, NN-*.md; the index is reussir-bugs/README.md) with one Reussir
# build.
#
#   reussir-bugs/repros/run.sh RRC_CHECKOUT [BUG...]
#
# RRC_CHECKOUT is a Reussir checkout with a build: its build/bin/rrc compiles
# the repros, and plain .rr repros link against its build/target-rt/release.
# BUG is a bug number (1, 02, 13, ...); the default is every bug that has a
# line here (all but 22, whose generator is run by hand). Each repro prints
# one line:
#
#   bug NN  REPRODUCES  the documented bad behaviour was seen
#   bug NN  FIXED       the expected output was seen
#   bug NN  OTHER       something else (shown)
#   bug NN  SKIPPED     a tool is missing, or a slow repro under QUICK=1 (shown)
#
# followed by what was seen and the rrc flags the repro needs.
#
# Plain .rr repros are built with rrc alone (--emit executable plus the
# polymorphic-FFI directories, as scripts/l2r.py passes them). The Lean
# repros (13 and 20, and the programs generated for 16 and 17) go through
# scripts/l2r.py with L2R_REUSSIR set to the checkout. They need Lean 4.33
# (`lean` on PATH) and a lean2rr build (`lake build` in lean2rr/, or
# L2R_LEAN2RR). l2r.py builds the runtime crate leanrt for the checkout
# once, under runtime/leanrt/target/.
#
# Bugs 10, 11, 16, 17, 20 and 23 are build-time entries: the repros of 10, 11,
# 16, 17 and 23 are generated at two sizes and the line reports the growth
# (for 23, of the link phase alone, timed through a rustc wrapper and
# rrc -v); bug 20's is built with and without lean2rr's workaround. They
# take one to three minutes each, and bugs 16 and 20 need 1.2 to 3 GB; bug
# 6 runs for about 15 s. Everything else takes seconds (a first .lean build
# also builds leanrt). Bugs 30 and 32 are build-time entries too, but quick:
# 30 times one conversion pass through reussir-opt (SKIPPED when the
# checkout has not built it), 32 compares the sizes of two --emit mlir dumps. lean2rr works around 16, 17 and 20; the repros turn
# its workarounds off (L2R_NO_OUTLINE, L2R_NO_INLINE_ANCHORS).
#
# Environment:
#   WORK    scratch directory (default: a new one under /tmp); rrc writes
#           reussir_rust_module_* files into its working directory, so every
#           build runs in WORK/run
#   RUSTC   the rustc that built Reussir's runtime (default: the toolchain
#           named in RRC_CHECKOUT/rust-toolchain.toml, else the one l2r.py
#           uses)
#   QUICK=1 skip the slow repros (6, 10, 11, 16, 17, 20, 23)
set -u

usage() { sed -n '2,/^set -u/p' "$0" | sed 's/^# \{0,1\}//; /^set -u/d'; exit 2; }
[ $# -ge 1 ] || usage
case "$1" in -h|--help) usage ;; esac

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
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

say_line() { # STATUS BUG TEXT FLAGS
    printf 'bug %-4s %-11s %s' "$2" "$1" "$3"
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

bug01() { plain_value 01 bug01-value-enum-payload 42 0 -O default; }
bug02() {
    plain_value 02a bug02a-struct-reuse 7005009 7000009 -O aggressive --no-pack-record-members
    plain_value 02b bug02b-variant-packed-layout 5001 11001 -O aggressive
}
bug03() {
    rr bug03-global-alloc-align.rr 03 -O aggressive
    if [ $RC != 0 ]; then say_line OTHER 03 "$(build_fail 03)" "-O aggressive"; return; fi
    exe 03
    local a m
    a=$(sed -n 's/^Box<u64> 16-aligned: \([0-9]*\) of 1000.*/\1/p' "$WORK/out/03.stdout")
    m=$(sed -n 's/.*mi_malloc(8) 16-aligned: \([0-9]*\) of 1000.*/\1/p' "$WORK/out/03.stdout")
    if [ -z "$a" ]; then say_line OTHER 03 "prints '$OUT_TXT'" "-O aggressive"
    elif [ "$a" = 1000 ] && [ "${m:-1000}" -lt 900 ]; then say_line REPRODUCES 03 "$OUT_TXT" "-O aggressive"
    elif [ "$a" -lt 900 ]; then say_line FIXED 03 "$OUT_TXT" "-O aggressive"
    else say_line OTHER 03 "$OUT_TXT" "-O aggressive"; fi
}
compile_crash() { # BUG NAME EXPECTED FLAGS: the bad behaviour is an rrc crash
    local bug=$1 name=$2 exp=$3; shift 3
    rr "$name.rr" "$bug" "$@"
    if [ $RC -ge 128 ] || [ $RC = 124 ]; then say_line REPRODUCES "$bug" "rrc killed by $(signame $RC)" "$*"; return; fi
    if [ $RC != 0 ]; then say_line OTHER "$bug" "$(build_fail "$bug")" "$*"; return; fi
    exe "$bug"
    if [ "$OUT_TXT" = "$exp" ]; then say_line FIXED "$bug" "compiles, prints $OUT_TXT" "$*"
    else say_line OTHER "$bug" "compiles, prints '$OUT_TXT' ($(signame $EXIT)), expected $exp" "$*"; fi
}
compile_error() { # BUG NAME EXPECTED PATTERN FLAGS: the bad behaviour is an rrc error
    local bug=$1 name=$2 exp=$3 pat=$4; shift 4
    rr "$name.rr" "$bug" "$@"
    if [ $RC != 0 ]; then
        if grep -q -- "$pat" "$WORK/out/$bug.log"; then say_line REPRODUCES "$bug" "rrc error: $pat" "$*"
        else say_line OTHER "$bug" "$(build_fail "$bug")" "$*"; fi
        return
    fi
    exe "$bug"
    if [ "$OUT_TXT" = "$exp" ]; then say_line FIXED "$bug" "compiles, prints $OUT_TXT" "$*"
    else say_line OTHER "$bug" "compiles, prints '$OUT_TXT' ($(signame $EXIT)), expected $exp" "$*"; fi
}
bug04() { compile_crash 04 bug04-recursive-type-compare 1005 -O aggressive; }
bug05() { compile_crash 05 bug05-one-armed-if 3 -O aggressive; }
bug06() {
    rr bug06-static-count-wrap.rr 06 $L2R_FLAGS
    if [ $RC != 0 ]; then say_line OTHER 06 "$(build_fail 06)" "$L2R_FLAGS"; return; fi
    exe 06 4294967300
    if [ "$OUT_TXT" = 4294967300 ]; then say_line FIXED 06 "N = 4294967300: prints $OUT_TXT" "$L2R_FLAGS"
    elif [ $EXIT = 139 ]; then say_line REPRODUCES 06 "N = 4294967300: SIGSEGV (static Nil freed)" "$L2R_FLAGS"
    else say_line OTHER 06 "N = 4294967300: '$OUT_TXT' ($(signame $EXIT))" "$L2R_FLAGS"; fi
}
bug07() {
    rr bug07-phantom-reuse-donor.rr 07 $L2R_FLAGS
    if [ $RC != 0 ]; then say_line OTHER 07 "$(build_fail 07)" "$L2R_FLAGS"; return; fi
    exe 07
    local r
    r=$(sed -n 's/^100003 100003 ratio \([0-9.]*\)$/\1/p' "$WORK/out/07.stdout")
    if [ -z "$r" ]; then say_line OTHER 07 "prints '$OUT_TXT'" "$L2R_FLAGS"
    elif ge "$r" 3; then say_line REPRODUCES 07 "insert returning t is ${r}x the rebuilding insert" "$L2R_FLAGS"
    elif le "$r" 1.6; then say_line FIXED 07 "insert returning t is ${r}x the rebuilding insert" "$L2R_FLAGS"
    else say_line OTHER 07 "time ratio $r (between 1.6 and 3)" "$L2R_FLAGS"; fi
}
bug08() {
    local fl="-O aggressive --no-pack-record-members"
    rr bug08-padding-lift.rr 08 $fl
    if [ $RC != 0 ]; then say_line OTHER 08 "$(build_fail 08)" "$fl"; return; fi
    exe 08
    if [ "$OUT_TXT" = 2550200000 ]; then say_line FIXED 08 "prints 2550200000" "$fl"
    elif [ $EXIT -ge 128 ] && [ $EXIT != 124 ]; then say_line REPRODUCES 08 "$(signame $EXIT) (cells overflowed), expected 2550200000" "$fl"
    else say_line OTHER 08 "prints '$OUT_TXT' ($(signame $EXIT)), expected 2550200000" "$fl"; fi
}
# The use-after-free repros print the number of wrong results: a crash or a
# nonzero count is the bug.
uaf_count() { # BUG NAME FLAGS
    local bug=$1 name=$2; shift 2
    rr "$name.rr" "$bug" "$@"
    if [ $RC != 0 ]; then say_line OTHER "$bug" "$(build_fail "$bug")" "$*"; return; fi
    exe "$bug"
    if [ $EXIT = 0 ] && [ "$OUT_TXT" = 0 ]; then say_line FIXED "$bug" "prints 0 (no wrong result in 1000 runs)" "$*"
    elif [ $EXIT != 0 ] && [ $EXIT != 124 ]; then say_line REPRODUCES "$bug" "use after free: $(signame $EXIT)${ERR_TXT:+ ($ERR_TXT)}, expected 0" "$*"
    elif [ $EXIT = 0 ] && [ -n "$OUT_TXT" ] && [ "$OUT_TXT" != 0 ]; then say_line REPRODUCES "$bug" "use after free: $OUT_TXT wrong results, expected 0" "$*"
    else say_line OTHER "$bug" "prints '$OUT_TXT' ($(signame $EXIT))" "$*"; fi
}
bug09() { uaf_count 09 bug09-duplicate-bound-member $L2R_FLAGS; }
bug14() { uaf_count 14 bug14-member-consumed-before-release $L2R_FLAGS; }
bug10() {
    python3 "$HERE/bug10-closure-type-print.py" 20 "$WORK/out/10.rr"
    timed rr "$WORK/out/10.rr" 10 -O aggressive; local tw=$SECS rw=$RC
    timed rr "$WORK/out/10.rr" 10n -O aggressive --no-closure-wpd; local tn=$SECS
    if [ $rw != 0 ]; then say_line OTHER 10 "K = 20: $(build_fail 10)" "-O aggressive"; return; fi
    local msg="K = 20: ${tw} s with closure devirtualization, ${tn} s with --no-closure-wpd"
    if ge "$tw" "$(echo "3 * $tn + 2" | bc)"; then say_line REPRODUCES 10 "$msg" "-O aggressive"
    elif le "$tw" "$(echo "1.5 * $tn + 1" | bc)"; then say_line FIXED 10 "$msg" "-O aggressive"
    else say_line OTHER 10 "$msg" "-O aggressive"; fi
}
bug11() {
    # N = 10 measures the fixed cost of a build (the FFI texture, linking).
    local n t0 ta tb
    for n in 10 2000 4000; do python3 "$HERE/bug11-sccp-call-graph.py" $n "$WORK/out/11-$n.rr"; done
    timed rr "$WORK/out/11-10.rr" 11-10 -O aggressive; t0=$SECS
    timed rr "$WORK/out/11-2000.rr" 11-2000 -O aggressive; ta=$SECS
    timed rr "$WORK/out/11-4000.rr" 11-4000 -O aggressive; tb=$SECS
    if [ $RC != 0 ]; then say_line OTHER 11 "N = 4000: $(build_fail 11-4000)" "-O aggressive"; return; fi
    local r msg
    r=$(ratio "$(echo "$tb - $t0" | bc)" "$(echo "$ta - $t0" | bc)")
    msg="N = 2000: ${ta} s, N = 4000: ${tb} s, N = 10: ${t0} s (${r}x without the fixed cost, for twice the call sites)"
    if ge "$r" 3; then say_line REPRODUCES 11 "$msg" "-O aggressive"
    elif le "$r" 2.5; then say_line FIXED 11 "$msg" "-O aggressive"
    else say_line OTHER 11 "$msg" "-O aggressive"; fi
}
bug12() {
    python3 "$HERE/bug12-node-cache-collision.py" "$WORK/out/12.rr"
    rr "$WORK/out/12.rr" 12 -O aggressive
    if [ $RC != 0 ]; then say_line OTHER 12 "$(build_fail 12)" "-O aggressive"; return; fi
    exe 12
    case "$OUT_TXT" in
        424242) say_line FIXED 12 "prints 424242" "-O aggressive" ;;
        7) say_line REPRODUCES 12 "prints 7 (the literal 424242 was parsed as the variable), expected 424242" "-O aggressive" ;;
        *) say_line OTHER 12 "prints '$OUT_TXT', expected 424242" "-O aggressive" ;;
    esac
}
bug13() {
    rr bug13-long-list-drop.rr 13 $L2R_FLAGS
    if [ $RC != 0 ]; then say_line OTHER 13 "$(build_fail 13)" "$L2R_FLAGS"; else
        local s
        for s in "0 list" "1 snoc" "2 lspine"; do
            set -- $s
            exe 13 "$1" 1000000
            if [ "$OUT_TXT" = 1000000 ]; then say_line FIXED "13" "$2, 1M cells, 8 MB stack: prints 1000000" "$L2R_FLAGS"
            elif [ -n "$ERR_TXT" ] || [ $EXIT -ge 128 ]; then say_line REPRODUCES "13" "$2, 1M cells, 8 MB stack: $ERR_TXT ($(signame $EXIT))" "$L2R_FLAGS"
            else say_line OTHER "13" "$2, 1M cells: '$OUT_TXT' ($(signame $EXIT))" "$L2R_FLAGS"; fi
        done
    fi
    local why
    if ! why=$(have_lean); then say_line SKIPPED "13" "lean2rr repro: $why"; return; fi
    lean_build "$HERE/bug13-long-list-drop.lean" LongDrop 13l
    if [ $RC != 0 ]; then say_line OTHER "13" "lean2rr build failed (see $WORK/out/13l.log)"; return; fi
    local c exp what
    for c in 0 1; do
        if [ $c = 0 ]; then exp="(some 7)"; what="List.replicate"; else exp=0; what=snoc; fi
        exe 13l $c 40000000
        if [ "$OUT_TXT" = "$exp" ]; then say_line FIXED 13 "lean2rr $what, 40M cells, 1 GiB stack: prints $OUT_TXT" "l2r.py"
        elif [ -n "$ERR_TXT" ] || [ $EXIT -ge 128 ]; then say_line REPRODUCES 13 "lean2rr $what, 40M cells, 1 GiB stack: $ERR_TXT ($(signame $EXIT))" "l2r.py"
        else say_line OTHER 13 "lean2rr $what, 40M cells: '$OUT_TXT' ($(signame $EXIT))" "l2r.py"; fi
    done
}
bug15() { compile_error 15 bug15-nullable-match-yield 1 "parent operation expected a value, but nothing is yielded" -O aggressive; }
bug16() {
    local why
    if ! why=$(have_lean); then say_line SKIPPED 16 "$why"; return; fi
    python3 "$HERE/bug16-nested-io-matches.py" 50 "$WORK/out/Nest50.lean"
    python3 "$HERE/bug16-nested-io-matches.py" 100 "$WORK/out/Nest100.lean"
    # Without lean2rr's workaround (Outline), so that rrc sees the nesting.
    export L2R_NO_OUTLINE=1
    lean_build "$WORK/out/Nest50.lean" Nest50 16a; local s1=$RSECS m1=$RKB r1=$RC
    lean_build "$WORK/out/Nest100.lean" Nest100 16b; local s2=$RSECS m2=$RKB r2=$RC
    lean_build "$WORK/out/Nest100.lean" Nest100 16c --no-reuse-across-call; local s3=$RSECS m3=$RKB
    unset L2R_NO_OUTLINE
    if [ $r1 != 0 ] || [ $r2 != 0 ] || [ -z "$m1" ] || [ -z "$m2" ]; then say_line OTHER 16 "build failed (see $WORK/out/16?.log)" "l2r.py"; return; fi
    local r msg
    r=$(ratio "$m2" "$m1")
    msg="rrc: N = 50: ${s1} s, $((m1 / 1024)) MB; N = 100: ${s2} s, $((m2 / 1024)) MB (${r}x memory); N = 100 without reuse across calls: ${s3:-?} s, $((${m3:-0} / 1024)) MB"
    if ge "$r" 2.5; then say_line REPRODUCES 16 "$msg" "l2r.py"
    elif le "$r" 1.6; then say_line FIXED 16 "$msg" "l2r.py"
    else say_line OTHER 16 "$msg" "l2r.py"; fi
}
bug17() {
    local why
    if ! why=$(have_lean); then say_line SKIPPED 17 "$why"; return; fi
    python3 "$HERE/bug17-long-nat-block.py" 250 "$WORK/out/Lets250.lean"
    python3 "$HERE/bug17-long-nat-block.py" 500 "$WORK/out/Lets500.lean"
    # Without lean2rr's workaround (Outline), so that rrc sees the long block.
    export L2R_NO_OUTLINE=1
    lean_build "$WORK/out/Lets250.lean" Lets250 17a; local s1=$RSECS m1=$RKB r1=$RC
    lean_build "$WORK/out/Lets500.lean" Lets500 17b; local s2=$RSECS m2=$RKB r2=$RC
    unset L2R_NO_OUTLINE
    if [ $r1 != 0 ] || [ $r2 != 0 ] || [ -z "$m1" ] || [ -z "$m2" ]; then say_line OTHER 17 "build failed (see $WORK/out/17?.log)" "l2r.py"; return; fi
    local r msg
    r=$(ratio "$m2" "$m1")
    msg="rrc: N = 250: ${s1} s, $((m1 / 1024)) MB; N = 500: ${s2} s, $((m2 / 1024)) MB (${r}x memory for twice the lets)"
    if ge "$r" 2.3; then say_line REPRODUCES 17 "$msg" "l2r.py"
    elif le "$r" 1.6; then say_line FIXED 17 "$msg" "l2r.py"
    else say_line OTHER 17 "$msg" "l2r.py"; fi
}
bug18() {
    local r
    r=$("$HERE/bug18-rrc-target-deps.sh" "$CK")
    say_line "${r%% *}" 18 "${r#* }"
}
bug19() { compile_error 19 bug19-cell-of-value-record 42 "operand type mismatch" -O aggressive; }
bug20() {
    local why
    if ! why=$(have_lean); then say_line SKIPPED 20 "$why"; return; fi
    # Without lean2rr's workaround (#[transform_anchor] on its conversion
    # and unboxing functions), then with it.
    export L2R_NO_INLINE_ANCHORS=1
    lean_build "$HERE/bug20-statet-tower.lean" Tower 20a; local s1=$RSECS m1=$RKB r1=$RC
    unset L2R_NO_INLINE_ANCHORS
    lean_build "$HERE/bug20-statet-tower.lean" Tower 20b; local s2=$RSECS m2=$RKB r2=$RC
    if [ $r1 != 0 ] || [ $r2 != 0 ] || [ -z "$m1" ] || [ -z "$m2" ]; then say_line OTHER 20 "build failed (see $WORK/out/20?.log)" "l2r.py"; return; fi
    local r msg
    r=$(ratio "$m1" "$m2")
    msg="rrc: ${s1} s, $((m1 / 1024)) MB; with the conversion functions kept out of the inliner: ${s2} s, $((m2 / 1024)) MB (${r}x memory)"
    if ge "$r" 2.5; then say_line REPRODUCES 20 "$msg" "l2r.py"
    elif le "$r" 1.5; then say_line FIXED 20 "$msg" "l2r.py"
    else say_line OTHER 20 "$msg" "l2r.py"; fi
}

bug21() { plain_value 21 bug21-unterminated-placeholder 4 2 -O aggressive; }

bug23() {
    # K and 2K instances of one polymorphic FFI import. The texture compiles
    # (one rustc each) are linear and come first; the link phase is timed
    # alone: from the exit of the last texture rustc (a wrapper logs each
    # exit) to rrc -v's "running the MLIR lowering pipeline". Twice the
    # instances: 4x the link time when quadratic, 2x when linear.
    local k tm tl t secs=() w=$WORK/out/23-rustc
    printf '#!/bin/sh\n"%s" "$@"\nr=$?\ndate +%%s.%%N >> "$RUSTC_LOG"\nexit $r\n' "$RUSTC" > "$w"
    chmod +x "$w"
    for k in 300 600; do
        python3 "$HERE/bug23-polyffi-link.py" $k "$WORK/out/23-$k.rr"
        rm -f "$WORK/out/23-$k.rustc"
        { (cd "$WORK/run" && RUSTC_LOG=$WORK/out/23-$k.rustc "$RRC" "$WORK/out/23-$k.rr" \
            -o "$WORK/out/23-$k" --emit executable -O aggressive -v --polyffi-rust-path "$w" \
            --polyffi-libdir "$RT" --polyffi-libdir "$RT/deps" --polyffi-libdir "$TL") \
            > "$WORK/out/23-$k.log" 2>&1; } 2> /dev/null
        RC=$?
        if [ $RC != 0 ]; then say_line OTHER 23 "K = $k: $(build_fail 23-$k)" "-O aggressive"; return; fi
        exe 23-$k
        if [ "$OUT_TXT" != $((k * (k - 1) / 2)) ]; then
            say_line OTHER 23 "K = $k: prints '$OUT_TXT' ($(signame $EXIT)), expected $((k * (k - 1) / 2))" "-O aggressive"; return
        fi
        t=$(grep -m1 -o '^[0-9T:.-]*Z.*running the MLIR lowering pipeline' "$WORK/out/23-$k.log" | cut -d' ' -f1)
        tm=$(date -d "$t" +%s.%N 2> /dev/null)
        # (the executable's link step runs the wrapper once more, later)
        tl=$(awk -v t="$tm" '$1 <= t' "$WORK/out/23-$k.rustc" 2> /dev/null | sort -n | tail -1)
        if [ -z "$tm" ] || [ -z "$tl" ]; then say_line OTHER 23 "K = $k: no phase timestamps (see $WORK/out/23-$k.log)" "-O aggressive"; return; fi
        secs+=("$(printf '%.1f' "$(echo "$tm - $tl" | bc)")")
    done
    local l1=${secs[0]} l2=${secs[1]} r=0 msg
    ge "$l1" 0.1 && r=$(ratio "$l2" "$l1")
    msg="link of the gathered modules: K = 300: ${l1} s, K = 600: ${l2} s (${r}x for twice the instances)"
    if ge "$r" 3 && ge "$l2" 2; then say_line REPRODUCES 23 "$msg" "-O aggressive"
    elif le "$r" 2.6 || le "$l2" 1; then say_line FIXED 23 "$msg" "-O aggressive"
    else say_line OTHER 23 "$msg" "-O aggressive"; fi
}

bug28() { plain_value 28 bug28-unique-carrying-join "101 1" "101 101" -O aggressive; }

bug29() {
    # Print the module, then read the dump back (a resumed build).
    local o=$WORK/out/29
    { (cd "$WORK/run" && "$RRC" "$HERE/bug29-ffi-member-mlir.rr" --emit mlir -o "$o.a.mlir" \
        && "$RRC" "$o.a.mlir" -x mlir --emit mlir -o "$o.b.mlir") > "$o.log" 2>&1; } 2> /dev/null
    RC=$?
    if [ $RC = 0 ] && cmp -s "$o.a.mlir" "$o.b.mlir"; then say_line FIXED 29 "the --emit mlir dump parses back and prints identically"
    elif grep -q "rc members must be atomic shared links" "$o.log"; then
        say_line REPRODUCES 29 "the --emit mlir dump does not parse: rc members must be atomic shared links"
    else say_line OTHER 29 "$(build_fail 29)"; fi
}

bug30() {
    # The conversion alone, through reussir-opt (not built by default:
    # `ninja -C build reussir-opt`). Twice the functions and calls: 4x the
    # time when quadratic, 2x when linear.
    local opt=$CK/build/bin/reussir-opt n secs=()
    if [ ! -x "$opt" ]; then say_line SKIPPED 30 "no reussir-opt at $opt"; return; fi
    for n in 5000 10000; do
        python3 "$HERE/bug30-call-lowering.py" $n "$WORK/out/30-$n.mlir"
        rm -f "$WORK/out/30-$n.out.mlir"
        timed "$opt" "$WORK/out/30-$n.mlir" --reussir-convert-to-llvm -o "$WORK/out/30-$n.out.mlir" 2> "$WORK/out/30-$n.log"
        if [ ! -s "$WORK/out/30-$n.out.mlir" ]; then say_line OTHER 30 "N = $n: reussir-opt failed (see $WORK/out/30-$n.log)"; return; fi
        secs+=("$SECS")
    done
    local t1=${secs[0]} t2=${secs[1]} r=0 msg
    ge "$t1" 0.1 && r=$(ratio "$t2" "$t1")
    msg="reussir-opt --reussir-convert-to-llvm: N = 5000: ${t1} s, N = 10000: ${t2} s (${r}x for twice the calls)"
    if ge "$r" 3 && ge "$t2" 1; then say_line REPRODUCES 30 "$msg"
    elif le "$r" 2.6 || le "$t2" 0.6; then say_line FIXED 30 "$msg"
    else say_line OTHER 30 "$msg"; fi
}

bug31() {
    python3 "$HERE/bug31-deep-expression.py" 8000 100000 "$WORK/out/31.rr"
    rr "$WORK/out/31.rr" 31 -O aggressive
    if [ $RC != 0 ]; then
        if grep -q "overflowed its stack" "$WORK/out/31.log"; then say_line REPRODUCES 31 "rrc: thread 'main' has overflowed its stack ($(signame $RC))" "-O aggressive"
        else say_line OTHER 31 "$(build_fail 31)" "-O aggressive"; fi
        return
    fi
    exe 31
    if [ "$OUT_TXT" = 32004007 ]; then say_line FIXED 31 "compiles, prints 32004007" "-O aggressive"
    else say_line OTHER 31 "compiles, prints '$OUT_TXT' ($(signame $EXIT)), expected 32004007" "-O aggressive"; fi
}

bug32() {
    # The size of the printed module at K and K + 2: 4x when exponential.
    local k sz=()
    for k in 10 12; do
        python3 "$HERE/bug32-emit-mlir-size.py" $k "$WORK/out/32-$k.rr"
        { (cd "$WORK/run" && "$RRC" "$WORK/out/32-$k.rr" --emit mlir -o "$WORK/out/32-$k.mlir") > "$WORK/out/32-$k.log" 2>&1; } 2> /dev/null
        RC=$?
        if [ $RC != 0 ]; then say_line OTHER 32 "K = $k: $(build_fail 32-$k)"; return; fi
        sz+=("$(stat -c %s "$WORK/out/32-$k.mlir")")
    done
    local r msg
    r=$(ratio "${sz[1]}" "${sz[0]}")
    msg="--emit mlir: K = 10: $((sz[0] / 1024)) KB, K = 12: $((sz[1] / 1024)) KB (${r}x for two more levels)"
    if ge "$r" 3; then say_line REPRODUCES 32 "$msg"
    elif le "$r" 1.5; then say_line FIXED 32 "$msg"
    else say_line OTHER 32 "$msg"; fi
}

ALL="01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 23 28 29 30 31 32"
SLOW=" 06 10 11 16 17 20 23 "
[ $# -gt 0 ] && ALL=$*
for b in $ALL; do
    b=$(printf '%02d' "$((10#${b%%[ab]}))")
    if [ "${QUICK:-0}" = 1 ] && [[ $SLOW == *" $b "* ]]; then say_line SKIPPED "$b" "slow (QUICK=1)"; continue; fi
    if declare -f "bug$b" > /dev/null; then "bug$b"; else echo "no repro for bug $b" >&2; fi
done
