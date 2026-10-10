#!/usr/bin/env bash
# lean2rr's allocations grow no faster than native Lean's: for each runtime
# test with a NAME.alloc file, builds NAME.lean natively (lean + leanc) and
# through lean2rr, both linked with the allocation counter
# (tests/runtime/alloccount: every call to mimalloc's and the C library's
# allocation entry points counted, "alloccount: allocs A reallocs R"
# printed to stderr at exit), runs both at the sizes of each line of
# NAME.alloc, and checks:
# - each run prints what native prints: the same stdout, the same stderr
#   (without the counter's line) and the same exit code;
# - lean2rr's allocations grow at most FACTOR times as much as native's,
#   plus OFFSET, from the small run to the large one:
#   (L_large - L_small) <= FACTOR * (N_large - N_small) + OFFSET,
#   where L and N count lean2rr's and native's allocations; and the same
#   for the bytes they request, with 64 x OFFSET bytes as the offset (a
#   copy of an array of n elements is one allocation of n elements: n
#   copies of a growing array are quadratic in bytes only). What both
#   allocate whatever the size (their startup) cancels out, so a lean2rr
#   build that is linear where native is linear passes with a FACTOR that
#   covers its constant factor, and one that is quadratic or exponential
#   where native is linear fails at sizes a few times apart;
# - optionally (`rss FACTOR OFFSET_KB`), lean2rr's peak memory in the large
#   run (maximum RSS, /usr/bin/time) is at most FACTOR times native's plus
#   OFFSET_KB.
# Every run stops when it has made ALLOC_CHECK_MAX_ALLOCS allocations
# (default 5 x 10^7) or requested ALLOC_CHECK_MAX_BYTES bytes (default 1 GiB):
# the counter's limits (alloccount.c), a safety net that bounds the time
# and the memory of a run that blows up more than its sizes were chosen for
# (each test's sizes keep a blowup of today's lean2rr well under 1 GB). Such
# a run fails the check ("stopped at the allocation limit"); native runs
# stay far below.
#
#   tests/runtime/alloc-check.sh [NAME...]   (default: every NAME.alloc)
#
# NAME.alloc: comment lines (#) and one line per measured case,
#   SMALL ARGS | LARGE ARGS | FACTOR OFFSET [| rss FACTOR OFFSET_KB]
# e.g. `300 | 1200 | 4 2000`: the program's arguments at the two sizes (a
# few times apart; each run must take at most a few seconds on today's
# lean2rr, also where it is quadratic), then the bound. NAME.opts is honored
# as by run.sh. A NAME.xfail file marks the test as known to fail (as for
# run.sh; its first line says why): a failure here is then XFAIL, a pass
# XPASS. A NAME.xfail whose first line starts with `alloc-check:` is for this
# check only: run.sh then expects the test's output to match native.
#
# Environment: as run.sh (L2R_REUSSIR, L2R_LEAN2RR, L2R_TEST_BUILD,
# L2R_LEAN_TOOLCHAIN, L2R_LEAN_RUNTIME, L2R_DISABLE_OPTS, L2R_RRC_FLAGS);
# ALLOC_CHECK_MAX_ALLOCS, ALLOC_CHECK_MAX_BYTES.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
. "$ROOT/scripts/toolchain.sh"
. "$HERE/alloccount/alloccount.sh"
OUT=${L2R_TEST_BUILD:-$HERE/build}/alloc-check
mkdir -p "$OUT"
cd "$OUT" || exit 2
alloccount_setup "$OUT" || { echo "FAIL alloc-check: cannot compile the counter"; exit 1; }
MAX_ALLOCS=${ALLOC_CHECK_MAX_ALLOCS:-50000000}
MAX_BYTES=${ALLOC_CHECK_MAX_BYTES:-1073741824}

if [ $# -gt 0 ]; then
  TESTS=("$@")
else
  TESTS=()
  for f in "$HERE"/Rt*.alloc; do TESTS+=("$(basename "$f" .alloc)"); done
fi

# run_one DIR EXE ARGS TAG: run DIR/EXE with ARGS (split by the shell),
# killed after 120 s; results in DIR/TAG.{out,err,code,rss}.
run_one() {
  local dir=$1 exe=$2 args=$3 tag=$4
  (
    cd "$dir" || exit
    # shellcheck disable=SC2086
    LEAN_BACKTRACE=0 ALLOCCOUNT_MAX_ALLOCS=$MAX_ALLOCS ALLOCCOUNT_MAX_BYTES=$MAX_BYTES \
      timeout -s KILL 120 /usr/bin/time -f "%M" -o "$tag.rss" ./"$exe" $args \
      < /dev/null > "$tag.out" 2> "$tag.err"
    echo $? > "$tag.code"
  )
}

pass=0; fail=0; xfail=0; xpass=0
for t in "${TESTS[@]}"; do
  t=${t%.alloc}
  d=$OUT/$t
  why=""
  if [ ! -f "$HERE/$t.alloc" ] || [ ! -f "$HERE/$t.lean" ]; then
    why=" no $t.alloc or $t.lean"
  else
    rm -rf "$d"; mkdir -p "$d"
    cp "$HERE/$t.lean" "$d/"
    opts=${L2R_DISABLE_OPTS:-}
    [ -f "$HERE/$t.opts" ] && opts="$opts${opts:+,}$(tr -d ' \n' < "$HERE/$t.opts")"
    # shellcheck disable=SC2086
    if ! (cd "$d" && lean -o "$t.olean" -c "$t.c" "$t.lean" && leanc -O3 -DNDEBUG "$t.c" $AC_LEANC -o native) \
         > "$d/build-native.log" 2>&1; then
      why=" native build failed (see $d/build-native.log)"
    elif ! L2R_DISABLE_OPTS=$opts L2R_RRC_FLAGS="${L2R_RRC_FLAGS:-} $AC_RRC" \
         python3 "$ROOT/scripts/l2r.py" "$t" --lean-path "$d" -o "$d/l2r" > "$d/build-l2r.log" 2>&1; then
      why=" lean2rr build failed (see $d/build-l2r.log)"
    else
      k=0
      while IFS= read -r line || [ -n "$line" ]; do
        case $line in "#"*|"") continue ;; esac
        k=$((k + 1))
        IFS='|' read -r small large bound rss <<< "$line"
        read -r factor offset <<< "$bound"
        small=$(echo $small); large=$(echo $large)
        res=""
        for size in small large; do
          a=${!size}
          for b in native l2r; do run_one "$d" "$b" "$a" "$k.$size.$b"; done
          p=$d/$k.$size
          for b in native l2r; do
            if grep -q '^alloccount: stopped at the limit' "$p.$b.err"; then
              res="$res $b stopped at the allocation limit at '$a' ($(sed -n 's/^alloccount: stopped at the limit: //p' "$p.$b.err"); limits $MAX_ALLOCS allocations, $MAX_BYTES bytes);"
            fi
          done
          if ! cmp -s "$p.native.out" "$p.l2r.out"; then res="$res stdout differs at '$a' (diff $p.native.out $p.l2r.out);"; fi
          if ! cmp -s <(alloccount_strip "$p.native.err") <(alloccount_strip "$p.l2r.err"); then
            res="$res stderr differs at '$a' (diff $p.native.err $p.l2r.err);"
          fi
          if ! cmp -s "$p.native.code" "$p.l2r.code"; then
            res="$res exit code $(cat "$p.l2r.code") at '$a', native $(cat "$p.native.code");"
          fi
        done
        read -r n1 nb1 <<< "$(alloccount_read "$d/$k.small.native.err")"
        read -r n2 nb2 <<< "$(alloccount_read "$d/$k.large.native.err")"
        read -r l1 lb1 <<< "$(alloccount_read "$d/$k.small.l2r.err")"
        read -r l2 lb2 <<< "$(alloccount_read "$d/$k.large.l2r.err")"
        if [ -z "$n1" ] || [ -z "$n2" ] || [ -z "$l1" ] || [ -z "$l2" ]; then
          res="$res no allocation count (counter not linked, or the run was killed);"
        else
          dn=$((n2 - n1)); dl=$((l2 - l1)); allowed=$((factor * (dn > 0 ? dn : 0) + offset))
          dnb=$((nb2 - nb1)); dlb=$((lb2 - lb1)); allowedb=$((factor * (dnb > 0 ? dnb : 0) + 64 * offset))
          nr=$(tail -1 "$d/$k.large.native.rss"); lr=$(tail -1 "$d/$k.large.l2r.rss")
          echo "  $t [$small -> $large]: allocations native +$dn, lean2rr +$dl (allowed +$allowed); bytes native +$dnb, lean2rr +$dlb (allowed +$allowedb); peak KB native $nr, lean2rr $lr"
          if [ "$dl" -gt "$allowed" ]; then
            res="$res allocations grow faster than native's ([$small -> $large]: +$dl, native +$dn, allowed $factor x +$dn + $offset);"
          fi
          if [ "$dlb" -gt "$allowedb" ]; then
            res="$res bytes allocated grow faster than native's ([$small -> $large]: +$dlb, native +$dnb, allowed $factor x +$dnb + 64 x $offset);"
          fi
          if [ -n "${rss// /}" ]; then
            read -r _ rf ro <<< "$rss"
            if [ "$lr" -gt $((rf * nr + ro)) ]; then
              res="$res peak memory $lr KB at '$large', native $nr KB (allowed $rf x $nr + $ro);"
            fi
          fi
        fi
        why="$why$res"
      done < "$HERE/$t.alloc"
      [ $k -gt 0 ] || why=" no case in $t.alloc"
    fi
  fi
  if [ -f "$HERE/$t.xfail" ]; then
    if [ -z "$why" ]; then
      xpass=$((xpass + 1)); echo "XPASS $t (remove $t.xfail)"
    else
      xfail=$((xfail + 1)); echo "XFAIL $t: $(head -1 "$HERE/$t.xfail")"
    fi
  elif [ -z "$why" ]; then
    pass=$((pass + 1)); echo "PASS  $t"
  else
    fail=$((fail + 1)); echo "FAIL  $t:$why"
  fi
done
echo "passed $pass, failed $fail, expected failures $xfail, unexpected passes $xpass"
[ $fail -eq 0 ] && echo "PASS  alloc-check"
[ $fail -eq 0 ]
