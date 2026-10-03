#!/usr/bin/env python3
"""Native-Lean oracle for the lean2rr classic corpus (Python 3, stdlib only).

    oracle.py build
        `lake build` in tests/classic, with the Lean toolchain lean2rr is
        pinned to (L2R_LEAN_TOOLCHAIN, default the elan toolchain that
        lean2rr/lean-toolchain names; as scripts/toolchain.sh).
    oracle.py record [--cases A B ...] [--sizes small medium bench]
        Run the native executables and write
        tests/classic/expected/<name>.<size>.{stdout,stderr,exitcode}.
    oracle.py check --cmd TEMPLATE [--cases ...] [--sizes ...] [--timeout S]
        Run another implementation and compare stdout, stderr and the exit
        code exactly with the recorded files. Exit status 1 on any mismatch.
    oracle.py bench [--cmd TEMPLATE] [--cases ...] [--size bench] [--repeat N]
        Time the native executable and (if given) the other implementation,
        interleaved, pinned with taskset to the least-loaded fast core
        (re-chosen for every case). Reports min wall time, max RSS, ratio.

TEMPLATE is a shell command with placeholders {name} (case name), {exe}
(executable name), {module} (root module), {size} (the size argument) and
{native} (path of the native executable), e.g.
    --cmd 'out/{exe} {size}'     or, to test the harness itself,
    --cmd '{native} {size}'
"""

import argparse
import json
import os
import shlex
import subprocess
import sys
import tempfile
import time

TESTS = os.path.dirname(os.path.abspath(__file__))
CLASSIC = os.path.join(TESTS, "classic")
EXPECTED = os.path.join(CLASSIC, "expected")
BIN = os.path.join(CLASSIC, ".lake", "build", "bin")
SIZES = ["small", "medium", "bench"]


def load_cases(selected=None):
    with open(os.path.join(CLASSIC, "cases.json")) as f:
        cases = json.load(f)
    if selected:
        known = {c["name"] for c in cases}
        unknown = [s for s in selected if s not in known]
        if unknown:
            sys.exit(f"unknown case(s): {', '.join(unknown)}")
        cases = [c for c in cases if c["name"] in selected]
    return cases


def native_path(case):
    return os.path.join(BIN, case["exe"])


def expand(template, case, size_label):
    return template.format(name=case["name"], exe=case["exe"], module=case["module"],
                           size=case["sizes"][size_label], native=shlex.quote(native_path(case)))


def expected_path(case, size_label, kind):
    return os.path.join(EXPECTED, f"{case['name']}.{size_label}.{kind}")


# ---------------------------------------------------------------- build / record

def lean_toolchain():
    """The Lean toolchain directory (see scripts/toolchain.sh)."""
    if os.environ.get("L2R_LEAN_TOOLCHAIN"):
        return os.environ["L2R_LEAN_TOOLCHAIN"]
    with open(os.path.join(TESTS, "..", "lean2rr", "lean-toolchain")) as f:
        pin = "".join(f.read().split())
    elan = os.environ.get("ELAN_HOME", os.path.join(os.path.expanduser("~"), ".elan"))
    return os.path.join(elan, "toolchains", pin.replace("/", "--").replace(":", "---"))


def cmd_build(args):
    bindir = os.path.join(lean_toolchain(), "bin")
    env = dict(os.environ, PATH=bindir + os.pathsep + os.environ.get("PATH", ""))
    return subprocess.call([os.path.join(bindir, "lake"), "build"], cwd=CLASSIC, env=env)


def cmd_record(args):
    os.makedirs(EXPECTED, exist_ok=True)
    for case in load_cases(args.cases):
        for label in args.sizes:
            size = str(case["sizes"][label])
            t0 = time.perf_counter()
            p = subprocess.run([native_path(case), size], capture_output=True)
            dt = time.perf_counter() - t0
            for kind, data in (("stdout", p.stdout), ("stderr", p.stderr),
                               ("exitcode", f"{p.returncode}\n".encode())):
                with open(expected_path(case, label, kind), "wb") as f:
                    f.write(data)
            note = "" if p.returncode == 0 and not p.stderr else "  (nonzero exit or stderr output!)"
            print(f"{case['name']:18} {label:6} {size:>9}  exit={p.returncode}  {dt:7.2f}s{note}")
    return 0


# ---------------------------------------------------------------- check

def first_difference(want, got):
    """Line number and both lines of the first difference (for the report)."""
    def lines(data):
        ls = data.decode(errors="replace").split("\n")
        return ls[:-1] if ls and ls[-1] == "" else ls   # drop the final newline's empty tail
    w, g = lines(want), lines(got)
    for i in range(max(len(w), len(g))):
        a = w[i] if i < len(w) else "<missing>"
        b = g[i] if i < len(g) else "<missing>"
        if a != b:
            return f"line {i + 1}:\n      expected: {a[:200]!r}\n      got:      {b[:200]!r}"
    return "identical lines (difference in trailing bytes)"


def cmd_check(args):
    failures = 0
    details = []
    print(f"{'case':18} {'size':6} {'stdout':6} {'stderr':6} {'exit':6} {'time':>8}")
    for case in load_cases(args.cases):
        for label in args.sizes:
            try:
                want_out = open(expected_path(case, label, "stdout"), "rb").read()
                want_err = open(expected_path(case, label, "stderr"), "rb").read()
                want_code = int(open(expected_path(case, label, "exitcode")).read())
            except FileNotFoundError:
                sys.exit(f"missing expected files for {case['name']}.{label}; run `record` first")
            command = expand(args.cmd, case, label)
            t0 = time.perf_counter()
            try:
                p = subprocess.run(command, shell=True, capture_output=True, timeout=args.timeout)
                got_out, got_err, got_code = p.stdout, p.stderr, p.returncode
            except subprocess.TimeoutExpired as e:
                got_out, got_err, got_code = e.stdout or b"", (e.stderr or b"") + b"<timeout>", None
            dt = time.perf_counter() - t0
            res = ["ok" if got_out == want_out else "FAIL",
                   "ok" if got_err == want_err else "FAIL",
                   "ok" if got_code == want_code else "FAIL"]
            print(f"{case['name']:18} {label:6} {res[0]:6} {res[1]:6} {res[2]:6} {dt:7.2f}s")
            if "FAIL" in res:
                failures += 1
                d = f"  {case['name']}.{label}: $ {command}\n"
                if res[0] == "FAIL":
                    d += f"    stdout {first_difference(want_out, got_out)}\n"
                if res[1] == "FAIL":
                    d += f"    stderr {first_difference(want_err, got_err)}\n"
                if res[2] == "FAIL":
                    d += f"    exit code: expected {want_code}, got {got_code}\n"
                details.append(d)
    if details:
        print("\nmismatches:\n" + "".join(details), end="")
    print(f"\n{failures} mismatch(es)" if failures else "\nall passed")
    return 1 if failures else 0


# ---------------------------------------------------------------- bench

def cpu_times():
    """cpu index -> (idle, total) jiffies, from /proc/stat."""
    out = {}
    with open("/proc/stat") as f:
        for line in f:
            parts = line.split()
            if parts[0].startswith("cpu") and parts[0] != "cpu":
                vals = [int(v) for v in parts[1:]]
                out[int(parts[0][3:])] = (vals[3] + vals[4], sum(vals))  # idle + iowait
    return out


def max_freq(cpu):
    try:
        with open(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/cpuinfo_max_freq") as f:
            return int(f.read())
    except OSError:
        return 0


def pick_core(interval=1.0):
    """The least-loaded core among the fastest cores we may run on."""
    allowed = sorted(os.sched_getaffinity(0))
    fastest = max(max_freq(c) for c in allowed)
    candidates = [c for c in allowed if max_freq(c) == fastest]
    a = cpu_times()
    time.sleep(interval)
    b = cpu_times()

    def idle(c):
        total = b[c][1] - a[c][1]
        return (b[c][0] - a[c][0]) / total if total else 0.0
    best = max(candidates, key=idle)
    return best, idle(best)


def timed_run(command, core, timeout):
    """(wall seconds, max RSS KiB, exit code, stdout) of one pinned run."""
    with tempfile.NamedTemporaryFile(mode="r", suffix=".time") as tf:
        full = f"taskset -c {core} /usr/bin/time -o {tf.name} -f '%e %M' sh -c {shlex.quote(command)}"
        p = subprocess.run(full, shell=True, capture_output=True, timeout=timeout)
        fields = tf.read().split()[-2:]
    wall, rss = (float(fields[0]), int(fields[1])) if len(fields) == 2 else (float("nan"), 0)
    return wall, rss, p.returncode, p.stdout


def cmd_bench(args):
    impls = [("native", "{native} {size}")]
    if args.cmd:
        impls.append(("alt", args.cmd))
    header = f"{'case':18} {'size':>9} {'core':>4} {'native s':>9} {'native MiB':>10}"
    if args.cmd:
        header += f" {'alt s':>9} {'alt MiB':>9} {'time x':>7} {'mem x':>6}  output"
    print(header)
    for case in load_cases(args.cases):
        core, idle = pick_core()
        best = {name: (float("inf"), 0) for name, _ in impls}
        outputs_ok = True
        want = None
        path = expected_path(case, args.size, "stdout")
        if os.path.exists(path):
            want = open(path, "rb").read()
        for _ in range(args.repeat):
            for name, template in impls:   # interleaved: native, alt, native, alt, ...
                wall, rss, code, out = timed_run(expand(template, case, args.size), core, args.timeout)
                if code != 0 or (want is not None and out != want):
                    outputs_ok = False
                best[name] = (min(best[name][0], wall), max(best[name][1], rss))
        nt, nr = best["native"]
        line = f"{case['name']:18} {case['sizes'][args.size]:>9} {core:>4} {nt:9.2f} {nr / 1024:10.1f}"
        if args.cmd:
            at, ar = best["alt"]
            tx = at / nt if nt > 0 else float("nan")
            mx = ar / nr if nr > 0 else float("nan")
            line += f" {at:9.2f} {ar / 1024:9.1f} {tx:7.2f} {mx:6.2f}  {'ok' if outputs_ok else 'MISMATCH'}"
        elif not outputs_ok:
            line += "  (native output differs from expected!)"
        print(line, flush=True)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="command", required=True)
    sub.add_parser("build", help="lake build the corpus")
    p = sub.add_parser("record", help="record native outputs as expected files")
    p.add_argument("--cases", nargs="+")
    p.add_argument("--sizes", nargs="+", choices=SIZES, default=SIZES)
    p = sub.add_parser("check", help="compare another implementation with the expected files")
    p.add_argument("--cmd", required=True)
    p.add_argument("--cases", nargs="+")
    p.add_argument("--sizes", nargs="+", choices=SIZES, default=SIZES)
    p.add_argument("--timeout", type=float, default=600.0)
    p = sub.add_parser("bench", help="time native versus another implementation")
    p.add_argument("--cmd")
    p.add_argument("--cases", nargs="+")
    p.add_argument("--size", choices=SIZES, default="bench")
    p.add_argument("--repeat", type=int, default=5)
    p.add_argument("--timeout", type=float, default=600.0)
    args = ap.parse_args()
    return {"build": cmd_build, "record": cmd_record, "check": cmd_check, "bench": cmd_bench}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
