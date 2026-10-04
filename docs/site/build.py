#!/usr/bin/env python3
"""Build the lean2rr design site (docs/site) from pages/*.md.

    python3 docs/site/build.py           # write the *.html files
    python3 docs/site/build.py --check   # fail if a page would change

The script needs Python 3 and the `markdown` module only. The pages work
offline (file://): no network, no external scripts or fonts.

What it does:
- renders every pages/NAME.md to NAME.html with the shared template;
- fills the placeholders of the pages:
    {{svg:NAME}}  a diagram from diagrams.py (DIAGRAMS)
    {{gen:NAME}}  a table generated from the repository's files (GENERATORS)
    {{v:NAME}}    a short value: a version or a count (values())
- turns links written as repo:PATH (in Markdown links and in href
  attributes) into relative links to the repository's files;
- checks the sources against each other and prints a warning for each
  disagreement;
- refuses to write a page that contains a forbidden string (FORBIDDEN):
  the site is public.

The output depends only on the repository's files, not on the date, the
commit or the machine: building twice gives the same pages, so the built
pages are committed and open directly after a clone.
"""

import argparse
import html
import json
import os
import re
import sys

import markdown

sys.dont_write_bytecode = True
import diagrams  # noqa: E402

SITE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(SITE, "..", ".."))
# From docs/site/ to the repository's root.
REPO_REL = "../../"

PAGES = [
    ("index", "Overview"),
    ("pipeline", "Pipeline"),
    ("representations", "Representations"),
    ("dependent-types", "Dependent types"),
    ("runtime", "Runtime"),
    ("passes", "Optional passes"),
    ("testing", "Testing"),
    ("reussir", "Reussir"),
    ("differences", "Known differences"),
    ("glossary", "Glossary"),
]

# Strings that must not appear in the site (its sources or its pages):
# local paths and private notes. More strings, one per line, can be listed
# in docs/local/site-forbidden.txt (not in git), so that the list itself
# names nothing private.
FORBIDDEN = ["/home/", "l2r-scratch", "docs/local"]
_LOCAL_FORBIDDEN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "local", "site-forbidden.txt")
if os.path.exists(_LOCAL_FORBIDDEN):
    with open(_LOCAL_FORBIDDEN, encoding="utf-8") as _f:
        FORBIDDEN += [line.strip() for line in _f if line.strip() and not line.startswith("#")]

WARNINGS = []


def warn(msg):
    WARNINGS.append(msg)
    print("warning:", msg, file=sys.stderr)


def read(path):
    with open(os.path.join(REPO, path), encoding="utf-8") as f:
        return f.read()


# ---------------------------------------------------------------------------
# Inline markdown of a table cell, with links made relative to the site.

def md_inline(text, base):
    """Render a markdown fragment taken from a file in directory `base`
    (relative to the repository), as inline HTML."""
    def fix(m):
        label, target = m.group(1), m.group(2)
        if re.match(r"^[a-z]+:", target) or target.startswith("#"):
            return m.group(0)
        return f"[{label}]({REPO_REL}{os.path.normpath(os.path.join(base, target))})"
    text = re.sub(r"\[([^\]]*)\]\(([^)\s]+)\)", fix, text)
    out = markdown.markdown(text)
    out = re.sub(r"^<p>|</p>$", "", out.strip())
    return out


def md_table(rows, header, cls="tbl"):
    h = "".join(f"<th>{html.escape(c)}</th>" for c in header)
    body = "".join("<tr>" + "".join(f"<td>{c}</td>" for c in r) + "</tr>" for r in rows)
    return (f'<div class="tblwrap"><table class="{cls}"><thead><tr>{h}</tr></thead>'
            f"<tbody>{body}</tbody></table></div>")


def parse_md_table(text, first_header):
    """Rows (lists of cell strings) of the markdown table whose header row
    starts with `| first_header |`."""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("| " + first_header + " |"):
            rows = []
            for r in lines[i + 2:]:
                if not r.startswith("|"):
                    break
                rows.append([c.strip() for c in re.split(r"(?<!\\)\|", r.strip())[1:-1]])
            return rows
    return []


def unquote(s):
    return s.replace('\\"', '"')


# ---------------------------------------------------------------------------
# Sources

def registry():
    t = read("lean2rr/LeanToReussir/Opt/Registry.lean")
    opts = re.findall(r'⟨"([^"]+)", (true|false), "((?:[^"\\]|\\.)*)", \w+\.install⟩', t)
    req = re.findall(r'⟨"([^"]+)", "((?:[^"\\]|\\.)*)",\s*"((?:[^"\\]|\\.)*)"⟩', t)
    st2 = re.findall(r'\.(replace|skip) `(\w+)(?: (\w+))?\s*"((?:[^"\\]|\\.)*)"', t)
    return opts, req, st2


def pass_guards():
    rows = parse_md_table(read("docs/implementation/optional-passes.md"), "Pass")
    out = {}
    for r in rows:
        m = re.match(r"`([^`]+)`", r[0])
        if m and len(r) >= 4:
            out[m.group(1)] = (r[2], r[3])
    return out


def status_pass_names():
    names = set()
    for r in parse_md_table(read("docs/implementation-status.md"), "pass"):
        names.update(re.findall(r"`([^`]+)`", r[0]))
    return names


def runtime_tests():
    d = os.path.join(REPO, "tests/runtime")
    tests = sorted(f[:-5] for f in os.listdir(d) if f.startswith("Rt") and f.endswith(".lean"))
    xfail = sorted(f[:-6] for f in os.listdir(d) if f.endswith(".xfail"))
    return tests, xfail


def env_checks():
    t = read("tests/env/run.sh")
    return re.findall(r"^\s*(?:[A-Z_]+=\S+\s+)*check\s+(\S+)\s+(accept|reject)\b", t, re.M)


def plan_section10():
    m = re.search(r"^## 10\..*?$(.*)", read("docs/translation-plan.md"), re.M | re.S)
    return m.group(1) if m else ""


# ---------------------------------------------------------------------------
# Generated tables

def gen_passes():
    opts, _, _ = registry()
    guards = pass_guards()
    rows = []
    for i, (name, on, desc) in enumerate(opts, 1):
        g = guards.get(name)
        if g is None:
            warn(f"pass {name} is in Opt/Registry.lean but not in docs/implementation/optional-passes.md")
            guard, detail = "(not documented)", ""
        else:
            guard = md_inline(g[0], "docs/implementation")
            detail = md_inline(g[1], "docs/implementation") if g[1] != "below" else \
                md_inline("[optional-passes.md](optional-passes.md)", "docs/implementation")
        rows.append([str(i), f"<code>{html.escape(name)}</code>", "on" if on == "true" else "off",
                     html.escape(unquote(desc)), guard, detail])
    names = [o[0] for o in opts]
    for name in guards:
        if name not in names:
            warn(f"pass {name} is in optional-passes.md but not in Opt/Registry.lean")
    status = status_pass_names()
    for name in names:
        if name not in status:
            warn(f"pass {name} is missing from the pass table of docs/implementation-status.md")
    return md_table(rows, ["#", "Pass", "Default", "What it does (Registry.lean)",
                           "Guard: soundness and other limits (optional-passes.md)", "Details"])


def gen_required():
    _, req, _ = registry()
    rows = [[f"<code>{html.escape(n)}</code>", html.escape(unquote(d)), html.escape(unquote(w))]
            for n, d, w in req]
    return md_table(rows, ["Part", "What it is", "Why it is not optional"])


def gen_stage2():
    _, _, st2 = registry()
    rows = []
    for kind, lean_pass, copy, why in st2:
        what = f"replaced by <code>{html.escape(copy)}</code>" if kind == "replace" else "not run here"
        rows.append([f"<code>{html.escape(lean_pass)}</code>", what, html.escape(unquote(why))])
    return md_table(rows, ["Lean's pass", "In lean2rr", "Why"])


def gen_patches():
    rows = parse_md_table(read("reussir-bugs/README.md"), "#")
    out = []
    for r in rows:
        if len(r) < 8:
            continue
        num, kind, effect, affects, workaround, patch, _review, applied = r[:8]
        out.append([md_inline(c, "reussir-bugs")
                    for c in (num, kind, effect, affects, workaround, patch, applied)])
    if not out:
        warn("no status table found in reussir-bugs/README.md")
    return md_table(out, ["Bug", "Kind", "Effect", "Affects lean2rr output?",
                          "lean2rr workaround", "Patch", "Applied"], "tbl small")


def gen_classic():
    rows = parse_md_table(read("tests/README.md"), "case")
    out = [[f"<code>{html.escape(r[0])}</code>", md_inline(r[1], "tests"), md_inline(r[2], "tests"),
            html.escape(r[3])] for r in rows if len(r) >= 4]
    return md_table(out, ["Case", "Origin", "What it stresses", "Sizes: small / medium / bench"],
                    "tbl small")


def gen_testsets():
    tests, xfail = runtime_tests()
    env = env_checks()
    cases = json.loads(read("tests/classic/cases.json"))
    ncases = len(cases) if isinstance(cases, list) else len(cases.get("cases", []))
    nacc = sum(1 for _, k in env if k == "accept")
    rows = [
        ["Runtime suite", "<code>tests/runtime/run.sh</code>",
         f"{len(tests)} programs (<code>Rt*.lean</code>), {len(xfail)} marked <code>.xfail</code>",
         "small programs, one feature or one finding each; native build against lean2rr build"],
        ["Classic corpus", "<code>tests/oracle.py</code>", f"{ncases} programs × 3 sizes",
         "benchmark programs; outputs recorded from the native build"],
        ["Corpus, passes off", "<code>L2R_DISABLE_OPTS=…</code>", f"the same {ncases} programs",
         "the core translation alone must also match native"],
        ["Loader checks", "<code>tests/env/run.sh</code>",
         f"{len(env)} cases ({nacc} accept, {len(env) - nacc} reject)",
         "which program modules lean2rr accepts; <code>--stats</code> on polymorphic recursion"],
        ["Reussir benchmark suite", "<code>tests/reussir-benchmark/run.sh</code>",
         "18 Lean programs, unchanged", "the suite's own programs, built natively and through lean2rr"],
        ["leanrt unit tests", "<code>tests/runtime/leanrt-unit.sh</code>", "Rust tests",
         "big numbers, one-word Nat/Int, tagged arrays, string layout and counts, a FILE model differential test"],
        ["lean-runtime's rows", "<code>tests/runtime/rows-check.sh</code>", "every row of lean-runtime",
         "lean-runtime's row oracle built with lean2rr against the rows' native values"],
        ["Inlined textures", "<code>tests/runtime/ffi-inline-check.sh</code>", "7 runtime tests",
         "no call through the FFI boundary in their LLVM IR (it would keep a loop's tail call)"],
        ["Big-number counters", "<code>tests/runtime/nat-alloc-check.sh</code>", "2 sizes",
         "every big number made is freed exactly once; big constants made once"],
        ["Conversion counter", "<code>tests/runtime/conv-count-check.sh</code>", "2 sizes",
         "uniform-updates: conversions grow at most linearly; a counter emitted in an undone cast probe is emitted again"],
        ["Reussir repros", "<code>reussir-bugs/repros/run.sh</code>", "one per Reussir bug",
         "REPRODUCES or FIXED for each bug, on a given rrc"],
    ]
    return md_table(rows, ["Set", "Runner", "Size (counted from the repository)", "What it checks"])


def gen_xfail():
    _, xfail = runtime_tests()
    if not xfail:
        return "<p>No test is marked <code>.xfail</code>.</p>"
    items = []
    for x in xfail:
        first = read(f"tests/runtime/{x}.xfail").strip().splitlines()[0]
        items.append(f"<li><code>{html.escape(x)}</code>: {html.escape(first)}</li>")
    return "<ul>" + "".join(items) + "</ul>"


def code_spans(s):
    return re.sub(r"`([^`]+)`", r"<code>\1</code>", html.escape(s))


def section10_groups():
    groups = []
    cur = None
    for line in plan_section10().splitlines():
        g = re.match(r"^\*\*([^*]+)\*\*", line)
        if g:
            cur = [g.group(1).strip(), []]
            groups.append(cur)
            continue
        it = re.match(r"^- \*([^*]+)\*", line)
        if it and cur is not None:
            cur[1].append(it.group(1).strip())
        elif re.match(r"^- \S", line) and cur is not None:
            words = re.sub(r"[`*]", "", line[2:]).split()
            cur[1].append(" ".join(words[:8]) + " …")
    return groups


def gen_diffindex():
    groups = section10_groups()
    if not groups:
        warn("could not read the groups of plan §10")
        return ""
    out = []
    for name, items in groups:
        lis = "".join(f"<li>{code_spans(i)}</li>" for i in items) or "<li>(no items)</li>"
        out.append(f'<div class="idxgrp"><h4>{html.escape(name)}</h4><ul>{lis}</ul></div>')
    return '<div class="idx">' + "".join(out) + "</div>"


def gen_leanbugs():
    for name, items in section10_groups():
        if name.startswith("Runtime: Lean bugs we do not reproduce"):
            lis = "".join(f"<li>{code_spans(i)}</li>" for i in items)
            return (f"<p>Plan §10 lists them, each with the native behaviour, lean2rr's "
                    f"behaviour and its test:</p><ul>{lis}</ul>")
    return ('<div class="note"><p><strong>In progress.</strong> The list of Lean runtime '
            'bugs that lean2rr does not reproduce is not in plan §10 yet. This section '
            'shows its items once it is.</p></div>')


GENERATORS = {
    "passes": gen_passes,
    "required": gen_required,
    "stage2": gen_stage2,
    "patches": gen_patches,
    "classic": gen_classic,
    "testsets": gen_testsets,
    "xfail": gen_xfail,
    "diffindex": gen_diffindex,
    "leanbugs": gen_leanbugs,
}


# ---------------------------------------------------------------------------
# Short values

def values():
    tool = read("lean2rr/lean-toolchain").strip()
    tests, xfail = runtime_tests()
    opts, req, _ = registry()
    rb = read("reussir-bugs/README.md")
    m = re.search(r"branch `l2r-local` \(head `([0-9a-f]+)`\)", rb)
    rhead = m.group(1) if m else "?"
    m = re.search(r"for p in (.*?); do", rb, re.S)
    applied = re.findall(r"\b0\d{3}\b", m.group(1)) if m else []
    m2 = re.search(r"the (\d+) local patches", rb)
    if m2 and int(m2.group(1)) != len(applied):
        warn(f"reussir-bugs/README.md says {m2.group(1)} local patches; its apply list has {len(applied)}")
    m3 = re.search(r"Runtime test suite \((\d+) programs", read("docs/implementation-status.md"))
    if m3 and int(m3.group(1)) != len(tests):
        warn(f"docs/implementation-status.md says {m3.group(1)} runtime tests; tests/runtime has {len(tests)}")
    return {
        "lean": tool.split(":")[-1],
        "rt_tests": str(len(tests)),
        "rt_xfail": str(len(xfail)),
        "env_cases": str(len(env_checks())),
        "opt_count": str(len(opts)),
        "req_count": str(len(req)),
        "reussir_head": rhead,
        "patches_applied": str(len(applied)),
        "bug_entries": str(len(parse_md_table(rb, "#"))),
    }


# ---------------------------------------------------------------------------
# Rendering

TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title} · lean2rr design</title>
<link rel="stylesheet" href="style.css">
</head>
<body>
<header class="top">
  <div class="brand"><a href="index.html">lean2rr</a> <span>architecture and design</span></div>
  <nav class="main">{nav}</nav>
</header>
<div class="layout">
  <aside class="toc"><div class="tochead">On this page</div>{toc}</aside>
  <main>
{body}
  </main>
</div>
<footer>Generated by <code>docs/site/build.py</code> from the repository's files (Lean {lean}).
This site summarizes; the markdown documents in the repository are the authority.</footer>
</body>
</html>
"""


def repo_links(text):
    text = re.sub(r"\]\(repo:([^)\s]+)\)", lambda m: f"]({REPO_REL}{m.group(1)})", text)
    return re.sub(r'href="repo:([^"]+)"', lambda m: f'href="{REPO_REL}{m.group(1)}"', text)


def render_page(name, title, vals):
    src = open(os.path.join(SITE, "pages", name + ".md"), encoding="utf-8").read()
    blocks = {}

    def stash(html_text):
        key = f"XXBLOCK{len(blocks)}XX"
        blocks[key] = html_text
        return "\n\n" + key + "\n\n"

    def sub_block(m):
        kind, key = m.group(1), m.group(2)
        table = diagrams.DIAGRAMS if kind == "svg" else GENERATORS
        fn = table.get(key)
        if not fn:
            warn(f"{name}.md: unknown {kind} {key}")
            return ""
        return stash(fn() if kind == "svg" else fn())

    src = re.sub(r"\{\{(svg|gen):([\w-]+)\}\}", sub_block, src)

    def sub_value(m):
        if m.group(1) not in vals:
            warn(f"{name}.md: unknown value {m.group(1)}")
            return "?"
        return vals[m.group(1)]

    src = re.sub(r"\{\{v:([\w-]+)\}\}", sub_value, src)
    src = repo_links(src)
    md = markdown.Markdown(extensions=["tables", "toc", "attr_list", "md_in_html",
                                       "fenced_code", "sane_lists", "def_list"],
                           extension_configs={"toc": {"toc_depth": "2-3"}})
    body = md.convert(src)
    for key, val in blocks.items():
        body = body.replace(f"<p>{key}</p>", val).replace(key, val)
    nav = "".join(f'<a href="{p}.html"{HERE if p == name else ""}>{html.escape(t)}</a>'
                  for p, t in PAGES)
    return TEMPLATE.format(title=html.escape(title), nav=nav, toc=md.toc, body=body,
                           lean=vals["lean"])


HERE = ' class="here"'


def forbidden_in(text):
    low = text.lower()
    return [f for f in FORBIDDEN if f.lower() in low]


def main():
    ap = argparse.ArgumentParser(description="Build the lean2rr design site.")
    ap.add_argument("--check", action="store_true",
                    help="write nothing; fail if a page would change or a warning comes up")
    args = ap.parse_args()
    errors = []
    # The site's own sources must be public-clean too.
    for d in (SITE, os.path.join(SITE, "pages")):
        for f in sorted(os.listdir(d)):
            # build.py holds the list itself.
            if f.endswith((".py", ".md", ".css")) and f != "build.py":
                bad = forbidden_in(open(os.path.join(d, f), encoding="utf-8").read())
                if bad:
                    errors.append(f"{os.path.relpath(os.path.join(d, f), SITE)}: forbidden {bad}")
    vals = values()
    pages = {}
    for name, title in PAGES:
        out = render_page(name, title, vals)
        bad = forbidden_in(out)
        if bad:
            errors.append(f"{name}.html: forbidden {bad}")
        pages[name] = out
    if errors:
        for e in errors:
            print("error:", e, file=sys.stderr)
        print("nothing written: the site must not contain these strings", file=sys.stderr)
        return 1
    changed = []
    for name, out in pages.items():
        path = os.path.join(SITE, name + ".html")
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != out:
            changed.append(name + ".html")
            if not args.check:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(out)
    if args.check:
        if changed:
            print("out of date: " + ", ".join(changed) + " (run docs/site/build.py)", file=sys.stderr)
        return 1 if (changed or WARNINGS) else 0
    print(f"{len(pages)} pages, {len(changed)} changed, {len(WARNINGS)} warning(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
