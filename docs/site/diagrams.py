"""Inline SVG diagrams for the lean2rr site.

Each public function returns an HTML <figure> with an inline <svg>. The
pages refer to them as {{svg:NAME}} (see build.py, which collects every
function listed in DIAGRAMS). Colours come from CSS classes (style.css),
so the diagrams follow the page's light or dark theme.

Coordinates are hand-placed. To change a diagram, edit its function and
run build.py; open the page to check the result. SVG text does not wrap:
keep box labels short.
"""

import html

CHAR_W = 7.0      # approximate width of one character at 13 px
SMALL_W = 6.2     # at 11.5 px
LINE_H = 17


def esc(s):
    return html.escape(s, quote=True)


class SVG:
    def __init__(self, name, width, height, title, caption=None):
        self.name = name
        self.w = width
        self.h = height
        self.title = title
        self.caption = caption
        self.parts = []

    # -- primitives -------------------------------------------------------

    def box(self, x, y, w, h, lines, cls="b-l2r", head=True, small_after=1,
            align="middle", rx=6):
        """A rounded box. lines[0] is bold when head; lines after
        small_after are drawn small."""
        self.parts.append(
            f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" class="{cls}"/>')
        n = len(lines)
        total = 0
        sizes = []
        for i, _ in enumerate(lines):
            sz = 15 if (i < small_after) else 14
            sizes.append(sz)
            total += sz
        ty = y + (h - total) / 2 + 12
        for i, s in enumerate(lines):
            if align == "middle":
                tx, anchor = x + w / 2, "middle"
            else:
                tx, anchor = x + 10, "start"
            tcls = "tb" if (head and i == 0) else ("t" if i < small_after else "ts")
            self.parts.append(
                f'<text x="{tx}" y="{ty:.1f}" text-anchor="{anchor}" class="{tcls}">{esc(s)}</text>')
            ty += sizes[i] + 1
        return (x, y, w, h)

    def text(self, x, y, s, cls="ts", anchor="start"):
        self.parts.append(
            f'<text x="{x}" y="{y}" text-anchor="{anchor}" class="{cls}">{esc(s)}</text>')

    def line(self, x1, y1, x2, y2, cls="ln"):
        self.parts.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" class="{cls}"/>')

    def arrow(self, x1, y1, x2, y2, label=None, cls="ar", lx=None, ly=None,
              anchor="start", lcls="ts"):
        self.parts.append(
            f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" class="{cls}" '
            f'marker-end="url(#{self.name}-ah)"/>')
        if label:
            if lx is None:
                lx = (x1 + x2) / 2 + 6
            if ly is None:
                ly = (y1 + y2) / 2 + 4
            self.text(lx, ly, label, lcls, anchor)

    def path(self, d, cls="ar", head=True):
        mk = f' marker-end="url(#{self.name}-ah)"' if head else ""
        self.parts.append(f'<path d="{d}" class="{cls}" fill="none"{mk}/>')

    def rect(self, x, y, w, h, cls, rx=0):
        self.parts.append(
            f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" class="{cls}"/>')

    # -- output -----------------------------------------------------------

    def render(self):
        defs = (f'<defs><marker id="{self.name}-ah" viewBox="0 0 10 10" refX="9" '
                f'refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
                f'<path d="M 0 0 L 10 5 L 0 10 z" class="ah"/></marker></defs>')
        svg = (f'<svg class="diagram" viewBox="0 0 {self.w} {self.h}" '
               f'width="{self.w}" role="img" aria-labelledby="{self.name}-title">'
               f'<title id="{self.name}-title">{esc(self.title)}</title>'
               + defs + "".join(self.parts) + "</svg>")
        cap = f"<figcaption>{self.caption}</figcaption>" if self.caption else ""
        return f'<figure class="fig" id="fig-{self.name}">{svg}{cap}</figure>'


def bar(svg, x, y, cells, unit=9.0, h=34, offsets=True, start=0):
    """A memory layout: cells = [(label, bytes, cls)]. Draws the byte
    offset of each cell above it. bytes may be a string ("n×8") for an
    open-ended part, drawn 120 px wide with a ragged end."""
    off = start
    cx = x
    for label, size, cls in cells:
        if isinstance(size, str):
            w = 130
            svg.rect(cx, y, w, h, cls)
            svg.parts.append(
                f'<path d="M {cx + w} {y} l -6 {h / 4} l 6 {h / 4} l -6 {h / 4} l 6 {h / 4}" class="rag"/>')
            svg.text(cx + w / 2, y + h / 2 + 5, label, "tc", "middle")
            if offsets:
                svg.text(cx, y - 5, str(off), "to", "middle")
            cx += w
            off = None
        else:
            w = size * unit
            svg.rect(cx, y, w, h, cls)
            svg.text(cx + w / 2, y + h / 2 + 5, label, "tc", "middle")
            if offsets and off is not None:
                svg.text(cx, y - 5, str(off), "to", "middle")
                off += size
            cx += w
    if offsets and off is not None:
        svg.text(cx, y - 5, str(off), "to", "middle")
    return cx


# ---------------------------------------------------------------------------
# Overview

def overview_flow():
    s = SVG("flow", 940, 270, "From a Lean program to two executables",
            "Both builds start from the same <code>.olean</code> files. "
            "The native build is the reference: tests compare the two executables' "
            "standard output, standard error and exit code.")
    s.box(10, 100, 110, 60, ["Lean program", ".lean files"], "b-lean")
    s.arrow(120, 130, 175, 130)
    s.text(149, 150, "lake build", "ts", "middle")
    s.box(180, 92, 150, 76, ["Compiled modules", ".olean files", "(LCNF code inside)"], "b-lean")
    # native path
    s.path("M 330 115 C 360 115 360 45 390 45")
    s.box(395, 18, 240, 56, ["Lean's own back end", "C code, leanc, Lean's C runtime"], "b-lean")
    s.arrow(635, 46, 690, 46)
    s.box(695, 18, 150, 56, ["native build", "executable"], "b-lean")
    # lean2rr path
    s.path("M 330 145 C 360 145 360 205 390 205")
    s.box(395, 175, 110, 60, ["lean2rr", "translator"], "b-l2r")
    s.arrow(505, 205, 540, 205)
    s.box(545, 175, 110, 60, ["prog.rr", "Reussir source"], "b-l2r")
    s.arrow(655, 205, 690, 205)
    s.box(695, 175, 150, 60, ["rrc (Reussir)", "+ leanrt, GMP"], "b-rr")
    s.arrow(770, 175, 770, 136)
    s.box(695, 96, 150, 40, ["lean2rr build"], "b-rr")
    # compare
    s.box(865, 60, 66, 100, ["same", "stdout", "stderr", "exit"], "b-test", small_after=1)
    s.line(845, 46, 865, 80, "ln")
    s.line(845, 116, 865, 120, "ln")
    return s.render()


# ---------------------------------------------------------------------------
# Pipeline

def pipeline():
    s = SVG("pipe", 940, 1005, "The lean2rr pipeline, stage by stage",
            "The pipeline as <code>lean2rr/Main.lean</code> runs it. The right "
            "column names the <code>--emit</code> option that stops after a "
            "step and prints its output.")
    X, W = 160, 470
    ys = []

    def step(y, h, lines, cls, emit=None, left=None):
        s.box(X, y, W, h, lines, cls, small_after=1, align="start")
        if emit:
            s.text(X + W + 20, y + h / 2 + 4, emit, "tcode")
        if left:
            for i, l in enumerate(left):
                s.text(X - 12, y + 18 + i * 15, l, "ts", "end")
        ys.append((y, h))

    def link(y_from, y_to, label=None):
        s.arrow(X + W / 2, y_from, X + W / 2, y_to - 2, label, lx=X + W / 2 + 10)

    step(10, 50, [".olean files of the program and of Lean's library",
                  "base LCNF: typed, polymorphic, A-normal form"], "b-lean",
         left=["input"])
    link(60, 82)
    step(84, 64, ["Loading (Env)",
                  "import every module with its extension states",
                  "check that Init/Std/Lean/Lake/L2RShim modules are the real ones"],
         "b-l2r", left=["Env.lean"])
    link(148, 170, "every declaration reachable from main and the startup work")
    step(172, 96, ["Stage 1: collect and monomorphize",
                   "one instance per list of type arguments, with a fresh name",
                   "static dictionaries specialize their callee",
                   "calls that Lean's cse merges across types are aligned",
                   "polymorphic recursion goes to the uniform instance (lcAny)"],
         "b-l2r", emit="--emit base, inst", left=["Collect.lean", "Mono.lean"])
    link(268, 290, "monomorphic base LCNF, a closed program")
    step(292, 96, ["Stage 2: Lean's own mono pipeline",
                   "Lean's passes in Lean's order: simp, cse, lambda lifting, ...",
                   "toMono, structProjCases: lean2rr copies that keep more types",
                   "inferVisibility, toImpure: not run",
                   "extractClosed: run last, as Lean ran it"],
         "b-lean", emit="--emit mono, externs", left=["Pipeline.lean", "Passes.lean"])
    link(388, 410, "mono LCNF with exact types (a few lcAny left)")
    step(412, 80, ["Stage 3: check and recover lost types",
                   "types flow from definitions, never from uses",
                   "split-map-loops, uniform-updates (optional passes)",
                   "typed references (typedRef)"],
         "b-l2r", emit="--emit retyped", left=["MonoRetype.lean", "Opt/*"])
    link(492, 514, "checked mono LCNF")
    step(516, 40, ["passes over mono LCNF (float-lits)"], "b-opt",
         left=["Opt/FloatLits"])
    link(556, 578)
    step(580, 112, ["Stage 4: lower to Reussir",
                    "types: records, enums, Box, function-value enums",
                    "declarations with Lean's arities; join points J1 to J4",
                    "externs: prelude functions and generated glue",
                    "startup chain, constants in once-cells, the entry point",
                    "lowering hooks of the optional passes"],
         "b-l2r", left=["Lower/*.lean", "Emit/*.lean"])
    link(692, 714, "Reussir functions and types")
    step(716, 64, ["After lowering",
                   "Array Nat literal tables, Outline (long code cut for rrc)",
                   "passes over the generated functions (sink-proj)"],
         "b-l2r", emit="--emit rr", left=["ArrayLits", "Outline", "Opt/SinkProj"])
    link(780, 802, "prog.rr: the program text, prelude.rr prepended")
    step(804, 80, ["rrc: Reussir",
                   "Reussir front end, then MLIR passes:",
                   "reference counting (Perceus), token reuse, drop glue",
                   "LLVM: optimization and code generation"],
         "b-rr", left=["scripts/l2r.py", "runs rrc"])
    link(884, 906, "object code, linked with the leanrt rlib and GMP")
    step(908, 44, ["executable (position-independent, as native)"], "b-rr")
    s.text(X, 990, "Colours: blue = Lean's code or Lean's passes; green = lean2rr; "
           "yellow = optional pass; orange = Reussir.", "ts")
    return s.render()


def joinpoints():
    s = SVG("jp", 900, 250, "How a join point is lowered",
            "The strategies are tried in this order. Every strategy runs the "
            "join point's body once on each path that jumps to it.")
    y = 30
    s.box(10, y, 150, 70, ["Join point j", "Lean's local", "continuation"], "b-lean")
    xs = [200, 370, 540]
    qs = [["J1: one jump?", "inline the body", "at the jump"],
          ["J2: every path", "ends in jmp j?", "let + body after"],
          ["J1': small?", "copy the body", "at each jump"]]
    prev = 160
    for x, q in zip(xs, qs):
        s.arrow(prev, y + 35, x, y + 35, "no" if prev != 160 else None, lx=prev + 6, ly=y + 28)
        s.box(x, y, 140, 70, q, "b-l2r")
        s.arrow(x + 70, y + 70, x + 70, y + 130, "yes", lx=x + 76)
        s.box(x, y + 132, 140, 34, ["structured code"], "b-ok")
        prev = x + 140
    s.arrow(prev, y + 35, 710, y + 35, "no", lx=prev + 6, ly=y + 28)
    s.box(710, y, 180, 70, ["J3: outline", "a function, called", "in tail position"], "b-rr")
    s.arrow(800, y + 70, 800, y + 130, "body tail-calls f?", lx=806)
    s.box(710, y + 132, 180, 52, ["J4: one state machine", "for f and its join points"], "b-rr")
    s.text(10, 238, "J1' (jp-small) and the J4 slots (state-machines) are optional passes; "
           "jp-sink moves join points down first.", "ts")
    return s.render()


def reussir_path():
    s = SVG("rrc", 900, 170, "What rrc does with prog.rr",
            "<code>scripts/l2r.py</code> runs <code>rrc</code> with "
            "<code>-O aggressive --no-pack-record-members --reuse-across-call "
            "--no-closure-wpd --relocation-mode pic</code>.")
    s.box(10, 40, 120, 60, ["prog.rr", "with prelude"], "b-l2r")
    s.arrow(130, 70, 160, 70)
    s.box(165, 30, 150, 80, ["Reussir front end", "parse, types,", "textures (Rust FFI)"], "b-rr")
    s.arrow(315, 70, 345, 70)
    s.box(350, 20, 220, 100, ["MLIR passes", "ownership: rc.inc / rc.dec", "token reuse (cells used", "again in place)", "drop glue"], "b-rr")
    s.arrow(570, 70, 600, 70)
    s.box(605, 30, 130, 80, ["LLVM", "optimization,", "code generation"], "b-rr")
    s.arrow(735, 70, 765, 70)
    s.box(770, 30, 120, 80, ["link", "leanrt.rlib", "libgmp.a"], "b-rt")
    s.text(10, 150, "Textures (the Rust bodies of #[ffi(import)] functions) are compiled by rustc "
           "and can be inlined into Reussir code.", "ts")
    return s.render()


# ---------------------------------------------------------------------------
# Representations

def nat_word():
    s = SVG("natword", 900, 215, "One-word Nat and Int",
            "A <code>Nat</code> or <code>Int</code> is one 64-bit word. Reussir "
            "counts the word only when its low bit is 0 (tagged handles, local "
            "patch 0050).")
    s.text(10, 28, "small value n (a Nat below 2^63, an Int in the int32 range): the word 2n+1", "t")
    s.rect(10, 40, 440, 34, "c-data")
    s.text(230, 62, "n  (bits 63 to 1)", "tc", "middle")
    s.rect(450, 40, 40, 34, "c-tag")
    s.text(470, 62, "1", "tc", "middle")
    s.text(10, 108, "big value: an even word, the address of a counted big-number block", "t")
    s.rect(10, 120, 440, 34, "c-ptr")
    s.text(230, 142, "address (8-aligned)", "tc", "middle")
    s.rect(450, 120, 40, 34, "c-tag")
    s.text(470, 142, "0", "tc", "middle")
    s.arrow(490, 137, 555, 137)
    s.box(560, 117, 300, 40, ["big-number block (next figure)"], "b-rt")
    s.text(10, 192, "Copying or dropping a small value costs one bit test. A small value is never allocated.", "ts")
    return s.render()


def big_block():
    s = SVG("bigblk", 900, 110, "A big number: one block",
            "One <code>mi_malloc</code> block per big number (native Lean: two, "
            "the object and GMP's limbs). The size is negative for a negative "
            "<code>Int</code>. GMP's <code>mpn</code> functions work on the limbs.")
    bar(s, 10, 40, [("count", 4, "c-hdr"), ("flags", 4, "c-hdr"),
                    ("size", 4, "c-hdr"), ("cap", 4, "c-hdr"),
                    ("limb 0", 8, "c-data"), ("limb 1", 8, "c-data"),
                    ("more limbs ...", "n", "c-data")], unit=16)
    s.text(10, 100, "count: u32 reference count; flags: u32, reserved; size: i32 limbs in use (negative: a negative Int); cap: u32 room for limbs", "ts")
    return s.render()


def lstr_block():
    s = SVG("lstr", 900, 100, "A string: one block",
            "<code>LStr</code>: a 32-byte header as Lean's string object, then "
            "the UTF-8 bytes (no terminator). The character count makes "
            "<code>String.length</code> a field read.")
    bar(s, 10, 40, [("count", 4, "c-hdr"), ("pad", 4, "c-pad"),
                    ("byte size", 8, "c-hdr"), ("capacity", 8, "c-hdr"),
                    ("chars", 8, "c-hdr"), ("UTF-8 bytes ...", "n", "c-data")], unit=16)
    return s.render()


def rvec_block():
    s = SVG("rvec", 900, 180, "Arrays: one block",
            "<code>RVec&lt;S&gt;</code> (<code>Array α</code>, <code>ByteArray</code>, "
            "<code>FloatArray</code>) and <code>TagVec</code> (<code>Array Nat</code>, "
            "<code>Array Int</code>) have Lean's 24-byte array header, then the "
            "elements inline.")
    s.text(10, 26, "RVec<S>: elements in their storage type S (at most 8 bytes each)", "t")
    bar(s, 10, 44, [("count", 4, "c-hdr"), ("pad", 4, "c-pad"),
                    ("size", 8, "c-hdr"), ("capacity", 8, "c-hdr"),
                    ("elem 0", 8, "c-data"), ("elem 1", 8, "c-data"),
                    ("more ...", "n", "c-data")], unit=16)
    s.text(10, 114, "TagVec: each element is the Nat's or Int's own word (odd: small; even: big pointer)", "t")
    bar(s, 10, 132, [("count", 4, "c-hdr"), ("pad", 4, "c-pad"),
                     ("size", 8, "c-hdr"), ("capacity", 8, "c-hdr"),
                     ("2n+1", 8, "c-data"), ("address", 8, "c-ptr"),
                     ("more words ...", "n", "c-data")], unit=16)
    return s.render()


def record_cells():
    s = SVG("rec", 900, 330, "Generated records and enums",
            "Reussir lays out the cells; lean2rr chooses the shape and the field "
            "order. A cell's header is a 32-bit count, and for an enum variant "
            "also the tag (one 8-byte header word).")
    s.text(10, 24, "structure P where a : UInt8; b : Nat; c : Float  →  shared struct, fields by decreasing alignment", "t")
    bar(s, 10, 40, [("count", 4, "c-hdr"), ("", 4, "c-pad"),
                    ("b : Nat", 8, "c-data"), ("c : f64", 8, "c-data"),
                    ("a : u8", 4, "c-data")], unit=16, offsets=False)
    s.text(10, 120, "Tree.node l k r  →  a variant cell of the shared enum T_Tree (count and tag in one word)", "t")
    bar(s, 10, 136, [("count", 4, "c-hdr"), ("tag", 4, "c-tag"),
                     ("l : T_Tree", 8, "c-ptr"), ("k : Nat", 8, "c-data"),
                     ("r : T_Tree", 8, "c-ptr")], unit=16, offsets=False)
    s.text(10, 214, "Tree.leaf (a constructor without fields): an immediate, a tagged pointer to a static cell; no allocation", "t")
    s.text(10, 238, "Ordering (no fields anywhere): enum [value], a small integer; no allocation", "t")
    s.text(10, 262, "ST.Out α (one relevant field): [value] struct, the field itself, stored inline", "t")
    s.text(10, 286, "Option α, Except ε α, List α, user types: one Reussir type per instantiation of their relevant parameters", "t")
    s.text(10, 310, "The widths are schematic (a : u8 is one byte): Reussir computes the real layout.", "ts")
    return s.render()


def box_uniform():
    s = SVG("box", 900, 240, "The uniform type L2RBox",
            "A value whose type is not statically known (<code>lcAny</code>) is an "
            "<code>L2RBox</code>: a generated shared enum with one variant per "
            "type the program boxes. Conversions go in and out of it.")
    s.box(10, 30, 170, 60, ["List Nat", "precise representation"], "b-l2r")
    s.box(10, 140, 170, 60, ["Nat → Nat", "function-value enum"], "b-l2r")
    s.arrow(180, 60, 330, 95, "box: wrap in its variant", lx=190, ly=60)
    s.arrow(180, 170, 330, 125)
    s.box(335, 70, 220, 90, ["L2RBox", "b0 (the boxed unit)", "b1(List Nat)", "b2(Nat → Nat), ..."], "b-rt")
    s.arrow(555, 115, 690, 115, "unbox", lx=622, ly=105, anchor="middle")
    s.text(622, 135, "(generated)", "ts", "middle")
    s.box(695, 70, 195, 90, ["precise use", "matches every variant", "that can hold the type;", "converts if needed"], "b-l2r")
    s.text(10, 228, "Typed code never pays for Box. It appears only on the rare paths: polymorphic recursion, existentials, Dynamic.", "ts")
    return s.render()


def lazy_cells():
    s = SVG("lazy", 900, 300, "Thunks and tasks",
            "<code>Thunk α</code> and <code>Task α</code> are a runtime cell "
            "(<code>LCell</code>) that holds a generated state. The closure "
            "runs at most once.")
    bar(s, 10, 44, [("count", 4, "c-hdr"), ("entry", 4, "c-tag"),
                    ("state S", 8, "c-ptr")], unit=16)
    s.text(10, 26, "LCell<S>: one runtime cell, seen through every alias", "t")
    s.text(10, 104, "count: u32 reference count; entry: the task's index in leanrt::task's table (tasks only); state: the generated enum", "ts")
    # state machine
    s.box(20, 140, 150, 50, ["pending(f)", "not run yet"], "b-l2r")
    s.arrow(170, 165, 260, 165, "forced", lx=185, ly=158)
    s.box(265, 140, 150, 50, ["busy", "f is running"], "b-rr")
    s.arrow(415, 165, 505, 165, "f returns v", lx=420, ly=158)
    s.box(510, 140, 150, 50, ["done(v)", "value stored"], "b-ok")
    s.box(20, 225, 230, 50, ["conv(g, o[, a])", "a copy at another representation"], "b-rt")
    s.box(280, 225, 230, 50, ["bind(f)", "a bind task not started"], "b-rt")
    s.text(540, 245, "conv: g forces the original o;", "ts")
    s.text(540, 262, "a task's a is the original's identity.", "ts")
    s.text(690, 160, "busy forced again by its own", "ts")
    s.text(690, 176, "computation: waits forever,", "ts")
    s.text(690, 192, "as natively.", "ts")
    return s.render()


def fn_values():
    s = SVG("fnv", 900, 170, "Function values",
            "A function value is a generated shared enum per function type. "
            "<code>l2r_ap&lt;j&gt;_T</code> matches the variant and calls the target "
            "when its last argument arrives, as <code>lean_apply_n</code>.")
    s.text(10, 24, "fun x => f a b x  (f of arity 3)  →  the variant p2_f with two captured values", "t")
    bar(s, 10, 40, [("count", 4, "c-hdr"), ("tag", 4, "c-tag"),
                    ("a", 8, "c-data"), ("b", 8, "c-data")], unit=16, offsets=False)
    s.text(10, 116, "Other variants: p0_f (nullary: no allocation), raw(...) (a Reussir closure from glue),", "ts")
    s.text(10, 134, "w_S(g) (a value of another representation, wrapped once), z (the placeholder).", "ts")
    return s.render()


def ref_cells():
    s = SVG("ref", 900, 120, "References",
            "<code>ST.Ref</code>/<code>IO.Ref</code>: a generated shared record "
            "around a Reussir cell. Every alias shares the record, so updates are "
            "seen everywhere. Two allocations (Lean: one).")
    s.box(10, 30, 210, 60, ["L2RRefN", "shared record (count, cell)"], "b-l2r")
    s.arrow(220, 60, 300, 60)
    s.box(305, 30, 230, 60, ["Cell<E>", "the value, in its own type"], "b-rr")
    s.text(560, 55, "set: store the new value, then release the old one", "ts")
    s.text(560, 72, "take: move the value out, leave the placeholder", "ts")
    return s.render()


# ---------------------------------------------------------------------------
# Runtime

def layers():
    s = SVG("layers", 940, 400, "The layers of a lean2rr build",
            "Every lean2rr build has these layers. The planned shared crate "
            "<code>lean-runtime</code> takes over the semantics of leanrt; the "
            "glue to lean2rr's representations stays in lean2rr.")
    W = 640
    s.box(10, 10, 420, 66, ["Generated program (lean2rr output)",
                           "the program's functions and types, glue for externs,",
                           "startup chain, entry point"], "b-l2r")
    s.box(440, 10, 210, 66, ["L2RShim (Lean)", "UV externs, time, ShareCommon;",
                            "compiled with the program"], "b-l2r")
    s.box(10, 90, W, 66, ["prelude.rr (Reussir source, prepended)",
                         "runtime types, one function per Lean extern (lean_xxx),",
                         "fast paths inline (small Nat), l2r_* primitives for the glue"], "b-rt")
    s.box(10, 170, W, 84, ["leanrt (Rust crate, linked into every program)",
                          "Nat/Int slow paths and big numbers (GMP), strings, arrays, hashes,",
                          "float printing, glibc FILE model, files, processes, once-cells,",
                          "tasks and the scheduler (contexts), Std.Sync, the event loop"], "b-rt")
    s.box(10, 268, W, 50, ["reussir_rt (Reussir's runtime)",
                          "Rc, the pending stack for frees (local patches 0013-0015), mimalloc"], "b-rr")
    s.box(10, 332, W, 50, ["System", "libc, libm (glibc's cbrt), GMP, the kernel"], "b-lean")
    s.box(680, 170, 250, 120, ["lean-runtime (planned)", "a shared crate: Lean's",
                              "runtime semantics in", "safe Rust; lean2rr keeps",
                              "only the glue to its", "own representations"], "b-plan")
    s.path("M 680 212 L 652 212", "ard")
    return s.render()


def startup_seq():
    s = SVG("start", 940, 200, "What the entry point does",
            "As Lean's generated <code>main</code> (EmitC), step by step. An "
            "error in an initializer prints <code>uncaught exception</code> and "
            "exits 1 before <code>main</code>.")
    steps = [("0", ["open libuv's", "descriptors", "(ELF constructor)"]),
             ("1", ["run the", "initializers", "(main thread, 8 MiB)"]),
             ("2", ["start the", "task manager;", "1 GiB thread"]),
             ("3", ["call main", "with the args", "and the world"]),
             ("4", ["run the IO tasks", "still pending", "(final run)"]),
             ("5-6", ["error: print it,", "exit 1; else exit", "with main's code"])]
    x = 10
    for n, lines in steps:
        s.box(x, 40, 140, 80, [f"{n}."] + lines, "b-rt" if n != "3" else "b-l2r")
        if x > 10:
            s.arrow(x - 18, 80, x - 2, 80)
        x += 155
    s.text(10, 160, "Stack overflow in any thread or task prints \"Stack overflow detected. Aborting.\" and exits 134, as natively.", "ts")
    return s.render()


def scheduler():
    s = SVG("sched", 940, 330, "Contexts on one thread",
            "When the running context blocks, the scheduler looks for work in "
            "this order. Contexts never run in parallel.")
    s.box(10, 20, 200, 64, ["running context blocks", "a lock, a promise, IO.wait,", "a sleep"], "b-l2r")
    s.arrow(210, 52, 250, 52)
    rows = [(20, ["1. a suspended context that", "can go on now (in the order", "they became ready)?"],
             ["switch to it"]),
            (104, ["2. a queued task, and a", "worker free for it", "(LEAN_NUM_THREADS, or the CPUs)?"],
             ["start it on a new context"]),
            (188, ["3. a timer, socket or sleeper", "still pending?"],
             ["wait for the first one,", "then look again"])]
    for y, q, a in rows:
        s.box(255, y, 300, 64, q, "b-rt", head=False, small_after=3)
        s.arrow(555, y + 32, 615, y + 32, "yes", lx=568, ly=y + 25)
        s.box(620, y + 7, 300, 50, a, "b-ok", head=False, small_after=2)
    s.arrow(405, 84, 405, 102, "no", lx=412, ly=97)
    s.arrow(405, 168, 405, 186, "no", lx=412, ly=181)
    s.arrow(405, 252, 405, 270, "no", lx=412, ly=265)
    s.box(255, 272, 300, 44, ["nothing can go on: wait forever,", "as a deadlocked native program"], "b-rr", head=False, small_after=2)
    s.text(10, 120, "Effect points (output, exit,", "ts")
    s.text(10, 136, "IO.sleep 0) also let due timers,", "ts")
    s.text(10, 152, "ready contexts and old queued", "ts")
    s.text(10, 168, "tasks run first, as other", "ts")
    s.text(10, 184, "threads would have.", "ts")
    return s.render()


def free_stack():
    s = SVG("free", 940, 190, "Freeing without recursion",
            "Native Lean frees iteratively. Here the runtime's containers and "
            "Reussir's drop glue (local patches 0013-0015) share one stack of "
            "pending work per thread, popped last first.")
    s.box(10, 50, 170, 70, ["last reference", "released", "(count was 1)"], "b-l2r")
    s.arrow(180, 85, 230, 85)
    s.box(235, 30, 260, 110, ["the cell's release function", "releases its members:",
                              "a member whose count ends", "goes on the pending stack", "(no recursion)"], "b-rr")
    s.arrow(495, 85, 545, 85)
    s.box(550, 30, 170, 110, ["pending stack", "(per thread)", "last pushed,", "first popped"], "b-rt")
    s.arrow(720, 85, 770, 85)
    s.box(775, 50, 155, 70, ["outermost free", "pops until empty"], "b-rt")
    s.text(10, 170, "Order: an array from its last element, a record from its last field, as Lean's lean_dec "
           "(one difference: the first cell of a free that user code starts at a record).", "ts")
    return s.render()


def persist_walk():
    s = SVG("persist", 940, 170, "The walk of a closed term for its tasks",
            "Native Lean marks a closed term persistent at its first use and "
            "waits for every task in it. lean2rr's walk does that in two passes, "
            "so the tasks run in the workers' queue order.")
    s.box(10, 40, 170, 80, ["closed term", "evaluated once,", "at first use"], "b-l2r")
    s.arrow(180, 80, 225, 80)
    s.box(230, 30, 290, 100, ["pass 1: collect", "walk the value (a loop, each cell once)",
                              "note the unfinished tasks", "do not look into them"], "b-rt")
    s.arrow(520, 80, 565, 80)
    s.box(570, 30, 360, 100, ["pass 2: wait", "walk again in Lean's order;",
                              "before waiting for a task, run the collected",
                              "tasks that natively come first (priority,",
                              "then creation order)"], "b-rt")
    s.text(10, 160, "Skipped when every task has finished (always at startup). A task the program drops meanwhile is deleted, not run.", "ts")
    return s.render()


# ---------------------------------------------------------------------------
# Testing

def runsh():
    s = SVG("runsh", 940, 260, "tests/runtime/run.sh, one test",
            "Each <code>Rt*.lean</code> test is built twice and run twice. "
            "<code>NAME.args</code>, <code>.stdin</code>, <code>.pipe</code>, "
            "<code>.opts</code> and <code>.xfail</code> files change the run.")
    s.box(10, 95, 140, 60, ["RtName.lean", "(+ .args, .stdin)"], "b-test")
    s.path("M 150 115 C 180 115 180 50 210 50")
    s.path("M 150 135 C 180 135 180 200 210 200")
    s.box(215, 20, 230, 60, ["native build", "lean -c, leanc -O3 -DNDEBUG"], "b-lean")
    s.box(215, 170, 230, 60, ["lean2rr build", "scripts/l2r.py (lean2rr + rrc)"], "b-l2r")
    s.arrow(445, 50, 495, 50)
    s.arrow(445, 200, 495, 200)
    s.box(500, 20, 150, 60, ["run", "LEAN_BACKTRACE=0", "120 s limit"], "b-test")
    s.box(500, 170, 150, 60, ["run", "the same way"], "b-test")
    s.path("M 650 50 C 680 50 680 110 710 110")
    s.path("M 650 200 C 680 200 680 140 710 140")
    s.box(715, 85, 215, 80, ["compare byte for byte:", "stdout, stderr, exit code;",
                             "and no text relocations", "in the lean2rr build"], "b-test")
    s.text(715, 195, "PASS, FAIL, or with NAME.xfail:", "ts")
    s.text(715, 211, "XFAIL (still fails), XPASS (remove .xfail)", "ts")
    return s.render()


def review_cycle():
    s = SVG("review", 940, 210, "Judge, fix, review",
            "Every finding goes through this loop. Every consistently "
            "reproducible lean2rr bug becomes a test in the same commit as its fix.")
    xs = [10, 195, 380, 565, 750]
    labels = [["review round", "reviewers read the code,", "confirm each idea with", "a small program"],
              ["finding", "an id (RV9C-02),", "repro, expected vs got"],
              ["judge", "is it real? a bug, a", "documented difference,", "or no defect?"],
              ["fix", "on its own branch,", "with a regression test", "(tests/runtime)"],
              ["review the fix", "try to break it;", "rework and review again", "until nothing is found"]]
    for x, l in zip(xs, labels):
        s.box(x, 30, 175, 100, l, "b-test" if x != 565 else "b-l2r")
    for a, b in zip(xs, xs[1:]):
        s.arrow(a + 175, 80, b - 2, 80)
    s.path("M 837 130 C 837 180 450 180 450 132")
    s.text(560, 190, "a new finding goes back to the judge", "ts")
    return s.render()


DIAGRAMS = {
    "flow": overview_flow,
    "pipeline": pipeline,
    "joinpoints": joinpoints,
    "rrc": reussir_path,
    "natword": nat_word,
    "bigblock": big_block,
    "lstr": lstr_block,
    "rvec": rvec_block,
    "records": record_cells,
    "box": box_uniform,
    "lazy": lazy_cells,
    "fnvalues": fn_values,
    "refs": ref_cells,
    "layers": layers,
    "startup": startup_seq,
    "scheduler": scheduler,
    "freestack": free_stack,
    "persist": persist_walk,
    "runsh": runsh,
    "review": review_cycle,
}
