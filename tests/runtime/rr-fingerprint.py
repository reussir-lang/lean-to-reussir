#!/usr/bin/env python3
"""Canonical fingerprints of the code lean2rr generates (a `.rr` file).

    rr-fingerprint.py show FILE.rr
        the pay-nothing counts (below), then one line `item KEY HASH` per
        generated item (a function, a type, an `extern` line)
    rr-fingerprint.py compare OLD.rr NEW.rr [--ignore PREFIX]...
        the items of OLD that NEW changed or dropped (keys starting with a
        PREFIX are not compared), and a summary line
    rr-fingerprint.py check BASELINE NEW.rr [--ignore PREFIX]...
        the same, with OLD given by the output of `show` (a baseline file)
    rr-fingerprint.py text FILE.rr KEY
        the canonical text of the items with that key (to see a change)

Only the generated part of the file counts: the text after the line
`// ---- generated types ----` (the runtime prelude before it is the fixed
file runtime/prelude.rr). It is split into items: a line at column 0 that
starts with `fn`, `pub fn`, `enum`, `struct` or `extern` starts one, with
the `#[...]` attribute lines before it.

Each item gets a hash of a canonical form of its text that does not change
when only the program's numbering changes. lean2rr numbers many names with
one counter for the whole program (`fresh`, LowerBase.lean): types
(`T_List_15`, `L2RRef245`, `L2RConvK827`, `Tuple12`, `L2RTask7`), helper
functions (`l2r_zero_836`, `l2r_vconv_301`, `jp_77`), constructors of
some types (a state machine's `j123`), the payload numbers of `Box` (the
prelude's `LAny`: 16 and up, `0x8000` + 16 and up for a leaf type, in the
order the program boxes them) and every local name (`x815`, `kj909`); and
it numbers the instances of each Lean declaration in the order Stage 1
finds them (`l_List_lengthTR___l2r_1____redArg`). A definition added to a
program shifts those numbers for code it does not touch. The canonical
form:
- renames the local names of each item (a lowercase stem and digits,
  `x815`; not the primitive types `u64`, `f64`...) in order of first use:
  `x#1`, `a#2`...;
- names a numbered constructor (`b2`, `j123`, `d0`) by its fields' types
  and its rank among the constructors of its type with the same stem and
  fields: `b[Nat]#0`;
- replaces each numbered type, numbered helper and Lean instance, where it
  is used or defined, also inside a longer name (`l2r_conv_T_T_763_T_T_776`,
  `L2RFn_F4nLStr...13nT_EST_Out_792`, dropping the length prefix `13n`), by
  a label: its name with the number replaced by `#`, and a hash of its own
  canonical definition, refined over four rounds (so `List Nat` and
  `List String` get different labels, and a type keeps its label while its
  layout stays the same);
- replaces a string literal's index, `l2r_str_lit(31)`, by the literal's
  text (from the table in the item `l2r_str_lit`), and the cell index of a
  constant (`l2r_once_get<T>(5)`) by its rank in the item;
- replaces a payload number of `Box` by the label of its type (the program's
  release of each payload type, the item `fn l2r_any_rel_17(x : T) -> unit`,
  gives each number's type): where a box is made or taken apart
  (`l2r_any_of<T>(e, 17)`, `l2r_any_of_fn`, `l2r_any_as`, `l2r_any_raw_as`),
  where an unboxing compares a word's number with it (`let bm12 : u64 =
  17;`), in a `match` arm on a number (`17 => `) in an item that reads a
  box's number (`l2r_any_raw_num`), in the names of the releases and their
  trampolines (`l2r_any_rel_17`, `l2r_any_rel_17_c`) and in the table that
  installs them (`leanrt::any::Rel(17, ...)`).

The key of an item is its name with the numbers replaced by `#` (labels
inside longer names); several items can share a key (the instances of one
declaration at several types, several `List` types). Comparing two
programs, the items of one key in OLD must all be in NEW with the same
hash: a key with one item on each side whose hash differs is `changed`,
any other OLD item without its hash in NEW is `dropped`.

Counts printed by `show` (the "pay nothing" markers; a program without
values of unknown type has few, all from the runtime's own startup code):
- `conversion-fns`: generated conversion helpers (`l2r_conv_*`,
  `l2r_vconv_*`, `l2r_fconv_*`, `l2r_lazyconv_*`, `l2r_unbox_*`);
- `conversion-sites`: the uses of those helpers in the other items;
- `box-sites`: values put into a `Box` (a call of `l2r_any_of`,
  `l2r_any_of_fn`, `l2r_any_of_<scalar>` or `l2r_any_imm`) in the items
  other than conversion helpers;
- `box-variants`: the program's pointer payload types of `Box` (the items
  `l2r_any_rel_N`, one per type);
- `items`, `functions`: the generated items, and the functions among them.

Standard library only. Used by tests/runtime/determinism-check.sh and
tests/runtime/paynothing-check.sh.
"""
import collections
import hashlib
import re
import sys

GEN_MARK = "// ---- generated types ----"
ITEM_START = re.compile(r"^(?:pub )?(?:fn|enum|struct|extern)\b")
NAME = re.compile(r"^(?:pub )?(fn|enum|struct)\s+(?:\[[^\]]*\]\s+)?([A-Za-z_][A-Za-z0-9_]*)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
LOCAL = re.compile(r"^([a-z]+)(\d+)$")
PRIMS = {f"{p}{n}" for p in "ui" for n in (8, 16, 32, 64, 128)} | {"f32", "f64"}
# Helper functions named with lean2rr's counter (`fresh "l2r_zero_"`,
# `fresh "l2r_vconv_"`, `fresh "jp_"`), and their companions
# (`l2r_zero_N_init`, `l2r_vconv_N_go`).
FRESH_FN = re.compile(r"^(l2r_zero_|l2r_vconv_|jp_)(\d+)(_[A-Za-z0-9_]*)?$")
# The number of a Lean declaration's instance (`freshInstName`, Mono.lean:
# `decl._l2r.k`, mangled `decl___l2r_k_`).
INST = re.compile(r"___l2r_\d+_")
CONV_FN = re.compile(r"^(l2r_conv_|l2r_vconv_|l2r_fconv_|l2r_lazyconv_|l2r_unbox_)")
LIT = re.compile(r'b"((?:[^"\\]|\\.)*)"')
STR_LIT = re.compile(r"l2r_str_lit\((\d+)\)")
ONCE = re.compile(r"(l2r_once_[a-z]+(?:<[^()]*?>)?\()(\d+)")
VARIANT_REF = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)::([a-z]+\d+)\b")
VARIANT_DEF = re.compile(r"^\s+([a-z]+\d+)\s*(\(.*\))?\s*,?\s*$")
KEPT = re.compile(r"\x00(\d+)\x00")
# The box (the prelude's `LAny`): the program's release of each payload type
# (an item per payload number, its trampoline, the table that installs
# them); the places a payload number appears.
REL_DEF = re.compile(r"^fn l2r_any_rel_(\d+)\(x : (.*)\) -> unit")
REL_TOK = re.compile(r"\bl2r_any_rel_(\d+)(_c)?\b")
REL_ARG = re.compile(r"(leanrt::any::Rel\()(\d+)(,)")
BOX_SITE = re.compile(r"\bl2r_any_(?:of|of_fn|of_u8|of_u16|of_u32|of_bool|of_f32|of_u64|of_f64|imm)\s*[<(]")
PAYLOAD_CALL = re.compile(r"\b(l2r_any_(?:of|of_fn|as|raw_as)<)")
NUM_ARG = re.compile(r"(,\s*)(\d+)(\))")
NUM_LET = re.compile(r"(let bm\d+ : u64 = )(\d+)(;)")
NUM_ARM = re.compile(r"^(\s+)(\d+)( => )", re.M)
ROUNDS = 4


def h(s):
    return hashlib.sha1(s.encode("utf-8", "surrogateescape")).hexdigest()[:12]


def split_items(text):
    lines = text.split("\n")
    try:
        start = lines.index(GEN_MARK)
    except ValueError:
        sys.exit(f"rr-fingerprint: no line '{GEN_MARK}': not lean2rr output")
    items, cur, attrs = [], None, []
    for line in lines[start + 1:]:
        if line.startswith("// ---- "):
            continue
        if line.startswith("#["):
            if cur:
                items.append(cur)
                cur = None
            attrs.append(line)
        elif ITEM_START.match(line):
            if cur:
                items.append(cur)
            cur, attrs = attrs + [line], []
        elif cur is not None:
            cur.append(line)
        elif line.strip():
            cur, attrs = attrs + [line], []
    if cur:
        items.append(cur)
    out = []
    for k, lines in enumerate(items):
        while lines and not lines[-1].strip():
            lines.pop()
        head = next((l for l in lines if not l.startswith("#[")), "")
        m = NAME.match(head)
        if m:
            kind, name = m.group(1), m.group(2)
        elif head.startswith("extern"):
            kind, name = "extern", head.strip()
        else:
            kind, name = "other", f"other#{k}"
        out.append((kind, name, "\n".join(lines)))
    return out


class Program:
    def __init__(self, path):
        with open(path, encoding="utf-8", errors="surrogateescape") as f:
            self.items = split_items(f.read())
        self.lits = []
        for kind, name, text in self.items:
            if kind == "fn" and name == "l2r_str_lit":
                self.lits = LIT.findall(text)
        types = {name for kind, name, _ in self.items if kind in ("enum", "struct")}
        # Numbered names and their stems. A numbered type ends with its own
        # number, not with the name of another type (as
        # `L2RFn_..._T_EST_Out_792` does: that one is named after its types).
        self.stem = {}
        for name in types:
            m = re.search(r"\d+$", name)
            if m and not any(name[i:] in types for i in range(1, len(name))):
                self.stem[name] = name[: m.start()] + "#"
        fresh_types = sorted(self.stem, key=len, reverse=True)
        for kind, name, _ in self.items:
            if kind != "fn":
                continue
            m = FRESH_FN.match(name)
            if m:
                self.stem[name] = m.group(1) + "#" + (m.group(3) or "")
            elif INST.search(name):
                self.stem[name] = INST.sub("___l2r_#_", name)
        self.embedded = (re.compile(r"(?:\d+n)?(" + "|".join(map(re.escape, fresh_types)) + r")(?!\d)")
                         if fresh_types else None)
        defs = {name: (kind, text) for kind, name, text in self.items}
        # The payload numbers of the box and their types.
        self.payload_ty = {}
        for kind, name, text in self.items:
            m = REL_DEF.match(text) if kind == "fn" else None
            if m:
                self.payload_ty[m.group(1)] = m.group(2)
        self.label = dict(self.stem)
        self.variants = {}
        for _ in range(ROUNDS):
            self.variants = self.variant_names()
            self.label = {n: f"{s}~{h(self.canon(*defs[n]))}" for n, s in self.stem.items()}
        self.variants = self.variant_names()
        self.canonical = [(kind, name, self.key(kind, name), self.canon(kind, text))
                          for kind, name, text in self.items]

    def variant_names(self):
        """{(type, numbered constructor): its name by fields and rank}."""
        out = {}
        for kind, name, text in self.items:
            if kind != "enum":
                continue
            seen = collections.Counter()
            for line in text.split("\n")[1:]:
                m = VARIANT_DEF.match(line)
                if m:
                    stem = LOCAL.match(m.group(1)).group(1)
                    fields = self.sub_tokens(m.group(2) or "")
                    k = (stem, fields)
                    out[(name, m.group(1))] = f"{stem}[{fields}]#{seen[k]}"
                    seen[k] += 1
        return out

    def sub_name(self, tok):
        """`tok` with the numbered names in it replaced by their labels."""
        if tok in self.label:
            return self.label[tok]
        if self.embedded is None or not any(c.isdigit() for c in tok):
            return tok
        return self.embedded.sub(lambda m: "«" + self.label[m.group(1)] + "»", tok)

    def sub_tokens(self, text):
        return IDENT.sub(lambda m: self.sub_name(m.group(0)), text)

    def key(self, kind, name):
        if kind in ("extern", "other"):
            return REL_TOK.sub(lambda m: "l2r_any_rel_#" + (m.group(2) or ""), name)
        if REL_TOK.fullmatch(name):
            return "l2r_any_rel_#"
        if name in self.stem:
            return self.stem[name]
        return self.sub_name(name)

    def canon(self, kind, text):
        # Text put in by the first substitutions (a literal's text, a
        # constructor's canonical name) is kept out of the renaming of
        # names below: it stands in the text as `\0K\0` (no name) until
        # the end.
        kept = []
        def keep(t):
            kept.append(t)
            return f"\0{len(kept) - 1}\0"
        def lit(m):
            i = int(m.group(1))
            return keep(f'l2r_str_lit(b"{self.lits[i]}")') if i < len(self.lits) else m.group(0)
        text = STR_LIT.sub(lit, text)
        cells = {}
        text = ONCE.sub(lambda m: m.group(1) + "#" + str(cells.setdefault(m.group(2), len(cells))), text)
        def variant(m):
            new = self.variants.get((m.group(1), m.group(2)))
            return m.group(1) + "::" + (keep(new) if new else m.group(2))
        text = VARIANT_REF.sub(variant, text)
        if self.payload_ty:
            def num(m):
                ty = self.payload_ty.get(m.group(2))
                return m.group(1) + (keep("payload<" + self.sub_tokens(ty) + ">") if ty else m.group(2)) + m.group(3)
            lines = text.split("\n")
            for i, line in enumerate(lines):
                if PAYLOAD_CALL.search(line):
                    line = NUM_ARG.sub(num, line)
                lines[i] = NUM_LET.sub(num, line)
            text = "\n".join(lines)
            if "l2r_any_raw_num" in text:
                text = NUM_ARM.sub(num, text)
            def rel(m):
                ty = self.payload_ty.get(m.group(1))
                return keep("l2r_any_rel<" + self.sub_tokens(ty) + ">" + (m.group(2) or "")) if ty else m.group(0)
            text = REL_TOK.sub(rel, text)
            text = REL_ARG.sub(num, text)
        if kind == "enum":
            lines = text.split("\n")
            ename = NAME.match(next(l for l in lines if not l.startswith("#["))).group(2)
            for i, line in enumerate(lines[1:], 1):
                m = VARIANT_DEF.match(line)
                new = self.variants.get((ename, m.group(1))) if m else None
                if new:
                    lines[i] = line.replace(m.group(1), keep(new), 1)
            text = "\n".join(lines)
        locals_ = {}
        out, pos = [], 0
        for m in IDENT.finditer(text):
            tok = m.group(0)
            out.append(text[pos:m.start()])
            pos = m.end()
            new = self.sub_name(tok)
            if new != tok:
                out.append(new)
                continue
            lm = LOCAL.match(tok)
            if (lm and kind != "enum" and tok not in PRIMS
                    and not text.startswith("::", max(m.start() - 2, 0))):
                out.append(lm.group(1) + "#" + str(locals_.setdefault(tok, len(locals_) + 1)))
            else:
                out.append(tok)
        out.append(text[pos:])
        return KEPT.sub(lambda m: kept[int(m.group(1))], "".join(out))

    def fingerprint(self):
        """(counts, [(key, hash)])."""
        conv_fns = conv_sites = box_sites = box_variants = fns = 0
        conv_names = {name for kind, name, _ in self.items if kind == "fn" and CONV_FN.match(name)}
        raws = {name: text for _, name, text in self.items}
        entries = []
        for kind, name, key, text in self.canonical:
            entries.append((key, h(text)))
            fns += kind == "fn"
            if name in conv_names:
                conv_fns += 1
                continue
            if kind == "fn" and REL_DEF.match(raws[name]):
                box_variants += 1
                continue
            raw = raws[name]
            conv_sites += sum(1 for m in IDENT.finditer(raw) if m.group(0) in conv_names)
            box_sites += len(BOX_SITE.findall(raw))
        counts = {"items": len(self.items), "functions": fns, "conversion-fns": conv_fns,
                  "conversion-sites": conv_sites, "box-sites": box_sites, "box-variants": box_variants}
        return counts, sorted(entries)


def show(path):
    counts, entries = Program(path).fingerprint()
    for k, v in counts.items():
        print(f"{k} {v}")
    for key, hv in entries:
        print(f"item {key} {hv}")


def read_baseline(path):
    counts, entries = {}, []
    with open(path, encoding="utf-8", errors="surrogateescape") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            if line.startswith("item "):
                key, hv = line[5:].rsplit(" ", 1)
                entries.append((key, hv))
            else:
                k, v = line.split(" ", 1)
                counts[k] = v
    return counts, entries


def diff(old, new, ignore=()):
    """(changed keys, dropped "key~hash"s, added "key~hash"s, unchanged count)."""
    group = lambda es: collections.defaultdict(list, {k: sorted(v for kk, v in es if kk == k) for k, _ in es})
    o, n = group(old), group(new)
    changed, dropped, added, same = [], [], [], 0
    for k in sorted(set(o) | set(n)):
        if any(k.startswith(p) for p in ignore):
            continue
        a, b = o.get(k, []), n.get(k, [])
        if len(a) == 1 and len(b) == 1 and a != b:
            changed.append(k)
            continue
        same += sum(1 for x in a if x in b)
        dropped += [f"{k} {x}" for x in a if x not in b]
        added += [f"{k} {x}" for x in b if x not in a]
    return changed, dropped, added, same


def main(argv):
    ignore = [argv[i + 1] for i, a in enumerate(argv) if a == "--ignore" and i + 1 < len(argv)]
    args = [a for i, a in enumerate(argv) if a != "--ignore" and (i == 0 or argv[i - 1] != "--ignore")]
    if len(args) == 2 and args[0] == "show":
        show(args[1])
        return 0
    if len(args) == 3 and args[0] == "text":
        for kind, name, key, text in Program(args[1]).canonical:
            if key == args[2]:
                print(f"// {name}\n{text}\n")
        return 0
    if len(args) == 3 and args[0] in ("compare", "check"):
        old = Program(args[1]).fingerprint()[1] if args[0] == "compare" else read_baseline(args[1])[1]
        new = Program(args[2]).fingerprint()[1]
        changed, dropped, added, same = diff(old, new, ignore)
        for k in changed:
            print(f"changed {k}")
        for k in dropped:
            print(f"dropped {k}")
        for k in added:
            print(f"added {k}")
        print(f"summary: {len(changed)} changed, {len(dropped)} dropped, {len(added)} added, {same} unchanged")
        return 0
    sys.stderr.write(__doc__)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except BrokenPipeError:  # `show ... | head`
        sys.stderr.close()
        sys.exit(0)
