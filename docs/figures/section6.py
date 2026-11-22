#!/usr/bin/env python3
"""Generate docs/figures/section6.svg, the README's picture of Connes' §6 as formalised.

    python3 docs/figures/section6.py           # write docs/figures/section6.svg
    python3 docs/figures/section6.py --check   # exit 1 if the committed SVG is stale
    python3 docs/figures/section6.py --list    # print each box with its resolved Lean locations

The diagram is data: BOXES, ARROWS and STATUSES below. Every Lean name in a box is resolved in
the source tree before anything is drawn. The script finds the declaration (an `alias`, `theorem`,
`def`, `structure`, ...), records its file and line, and follows a one-line `alias` or `abbrev` to
the declaration that carries the proof. A name that does not exist stops the run with an error,
and so does a name in a proved box that Audit.lean does not `#print axioms`. So the figure cannot
name a theorem the code does not have.

In the SVG each name links to its declaration on GitHub, and each box links to its first name.
GitHub shows README images through <img>, where links are inert, so the figure reads in full
without them; open the SVG file itself to follow the links.

Standard library only. The output is deterministic.
"""

import argparse
import re
import sys
from pathlib import Path
from xml.dom import minidom
from xml.sax.saxutils import escape, quoteattr

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "docs" / "figures" / "section6.svg"
AUDIT = ROOT / "Audit.lean"
GITHUB = "https://github.com/j-white/cvs-lean/blob/main/"
# Files searched first for a name. A name not found there is looked up in the module its
# namespace points at (Cvs.A.B.c in Cvs/A/B.lean), and then in every file under Cvs/.
HEADLINE_FILES = ["Cvs/Main.lean", "Cvs/Bridge.lean"]

TITLE = "Connes §6 in Lean: proved, open, and what RH gives"
FOOTNOTE = ("Names in monospace are Lean declarations, most of them in Cvs/Main.lean and "
            "Cvs/Bridge.lean.")

# ----------------------------------------------------------------------------------------------
# The diagram, as data
# ----------------------------------------------------------------------------------------------

# status -> (legend text, whether its Lean names must appear in Audit.lean)
STATUSES = {
    "proved": ("proved here", True),
    "key": ("the main theorem", True),
    "open": ("open, even given RH", False),
    "rh": ("RH itself", False),
    "bridge": ("follows from RH (Cvs/Bridge)", True),
}

# Text may use _{...} for a subscript. `lean` lists the declarations the box rests on, by full
# name. `row` and `col` place the box on the grid. `external` is for a name that lives outside
# this repository: (label, tooltip, url).
BOXES = [
    dict(id="fact63", row=0, col=0, status="proved",
         title="Fact 6.3 · prolates",
         text="eigen-relations, λ_{k} < 1, 1 − λ_{k} tiny",
         lean=["Cvs.prolate_eigen", "Cvs.prolate_lam_lt_one", "Cvs.prolate_one_sub_lam_le"]),
    dict(id="weil", row=0, col=1, status="proved",
         title="§6.4 · Weil form QW_{λ}",
         text="bottom attained; RH ⟺ QW_{λ} ≥ 0",
         lean=["Cvs.bottom_attained", "Cvs.rh_iff_weil_positivity"]),
    dict(id="fact62", row=0, col=2, status="proved",
         title="Fact 6.2 · Ξ and Φ",
         text="Ξ = Fourier–Laplace of Φ; Poisson for E",
         lean=["Cvs.xi_eq_fourierLaplace", "Cvs.poisson_E"]),
    dict(id="stepA", row=1, col=0, status="open",
         title="Step A at every scale · open",
         text="bottom of QW_{λ} simple, vector even",
         lean=["Cvs.ConnesStepA"]),
    dict(id="thm61", row=1, col=1, status="key",
         title="Theorem 6.1 · CvS",
         text="simple even bottom ⇒ all zeros of θ̂ real",
         lean=["Cvs.theorem_6_1"]),
    dict(id="fact64", row=1, col=2, status="proved",
         title="Fact 6.4 · approximant",
         text="k̂_{λ} → Ξ on closed substrips",
         lean=["Cvs.fact_6_4"]),
    dict(id="stepB", row=2, col=0, status="open",
         title="Step B · open",
         text="θ̂_{λ} tracks k̂_{λ} as λ → ∞",
         lean=["Cvs.Composition.ConnesSectionSix.ConnesStepB"]),
    dict(id="hurwitz", row=2, col=1, status="proved",
         title="§6.6 · Hurwitz passage",
         text="real-rooted limits stay real-rooted",
         lean=["Cvs.rh_of_connes", "Cvs.hurwitz"]),
    dict(id="bridgeA", row=3, col=0, status="bridge",
         title="Step A + Thm 6.1 per bandwidth",
         text="finite resolution, all large scales",
         lean=["Cvs.Bridge.connesStepAN_along", "Cvs.Bridge.realZeros_along"]),
    dict(id="rh", row=3, col=1, status="rh",
         title="Riemann Hypothesis",
         text="proved in Lean by Alpöge (2026)",
         lean=[],
         external=("Mathlib: RiemannHypothesis",
                   "RiemannHypothesis, in Mathlib/NumberTheory/LSeries/RiemannZeta.lean",
                   "https://github.com/leanprover-community/mathlib4/blob/master/"
                   "Mathlib/NumberTheory/LSeries/RiemannZeta.lean")),
    dict(id="bridgeW", row=3, col=2, status="bridge",
         title="§6.4 settled: QW_{λ} ≥ 0",
         text="every truncation matrix is PSD",
         lean=["Cvs.Bridge.weil_nonneg", "Cvs.Bridge.truncation_posSemidef"]),
]

# (from, to, kind). "implies" is a solid grey arrow, "gives" the dashed blue arrow out of RH.
ARROWS = [
    ("fact63", "stepA", "implies"),
    ("weil", "thm61", "implies"),
    ("fact62", "fact64", "implies"),
    ("stepA", "thm61", "implies"),
    ("thm61", "hurwitz", "implies"),
    ("fact64", "hurwitz", "implies"),
    ("stepB", "hurwitz", "implies"),
    ("hurwitz", "rh", "implies"),
    ("rh", "bridgeA", "gives"),
    ("rh", "bridgeW", "gives"),
]

# ----------------------------------------------------------------------------------------------
# Resolving Lean names
# ----------------------------------------------------------------------------------------------

DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "alias", "structure", "class", "inductive",
              "instance", "opaque", "axiom")
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
    r"(" + "|".join(DECL_KINDS) + r")\s+([^\s:({\[]+)")
SCOPE_RE = re.compile(r"^(?:noncomputable\s+)?(namespace|section)\b\s*(\S*)")
END_RE = re.compile(r"^end\b")
# A declaration whose whole body is another name: `alias a := X`, `abbrev a := @X`.
FORWARD_RE = re.compile(r":=\s*@?([A-Za-z_][\w.'!?]*)\s*$")


class ResolveError(Exception):
    pass


class Decl:
    def __init__(self, name, kind, path, line, forward):
        self.name, self.kind, self.path, self.line, self.forward = name, kind, path, line, forward

    @property
    def where(self):
        return "%s:%d" % (self.path, self.line)

    @property
    def url(self):
        return "%s%s#L%d" % (GITHUB, self.path, self.line)


_index_cache = {}


def index_file(rel):
    """All declarations of one Lean file, as {full name: Decl}. Tracks namespaces and comments."""
    if rel in _index_cache:
        return _index_cache[rel]
    lines = (ROOT / rel).read_text(encoding="utf-8").split("\n")
    decls, scopes, depth = {}, [], 0
    for i, raw in enumerate(lines):
        line = raw
        if depth == 0 and not raw.startswith("/-"):
            m = SCOPE_RE.match(line)
            if m:
                scopes.append((m.group(1), m.group(2)))
            elif END_RE.match(line):
                if scopes:
                    scopes.pop()
            else:
                m = DECL_RE.match(line)
                if m:
                    ns = [n for kind, n in scopes if kind == "namespace" and n]
                    full = ".".join(ns + [m.group(2)])
                    # The body of a one-line forward may sit on the next line.
                    body = line
                    if line.rstrip().endswith(":=") and i + 1 < len(lines):
                        body = line.rstrip() + " " + lines[i + 1].strip()
                    f = FORWARD_RE.search(body) if m.group(1) in ("alias", "abbrev") else None
                    decls.setdefault(full, Decl(full, m.group(1), rel, i + 1,
                                                f.group(1) if f else None))
        # Block comments nest in Lean; keep a depth across lines.
        depth += line.count("/-") - line.count("-/")
        depth = max(depth, 0)
    _index_cache[rel] = decls
    return decls


def candidate_files(name):
    """Files that may declare `name`, cheapest first."""
    seen = []
    for rel in HEADLINE_FILES:
        seen.append(rel)
    parts = name.split(".")
    for k in range(len(parts) - 1, 0, -1):
        rel = "/".join(parts[:k]) + ".lean"
        if (ROOT / rel).is_file() and rel not in seen:
            seen.append(rel)
    return seen


def find_decl(name):
    for rel in candidate_files(name):
        d = index_file(rel).get(name)
        if d:
            return d
    last = name.split(".")[-1]
    for path in sorted((ROOT / "Cvs").rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        if rel in _index_cache:
            continue
        if last not in path.read_text(encoding="utf-8"):
            continue
        d = index_file(rel).get(name)
        if d:
            return d
    return None


def resolve(name):
    """(declaration, declaration carrying the proof). They are equal unless the first forwards."""
    d = find_decl(name)
    if d is None:
        raise ResolveError(
            "Lean name `%s` is not declared in %s or anywhere under Cvs/"
            % (name, " or ".join(HEADLINE_FILES)))
    target, hops = d, 0
    while target.forward and hops < 8:
        nxt = find_decl(target.forward)
        if nxt is None:
            raise ResolveError("`%s` (%s) forwards to `%s`, which is not declared under Cvs/"
                               % (target.name, target.where, target.forward))
        target, hops = nxt, hops + 1
    return d, target


def audited_names():
    names = set()
    for line in AUDIT.read_text(encoding="utf-8").split("\n"):
        m = re.match(r"^#print axioms\s+(\S+)", line)
        if m:
            names.add(m.group(1))
    return names


def resolve_all():
    """Attach `links` to every box: a list of (label, tooltip, url, decl, proof decl)."""
    errors, audit = [], audited_names()
    ids = [b["id"] for b in BOXES]
    if len(set(ids)) != len(ids):
        errors.append("duplicate box id")
    for b in BOXES:
        if b["status"] not in STATUSES:
            errors.append("box %s: unknown status %r" % (b["id"], b["status"]))
            continue
        must_audit = STATUSES[b["status"]][1]
        if must_audit and not b["lean"]:
            errors.append("box %s is %s but names no Lean declaration" % (b["id"], b["status"]))
        b["links"] = []
        for name in b["lean"]:
            try:
                d, proof = resolve(name)
            except ResolveError as e:
                errors.append("box %s: %s" % (b["id"], e))
                continue
            if must_audit and name not in audit:
                errors.append("box %s: `%s` is not in Audit.lean's `#print axioms` list"
                              % (b["id"], name))
            tip = "%s (%s, %s)" % (name, d.kind, d.where)
            if proof is not d:
                tip += "; proof: %s (%s)" % (proof.name, proof.where)
            b["links"].append((short(name), tip, d.url, d, proof))
        if b.get("external"):
            label, tip, url = b["external"]
            b["links"].append((label, tip, url, None, None))
    for a, c, kind in ARROWS:
        for end in (a, c):
            if end not in ids:
                errors.append("arrow %s -> %s: no box %r" % (a, c, end))
        if kind not in ("implies", "gives"):
            errors.append("arrow %s -> %s: unknown kind %r" % (a, c, kind))
    if errors:
        raise ResolveError("\n".join(errors))


def short(name):
    """Label shown in the figure: Cvs.theorem_6_1 -> theorem_6_1, Cvs.Bridge.x -> Bridge.x,
    deeper names keep only the last component."""
    parts = name.split(".")
    if parts[0] == "Cvs":
        parts = parts[1:]
    return ".".join(parts) if len(parts) <= 2 else parts[-1]


# ----------------------------------------------------------------------------------------------
# Text measurement (approximate) and rich text
# ----------------------------------------------------------------------------------------------

SANS = "-apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif"
MONO_ADVANCE = 0.62  # em per character, slightly generous


def char_em(ch):
    if ch in "̂̀́":  # combining marks take no room
        return 0.0
    if ch == " ":
        return 0.30
    if ch in "ijl.,;:'|!":
        return 0.29
    if ch in "ftrI()[]·-":
        return 0.37
    if ch in "mwMW":
        return 0.88
    if ch in "⟺⇒→←−≥≤<>=+–":
        return 0.80 if ch in "⟺⇒→←" else 0.62
    if ch.isupper() or ch in "ΞΦΩ§":
        return 0.70
    return 0.58


def sans_width(s, size, bold=False):
    return sum(char_em(c) for c in s) * size * (1.05 if bold else 1.0)


def parse_rich(s):
    """'QW_{λ} ≥ 0' -> [('QW', False), ('λ', True), (' ≥ 0', False)]"""
    out, pos = [], 0
    for m in re.finditer(r"_\{([^}]*)\}", s):
        if m.start() > pos:
            out.append((s[pos:m.start()], False))
        out.append((m.group(1), True))
        pos = m.end()
    if pos < len(s):
        out.append((s[pos:], False))
    return out


def rich_width(s, size, bold=False):
    return sum(sans_width(t, size * (0.75 if sub else 1.0), bold) for t, sub in parse_rich(s))


def rich_svg(s, size):
    """Subscripts as dy-shifted tspans (baseline-shift is not supported everywhere)."""
    drop = round(size * 0.22, 1)
    out, lowered = [], False
    for t, sub in parse_rich(s):
        if sub:
            out.append('<tspan dy="%s" font-size="75%%">%s</tspan>' % (num(drop), escape(t)))
            lowered = True
        elif lowered:
            out.append('<tspan dy="%s">%s</tspan>' % (num(-drop), escape(t)))
            lowered = False
        else:
            out.append(escape(t))
    return "".join(out)


def wrap_rich(s, size, width):
    """Greedy word wrap; a subscript never separates from its base because it has no space."""
    lines, cur = [], ""
    for word in s.split(" "):
        trial = (cur + " " + word) if cur else word
        if cur and rich_width(trial, size) > width:
            lines.append(cur)
            cur = word
        else:
            cur = trial
    lines.append(cur)
    return lines


def num(x):
    x = round(float(x), 1)
    return str(int(x)) if x == int(x) else str(x)


# ----------------------------------------------------------------------------------------------
# Layout
# ----------------------------------------------------------------------------------------------

WIDTH = 900
MARGIN = 20
COL_GAP = 25
ROW_GAP = 46
PAD_X = 8
PAD_TOP = 26        # box top to title baseline
PAD_BOTTOM = 14     # last baseline to box bottom
TITLE_SIZE = 15
TEXT_SIZE = 13
MONO_SIZE = 11.5
TEXT_LEAD = 18
MONO_LEAD = 16
TEXT_GAP = 21       # title baseline to first statement baseline
MONO_GAP = 20       # last statement baseline to first name baseline
SEP = " · "
HEAD_Y = 34         # figure title baseline
GRID_TOP = 58
ARROW_CLEAR = 3     # gap between an arrow head and the box it points at


def pack_names(links, width):
    """Greedy rows of name labels that fit the inner width of a box."""
    rows, cur, cur_w = [], [], 0.0
    for link in links:
        w = len(link[0]) * MONO_SIZE * MONO_ADVANCE
        if w > width:
            raise ResolveError("label `%s` is wider than a box; shorten it" % link[0])
        extra = len(SEP) * MONO_SIZE * MONO_ADVANCE if cur else 0.0
        if cur and cur_w + extra + w > width:
            rows.append(cur)
            cur, cur_w = [link], w
        else:
            cur.append(link)
            cur_w += extra + w
    if cur:
        rows.append(cur)
    return rows


def layout():
    ncols = max(b["col"] for b in BOXES) + 1
    nrows = max(b["row"] for b in BOXES) + 1
    col_w = (WIDTH - 2 * MARGIN - (ncols - 1) * COL_GAP) / ncols
    inner = col_w - 2 * PAD_X
    cells = {}
    for b in BOXES:
        key = (b["row"], b["col"])
        if key in cells:
            raise ResolveError("boxes %s and %s share a grid cell" % (cells[key]["id"], b["id"]))
        cells[key] = b
        if rich_width(b["title"], TITLE_SIZE, bold=True) > inner:
            raise ResolveError("box %s: title is wider than the box" % b["id"])
        b["text_lines"] = wrap_rich(b["text"], TEXT_SIZE, inner)
        b["name_rows"] = pack_names(b["links"], inner)
        b["need"] = (PAD_TOP + TEXT_GAP + (len(b["text_lines"]) - 1) * TEXT_LEAD
                     + (MONO_GAP + (len(b["name_rows"]) - 1) * MONO_LEAD if b["name_rows"] else 0)
                     + PAD_BOTTOM)
    # Every box of a row takes the height of the row's tallest, so titles line up.
    row_h = [max([b["need"] for b in BOXES if b["row"] == r] or [0]) for r in range(nrows)]
    row_y = [GRID_TOP + sum(row_h[:r]) + r * ROW_GAP for r in range(nrows)]
    for b in BOXES:
        b["x"] = MARGIN + b["col"] * (col_w + COL_GAP)
        b["y"] = row_y[b["row"]]
        b["w"], b["h"] = col_w, row_h[b["row"]]
        b["cx"], b["cy"] = b["x"] + col_w / 2, b["y"] + b["h"] / 2
    grid_bottom = row_y[-1] + row_h[-1]
    return cells, grid_bottom


def route(a, b, cells):
    """Path between two boxes on the grid: straight when they share a row or a column, otherwise
    down out of the source and sideways into the target. Refuses to cross another box."""
    c = ARROW_CLEAR
    if a["col"] == b["col"]:
        lo, hi = sorted((a["row"], b["row"]))
        between = [(r, a["col"]) for r in range(lo + 1, hi)]
        if a["row"] < b["row"]:
            d = "M%s,%s V%s" % (num(a["cx"]), num(a["y"] + a["h"]), num(b["y"] - c))
        else:
            d = "M%s,%s V%s" % (num(a["cx"]), num(a["y"]), num(b["y"] + b["h"] + c))
    elif a["row"] == b["row"]:
        lo, hi = sorted((a["col"], b["col"]))
        between = [(a["row"], k) for k in range(lo + 1, hi)]
        if a["col"] < b["col"]:
            d = "M%s,%s H%s" % (num(a["x"] + a["w"]), num(a["cy"]), num(b["x"] - c))
        else:
            d = "M%s,%s H%s" % (num(a["x"]), num(a["cy"]), num(b["x"] + b["w"] + c))
    else:
        lo, hi = sorted((a["row"], b["row"]))
        between = [(r, a["col"]) for r in range(lo + 1, hi + 1)]
        lo, hi = sorted((a["col"], b["col"]))
        between += [(b["row"], k) for k in range(lo + 1, hi)]
        start_y = a["y"] + a["h"] if a["row"] < b["row"] else a["y"]
        end_x = b["x"] + b["w"] + c if a["col"] > b["col"] else b["x"] - c
        d = "M%s,%s V%s H%s" % (num(a["cx"]), num(start_y), num(b["cy"]), num(end_x))
    for cell in between:
        if cell in cells:
            raise ResolveError("arrow %s -> %s would cross box %s"
                               % (a["id"], b["id"], cells[cell]["id"]))
    return d


# ----------------------------------------------------------------------------------------------
# SVG
# ----------------------------------------------------------------------------------------------

STYLE = """\
    .bg { fill: #ffffff; }
    .t { fill: #1f2328; }
    .m { fill: #59636e; }
    .mono { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 11.5px; }
    .proved { fill: #eef8f0; stroke: #1a7f37; stroke-width: 1.5; }
    .key { fill: #dcf3e2; stroke: #1a7f37; stroke-width: 3; }
    .open { fill: #fff8e5; stroke: #bf8700; stroke-width: 1.5; stroke-dasharray: 6 4; }
    .rh { fill: #f6f8fa; stroke: #1f2328; stroke-width: 2; }
    .bridge { fill: #ddf4ff; stroke: #0969da; stroke-width: 1.5; }
    .implies { stroke: #59636e; stroke-width: 1.6; fill: none; }
    .gives { stroke: #0969da; stroke-width: 1.6; fill: none; stroke-dasharray: 5 4; }
    .head-implies { fill: #59636e; }
    .head-gives { fill: #0969da; }
    a { cursor: pointer; }
    a.n:hover { text-decoration: underline; }
    @media (prefers-color-scheme: dark) {
      .bg { fill: #0d1117; }
      .t { fill: #e6edf3; }
      .m { fill: #9198a1; }
      .proved { fill: #12261a; stroke: #3fb950; }
      .key { fill: #163320; stroke: #3fb950; }
      .open { fill: #2a2210; stroke: #d29922; }
      .rh { fill: #161b22; stroke: #e6edf3; }
      .bridge { fill: #0f2240; stroke: #4493f8; }
      .implies { stroke: #9198a1; }
      .gives { stroke: #4493f8; }
      .head-implies { fill: #9198a1; }
      .head-gives { fill: #4493f8; }
    }
"""


def box_svg(b):
    out = []
    cx = num(b["cx"])
    y = b["y"] + PAD_TOP
    weight = "700" if b["status"] in ("key", "rh") else "600"
    body = ['<rect class="%s" x="%s" y="%s" width="%s" height="%s" rx="8"/>'
            % (b["status"], num(b["x"]), num(b["y"]), num(b["w"]), num(b["h"])),
            '<text class="t" x="%s" y="%s" text-anchor="middle" font-size="%d" font-weight="%s">'
            '%s</text>' % (cx, num(y), TITLE_SIZE, weight, rich_svg(b["title"], TITLE_SIZE))]
    y += TEXT_GAP
    for k, line in enumerate(b["text_lines"]):
        body.append('<text class="t" x="%s" y="%s" text-anchor="middle" font-size="%d">%s</text>'
                    % (cx, num(y + k * TEXT_LEAD), TEXT_SIZE, rich_svg(line, TEXT_SIZE)))
    y += (len(b["text_lines"]) - 1) * TEXT_LEAD
    out.append('  <g id="%s">' % b["id"])
    if b["links"]:
        label, tip, url = b["links"][0][:3]
        out.append("    <a href=%s>" % quoteattr(url))
        out.append("      <title>%s</title>" % escape(tip))
        out += ["      " + s for s in body]
        out.append("    </a>")
    else:
        out += ["    " + s for s in body]
    y += MONO_GAP
    for k, row in enumerate(b["name_rows"]):
        parts = []
        for label, tip, url, _, _ in row:
            parts.append('<a class="n" href=%s><title>%s</title>%s</a>'
                         % (quoteattr(url), escape(tip), escape(label)))
        out.append('    <text class="m mono" x="%s" y="%s" text-anchor="middle">%s</text>'
                   % (cx, num(y + k * MONO_LEAD), escape(SEP).join(parts)))
    out.append("  </g>")
    return out


def legend_svg(y):
    """One centred row of swatches, in the order of STATUSES."""
    sw, sh, gap, between, size = 22, 14, 8, 26, 13
    used = [s for s in STATUSES if any(b["status"] == s for b in BOXES)]
    widths = [sw + gap + sans_width(STATUSES[s][0], size) for s in used]
    total = sum(widths) + between * (len(used) - 1)
    if total > WIDTH - 2 * MARGIN:
        raise ResolveError("legend is wider than the figure")
    x, out = (WIDTH - total) / 2, []
    for s, w in zip(used, widths):
        out.append('  <rect class="%s" x="%s" y="%s" width="%d" height="%d" rx="3"/>'
                   % (s, num(x), num(y - 12), sw, sh))
        out.append('  <text class="t" x="%s" y="%s" font-size="%d">%s</text>'
                   % (num(x + sw + gap), num(y), size, escape(STATUSES[s][0])))
        x += w + between
    return out


def build():
    resolve_all()
    cells, grid_bottom = layout()
    by_id = {b["id"]: b for b in BOXES}
    legend_y = grid_bottom + 40
    foot_y = legend_y + 28
    height = int(round(foot_y + 18))

    o = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %d %d" width="%d" height="%d" '
         'font-family="%s">' % (WIDTH, height, WIDTH, height, SANS),
         "  <!-- Generated by docs/figures/section6.py from the Lean declaration names. "
         "Do not edit by hand. -->",
         "  <title>%s</title>" % escape(TITLE),
         "  <style>", STYLE.rstrip("\n"), "  </style>",
         "  <defs>"]
    for kind in ("implies", "gives"):
        o.append('    <marker id="head-%s" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" '
                 'markerHeight="8" orient="auto-start-reverse">' % kind)
        o.append('      <path class="head-%s" d="M0,0 L10,5 L0,10 z"/>' % kind)
        o.append("    </marker>")
    o.append("  </defs>")
    o.append('  <rect class="bg" x="0" y="0" width="%d" height="%d"/>' % (WIDTH, height))
    o.append('  <text class="t" x="%s" y="%d" text-anchor="middle" font-size="18" '
             'font-weight="600">%s</text>' % (num(WIDTH / 2), HEAD_Y, escape(TITLE)))
    for a, c, kind in ARROWS:
        o.append('  <path class="%s" d="%s" marker-end="url(#head-%s)"/>'
                 % (kind, route(by_id[a], by_id[c], cells), kind))
    for b in BOXES:
        o += box_svg(b)
    o += legend_svg(legend_y)
    o.append('  <text class="m" x="%s" y="%s" text-anchor="middle" font-size="12">%s</text>'
             % (num(WIDTH / 2), num(foot_y), escape(FOOTNOTE)))
    o.append("</svg>")
    svg = "\n".join(o) + "\n"
    minidom.parseString(svg.encode("utf-8"))  # must be well-formed XML
    return svg


def listing():
    lines = []
    for b in BOXES:
        lines.append("%-8s %-7s %s" % (b["id"], b["status"], b["title"].replace("_{", "").replace("}", "")))
        for label, tip, url, d, proof in b["links"]:
            if d is None:
                lines.append("    %s  (external)  %s" % (label, url))
                continue
            lines.append("    %s  %s %s" % (d.name, d.kind, d.where))
            if proof is not d:
                lines.append("        proof: %s  %s %s" % (proof.name, proof.kind, proof.where))
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="do not write; exit 1 if %s differs from the generated figure"
                    % OUT.relative_to(ROOT))
    ap.add_argument("--list", action="store_true",
                    help="print each box with the Lean declarations it resolves to")
    args = ap.parse_args(argv)
    try:
        svg = build()
    except ResolveError as e:
        sys.stderr.write("section6.py: error:\n%s\n" % e)
        return 1
    if args.list:
        print(listing())
        return 0
    rel = OUT.relative_to(ROOT)
    if args.check:
        current = OUT.read_text(encoding="utf-8") if OUT.is_file() else None
        if current != svg:
            sys.stderr.write("section6.py: %s is out of date; run python3 docs/figures/section6.py\n"
                             % rel)
            return 1
        print("%s is up to date" % rel)
        return 0
    OUT.write_text(svg, encoding="utf-8")
    print("wrote %s" % rel)
    return 0


if __name__ == "__main__":
    sys.exit(main())
