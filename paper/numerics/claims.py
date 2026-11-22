"""Claim reporting shared by the scripts and read back by run_all.py.

Each script calls `claim(...)` for every number the paper quotes.  The call
prints a human-readable line and a tab-separated machine line starting with '@@', which
run_all.py collects into its summary table.

Status rule: MATCH when the reproduced value, rounded to the number of
decimals the paper prints, equals the paper's value (or lies within an
explicit tolerance `tol`); DIFFERS otherwise.  DIFFERS is information, not
failure.
"""

from __future__ import annotations


def _decimals(s: str) -> int:
    s = s.strip().lstrip("+-")
    if "e" in s.lower():
        return -1
    return len(s.split(".")[1]) if "." in s else 0


def claim(label: str, paper, value, tol: float | None = None, fmt: str | None = None) -> bool:
    """Report one quoted number.

    paper : the paper's value as printed (string, e.g. "0.726"), or a number
    value : the reproduced value (number, bool, or string)
    tol   : absolute tolerance; default is half a unit in the paper's last place
    """
    if isinstance(value, bool) or isinstance(value, str):
        ok = (str(value) == str(paper))
        shown = str(value)
    else:
        ps = paper if isinstance(paper, str) else repr(paper)
        p = float(ps)
        d = _decimals(ps)
        if tol is None:
            tol = 0.5 * 10 ** (-d) if d >= 0 else abs(p) * 0.05
            tol *= 1 + 1e-9
        ok = abs(float(value) - p) <= tol
        if fmt is None:
            fmt = f".{max(d, 0) + 2}f" if d >= 0 else ".3e"
        shown = format(int(value), fmt) if fmt == "d" else format(float(value), fmt)
    status = "MATCH" if ok else "DIFFERS"
    print(f"  [{status}] {label}: paper {paper}, reproduced {shown}")
    print(f"@@\t{label}\t{paper}\t{shown}\t{status}", flush=True)
    return ok
