"""The plateaus of Table tab:staircase, checked on truncated odd-sector atoms.

For one unit-weight atom at lag y on a window of length L, the largest |eigenvalue|
of the N x N odd-sector matrix (eq. atom_odd, pathlaw_core.odd_block) approaches
2 cos(pi/(m+1)), m = ceil(L/y), from below (Theorem thm:pathlaw, Section 4).

This prints the truncated values on a grid of y/L at N = 120, and for the prime
powers q < 25 at c = 25 at N = 160, and checks:

  * the grid points away from the right end of their plateau are within 1e-11 of
    2 cos(pi/(m+1)) at N = 120;
  * y/L = 0.49, just left of the right end of the m = 3 plateau, is still
    1.7e-4 short at N = 120 (the slow case quoted in Section 4);
  * every prime power q < 25 at c = 25 is within 1e-9 of the plateau value;
  * q = 5 at c = 25 has L/y = 2 exactly: norm w_5 and spectrum {+w_5, -w_5}
    (Table tab:staircase caption).

Measured, not proved.
"""
import math

import numpy as np

from pathlaw_core import capacity, chebFactor, odd_block, prime_power_weight
from claims import claim

GRID = (0.06, 0.09, 0.13, 0.17, 0.21, 0.26, 0.28, 0.34, 0.40, 0.49, 0.51, 0.70, 0.95)
# Just left of the right end 1/(m-1) of their plateau, where the long-chain base
# 1 - (m-1) y/L is at most 0.02: there the truncations converge slowly.
SLOW = (0.09, 0.49)


def top_abs(M):
    return float(np.max(np.abs(np.linalg.eigvalsh(M))))


def main():
    print("odd-sector truncation at N = 120, unit weight")
    print(f"   {'y/L':>6} {'measured':>12} {'m':>3} {'2cos(pi/(m+1))':>15} {'diff':>10}")
    diffs = {}
    for f in GRID:
        m = capacity(1.0, f)
        diffs[f] = top_abs(odd_block(f, 1.0, 120)) - chebFactor(m)
        print(f"   {f:>6.2f} {diffs[f] + chebFactor(m):>12.9f} {m:>3} {chebFactor(m):>15.9f}"
              f" {diffs[f]:>+10.1e}{'   (near the right end of the plateau)' if f in SLOW else ''}")
    fast = max(abs(d) for f, d in diffs.items() if f not in SLOW)
    claim("grid points away from plateau right ends, |diff| < 1e-11 at N=120", "True",
          bool(fast < 1e-11))
    claim("deviation at y/L=0.49, N=120", "1.7e-4", abs(diffs[0.49]), tol=0.05e-4, fmt=".2e")

    print("\nprime powers q < 25 at c = 25, N = 160")
    L = math.log(25)
    worst = 0.0
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23):
        y = math.log(q)
        w = prime_power_weight(q)
        M = w * odd_block(y, L, 160)
        m = capacity(L, y)
        nm = top_abs(M) / w
        worst = max(worst, abs(nm - chebFactor(m)))
        print(f"   q={q:>3}  m={m}  plateau {chebFactor(m):.6f}  measured {nm:.6f}"
              f"  diff {nm - chebFactor(m):+.1e}")
        if q == 5:
            ev = np.linalg.eigvalsh(M) / w
            claim("q=5 at c=25: norm / w_5 (L/y = 2 exactly)", "1.0000", nm)
            claim("q=5 at c=25: spectrum {+w_5, -w_5}", "True",
                  bool(np.max(np.abs(np.abs(ev) - 1.0)) < 1e-12 and ev.min() < 0 < ev.max()))
    print(f"   worst deviation {worst:.1e} (q = 23 sits at y/L = 0.974, next to the window edge)")
    claim("prime powers q < 25 at c = 25 within 1e-9 of the plateau", "True", bool(worst < 1e-9))


if __name__ == "__main__":
    main()
