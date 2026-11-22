"""Odd-sector truncations at 60 digits (Section 4, Table tab:hp_rate).

A single unit-weight atom at y/L = 0.28 (capacity m = 4, limit
phi = 2 cos(pi/5)).  The N x N odd-sector matrix (eq. atom_odd) is built and
diagonalised in 60-digit arithmetic (mpmath) for N = 20, 40, ..., 120, and this
prints

    lambda_max(N),   dev(N) = lambda_max(N) - phi,   local rate = log(dev(N-20)/dev(N)) / 20,

checking that dev < 0 (Cauchy interlacing) and that lambda_max(N) increases with N.

Measured, not proved.
"""
import mpmath as mp

from claims import claim

DPS = 60
BANDS = (20, 40, 60, 80, 100, 120)
# Table tab:hp_rate as printed in the paper.
PAPER_DEV = {20: "-7.84e-9", 40: "-1.37e-17", 60: "-2.96e-26",
             80: "-5.20e-35", 100: "-8.71e-44", 120: "-1.03e-52"}
PAPER_RATE = {40: "1.008", 60: "0.998", 80: "1.008", 100: "1.010", 120: "1.028"}


def atom_odd_mp(f, N):
    """Unit-weight odd atom at y/L = f, entries -d_kl + r_kl (see pathlaw_core.odd_block)."""
    s = [mp.sin(2 * mp.pi * k * f) for k in range(N + 1)]
    O = mp.matrix(N, N)
    for k in range(1, N + 1):
        ck = 2 * (1 - f) * mp.cos(2 * mp.pi * k * f)
        for l in range(1, N + 1):
            d = ck if k == l else (s[l] - s[k]) / (mp.pi * (k - l))
            r = -(s[l] + s[k]) / (mp.pi * (k + l))
            O[k - 1, l - 1] = -d + r
    return O


def main():
    mp.mp.dps = DPS
    f = mp.mpf("0.28")
    phi = 2 * mp.cos(mp.pi / 5)
    print(f"phi = 2cos(pi/5) = {mp.nstr(phi, 25)}   (y/L = 0.28, m = 4, {DPS} digits)")
    print(f"{'N':>4}  {'lambda_max(N)':<28} {'dev':>12} {'local rate':>11}")
    prev = mp.mpf(0)
    dev = {}
    monotone = True
    for N in BANDS:
        top = max(mp.eigsy(atom_odd_mp(f, N), eigvals_only=True))
        dev[N] = top - phi
        monotone = monotone and dev[N] < 0 and top > prev
        prev = top
        rate = mp.log(dev[N - 20] / dev[N]) / 20 if N - 20 in dev else None
        print(f"{N:>4}  {mp.nstr(top, 25, strip_zeros=False):<28} {mp.nstr(dev[N], 4):>12}"
              f" {(mp.nstr(rate, 4) if rate is not None else '-'):>11}", flush=True)

    for N in BANDS:
        p = PAPER_DEV[N]
        claim(f"dev({N})", p, float(dev[N]), tol=0.005 * 10 ** float(p.split("e")[1]), fmt=".3e")
    for N, p in PAPER_RATE.items():
        claim(f"local rate({N})", p, float(mp.log(dev[N - 20] / dev[N]) / 20))
    claim("dev < 0 and lambda_max increasing for N = 20..120", "True", bool(monotone))


if __name__ == "__main__":
    main()
