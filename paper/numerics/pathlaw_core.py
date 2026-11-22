"""Core routines for the single-atom path law.

The path law (Theorem thm:pathlaw): the Galerkin matrix of one prime-power atom q
in the window L = log c has operator norm

    ||Delta O_q|| = 2 cos(pi / (m + 1)) * Lambda(q) / sqrt(q),   m = ceil(L / log q).

The functions `capacity`, `chebFactor`, `weight`, `pathLawNorm` and `atomEntry`
follow the Lean definitions of the same names in Cvs/PathLaw/Basic.lean and
Cvs/PathLaw/Statement.lean (up to the floating-point guard in `capacity`).
`odd_block` builds the odd-sector matrix of eq. atom_odd, which staircase.py uses;
`atom_matrix` builds either sector for a prime power, and the self-check below
compares its unfolded sector with `atomEntry`.

Dependencies: numpy only.
"""

from __future__ import annotations

import math
from typing import Union

import numpy as np

Real = Union[int, float]


# ---------------------------------------------------------------------------
# Arithmetic
# ---------------------------------------------------------------------------

def von_mangoldt(n: int) -> float:
    """The von Mangoldt function Lambda(n): log p if n = p^k, else 0."""
    if n < 2:
        return 0.0
    d = 2
    temp = n
    prime_factor = None
    while d * d <= temp:
        if temp % d == 0:
            prime_factor = d
            while temp % d == 0:
                temp //= d
            break
        d += 1
    if prime_factor is None:
        return math.log(n)          # n is prime
    if temp == 1:
        return math.log(prime_factor)   # n = p^k
    return 0.0


def prime_power_weight(q: int) -> float:
    """w_q = Lambda(q) / sqrt(q)."""
    lam = von_mangoldt(q)
    return lam / math.sqrt(q) if lam > 0 else 0.0


# ---------------------------------------------------------------------------
# The definitions that follow the Lean development
# ---------------------------------------------------------------------------

def capacity(L: float, y: float) -> int:
    """capacity L y = ceil(L / y)   (Lean: PathLaw/Basic.lean).

    The 1e-12 guard absorbs floating-point error at exact integer ratios
    (q = 5 at c = 25 has L/y = 2 exactly, and log 25 / log 5 evaluates to
    2 + 4e-16 in double precision); the Lean definition is over the reals.
    """
    return max(int(math.ceil(L / y - 1e-12)), 0)


def chebFactor(m: int) -> float:
    """chebFactor m = 2 cos(pi / (m + 1)), the norm of the path graph P_m."""
    return 2.0 * math.cos(math.pi / (m + 1))


def weight(q: int) -> float:
    """weight q = Lambda(q) / sqrt(q)."""
    return von_mangoldt(q) / math.sqrt(q)


def pathLawNorm(q: int, c: Real) -> float:
    """pathLawNorm q c = chebFactor (capacity (log c) (log q)) * weight q."""
    return chebFactor(capacity(math.log(c), math.log(q))) * weight(q)


def atomEntry(q: int, c: Real, k: int, l: int) -> float:
    """Unfolded atom matrix entry (k, l) in Z x Z   (Lean: PathLaw/Statement.lean).

        alpha = 2 pi (1 - log q / log c)
        k = l :  weight q * (alpha / pi) * cos(alpha k)
        k != l:  weight q * (sin(alpha l) - sin(alpha k)) / (pi (l - k))

    This is w_q Q_y of eq. Q, written with alpha = 2 pi - theta.
    """
    L = math.log(c)
    y = math.log(q)
    alpha = 2 * math.pi * (1 - y / L)
    if k == l:
        return weight(q) * ((alpha / math.pi) * math.cos(alpha * k))
    return weight(q) * ((math.sin(alpha * l) - math.sin(alpha * k)) / (math.pi * (l - k)))


# ---------------------------------------------------------------------------
# Galerkin matrices
# ---------------------------------------------------------------------------

def odd_block(y: float, L: float, N: int) -> np.ndarray:
    """Unit-weight odd-sector (sine-basis, k, l = 1..N) atom block at lag y.

    Entry: -d_{kl} + r_{kl}, with
      d_kk = 2(1 - y/L) cos(2 pi k y/L),
      d_kl = (sin(2 pi l y/L) - sin(2 pi k y/L)) / (pi (k - l)),
      r_kl = -(sin(2 pi l y/L) + sin(2 pi k y/L)) / (pi (k + l)).
    This is Delta O_q / w_q of eq. atom_odd, the odd-sector block of -Q_y.
    Works for any real lag.
    """
    k = np.arange(1, N + 1)
    Kk, Ll = np.meshgrid(k, k, indexing="ij")
    with np.errstate(divide="ignore", invalid="ignore"):
        d = np.where(
            Kk == Ll,
            2.0 * (1.0 - y / L) * np.cos(2.0 * np.pi * Kk * y / L),
            (np.sin(2.0 * np.pi * Ll * y / L) - np.sin(2.0 * np.pi * Kk * y / L))
            / (np.pi * (Kk - Ll)),
        )
    r = -(np.sin(2.0 * np.pi * Ll * y / L) + np.sin(2.0 * np.pi * Kk * y / L)) / (
        np.pi * (Kk + Ll))
    return -d + r


def atom_matrix(q: int, c: Real, N: int, parity: str = "odd") -> np.ndarray:
    """Finite Galerkin matrix of the prime-power atom q at cutoff c.

    parity 'unfolded' : indices -N..N (dim 2N+1), entries atomEntry(q, c, k, l);
           'odd'      : the sine sector (dim N), Delta O_q of eq. atom_odd.
    """
    L = math.log(float(c))
    y = math.log(float(q))
    w = prime_power_weight(q)

    if parity == "unfolded":
        k = np.arange(-N, N + 1)
        K, Lg = np.meshgrid(k, k, indexing="ij")
        alpha = 2.0 * np.pi * (1.0 - y / L)
        with np.errstate(divide="ignore", invalid="ignore"):
            Q = np.where(
                K == Lg,
                (alpha / np.pi) * np.cos(alpha * K),
                (np.sin(alpha * Lg) - np.sin(alpha * K)) / (np.pi * (Lg - K)),
            )
        return w * Q

    if parity == "odd":
        return w * odd_block(y, L, N)

    raise ValueError(f"Unknown parity: {parity}. Must be 'odd' or 'unfolded'.")


if __name__ == "__main__":
    # Self-check: vectorised unfolded matrix == atomEntry; plateau values.
    q, c, N = 3, 25, 6
    A = atom_matrix(q, c, N, "unfolded")
    err = max(abs(A[i + N, j + N] - atomEntry(q, c, i, j))
              for i in range(-N, N + 1) for j in range(-N, N + 1))
    print(f"atom_matrix vs atomEntry: max err {err:.1e}")
    for q in (2, 3, 5, 7):
        print(f"q={q} c=25  capacity={capacity(math.log(25), math.log(q))}"
              f"  pathLawNorm={pathLawNorm(q, 25):.6f}")
