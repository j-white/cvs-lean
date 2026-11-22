"""Theorem thm:two_atom and Example ex:two_three, checked on a discretised window.

The operator w_a (T_a + T_a*) + w_b (T_b + T_b*) on L^2(0, L] is discretised on a
grid of step h, where the partial shifts become banded 0/1 matrices.  Its norm is
compared with mu = (w_b + sqrt(w_b^2 + 4 w_a^2)) / 2 for the primes 2, 3 at c = 4,
for random (a, b, L, w) satisfying L <= min(2a, 2b - a), and for one case that
violates it (where the formula must NOT hold).  Measured, not proved.
"""
import math
import random

import numpy as np

from claims import claim

H = 1e-3


def op_norm(a, b, L, wa, wb, h=H):
    n = int(round(L / h))
    M = np.zeros((n, n))
    for lag, w in ((a, wa), (b, wb)):
        k = int(round(lag / h))
        if k < n:
            M += w * (np.eye(n, k=k) + np.eye(n, k=-k))
    return float(np.abs(np.linalg.eigvalsh(M)).max())


def mu(wa, wb):
    return (wb + math.sqrt(wb * wb + 4 * wa * wa)) / 2


def main():
    wa, wb = math.log(2) / math.sqrt(2), math.log(3) / math.sqrt(3)
    got, want = op_norm(math.log(2), math.log(3), math.log(4), wa, wb), mu(wa, wb)
    print(f"primes 2, 3 at c = 4: discretised norm {got:.6f}  mu {want:.6f}  w_a + w_b {wa + wb:.4f}")
    claim("w_a = log 2/sqrt 2", "0.4901", wa)
    claim("w_b = log 3/sqrt 3", "0.6343", wb)
    claim("mu for the primes 2, 3", "0.9009", want)
    claim("w_a + w_b", "1.1244", wa + wb)
    claim("discretised norm at c = 4 equals mu (to 1e-9)", "True", bool(abs(got - want) < 1e-9))

    rng = random.Random(1)
    ok = True
    for _ in range(5):
        a = rng.uniform(1, 2)
        b = rng.uniform(1.01 * a, 0.99 * 2 * a)
        L = rng.uniform(1.001 * b, min(2 * a, 2 * b - a))
        wa, wb = rng.uniform(0.1, 1), rng.uniform(0.1, 1)
        got, want = op_norm(a, b, L, wa, wb), mu(wa, wb)
        print(f"a={a:.3f} b={b:.3f} L={L:.3f}: discretised norm {got:.6f}  mu {want:.6f}")
        ok = ok and abs(got - want) < 1e-9
    claim("5 random geometries with L <= min(2a, 2b-a): norm equals mu", "True", bool(ok))

    got, want = op_norm(1.0, 1.3, 2.4, 0.5, 0.6), mu(0.5, 0.6)
    print(f"control L > 2a: discretised norm {got:.5f}  mu {want:.5f}  (must differ)")
    claim("control with L > 2a: norm differs from mu by more than 0.1", "True",
          bool(abs(got - want) > 0.1))


if __name__ == "__main__":
    main()
