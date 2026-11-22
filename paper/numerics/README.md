# Numerical checks for `pathlaw.tex`

`make numerics` (from `paper/`) builds `.venv` from `requirements.txt` (numpy, mpmath) and runs
`run_all.py`. It needs Python 3.12 or later, which numpy 2.5 requires; if `python3` is older, pass an
interpreter with `make numerics PYTHON=python3.12`. That script runs each script below, saves each output to `out/<script>.txt`, and
prints one table: claim | paper value | reproduced value | MATCH/DIFFERS. It exits non-zero only
on a crash. Runtimes are wall-clock on an Apple-silicon laptop.

| script | backs | runtime |
| --- | --- | --- |
| `pathlaw_core.py` | library: `capacity`, `chebFactor`, `weight`, `pathLawNorm` and `atomEntry`, which follow the Lean definitions of the same names, and the odd-sector block `odd_block` of eq. `atom_odd` | — |
| `claims.py` | library: the claim/status lines read by `run_all.py` | — |
| `staircase.py` | Table `tab:staircase`: truncated atom norms on a grid of y/L and at the prime powers q < 25 for c = 25 (q = 5 has norm w_5 and spectrum {±w_5}); the slow case y/L = 0.49 quoted in Section 4 | <1 s |
| `truncation.py` | Table `tab:hp_rate`: 60-digit λ_max(N), its deviation from φ, and the local rate for N = 20..120 | 8 s |
| `two_atom.py` | Theorem `thm:two_atom` and Example `ex:two_three` (μ = 0.9009 against w_a + w_b = 1.1244), random admissible geometries, and one geometry that violates the hypothesis | 14 s |
| `run_all.py` | runs all of the above | 22 s |
