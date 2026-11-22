import Mathlib
import Cvs.Upstream.PreissmannLevequeIdentity

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# MV steps 2–3 — the Preissmann–Lévêque eigen-identity and the eigenvalue bound

* `eigen_identity` (arXiv:2203.14950 Lemma 2.1): pure Finset algebra
  over ℂ + partial fractions + the conjugate eigen-relation; the `−iμ` cross piece dies under
  `Re` — the cancellation at the heart of Montgomery–Vaughan.
* `eigen_bound`: with `c = √δ`, summing the identity over `m` for a unit
  eigenvector and inserting `spacing_sq` (≤ 9) and `Uform_le` (≤ 73):
  `μ² ≤ 9 + 2·73 = 155 ≤ 13²`.
-/

noncomputable section
open Real Finset Complex
open scoped BigOperators ComplexConjugate

namespace Cvs.Zeta.Base
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {freq δ : ι → ℝ}

/-- **Step 2, Preissmann–Lévêque identity.**  Only injectivity of `freq` and
positivity of `c` are needed.  `heig` is the eigen-relation `(H u)_m = iμ u_m` for the
skew-Hermitian `H_{mn} = c_m c_n/(freq m − freq n)`. -/
theorem eigen_identity (hinj : Function.Injective freq) (c : ι → ℝ) (hc : ∀ r, 0 < c r)
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ Finset.univ.erase m,
        ((c m * c n / (freq m - freq n) : ℝ) : ℂ) * u n = (μ : ℂ) * Complex.I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ Finset.univ.erase m, (c m * c n) ^ 2 * ‖u n‖ ^ 2 / (freq m - freq n) ^ 2)
      + 2 * ∑ n ∈ Finset.univ.erase m,
          c m ^ 3 * c n * (u m * conj (u n)).re / (freq m - freq n) ^ 2 :=
  eigen_identity' hinj c hc u μ heig m

end MV
end Cvs.Zeta.Base
