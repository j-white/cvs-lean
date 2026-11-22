import Mathlib
import Cvs.L2a.FarIntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The complex Q-identity iterated once, and the sharp `|Q′|`

For `G = w/Q` the Leibniz relations `QG⁽ⁿ⁾ + nQ′G⁽ⁿ⁻¹⁾ + C(n,2)Q″G⁽ⁿ⁻²⁾ = w⁽ⁿ⁾` (`Q‴ = 0`) give `G‴, G⁗`,
hence `R′, R″` for `R = (pG′)′ + 2icy pG′`, and a second Q-step with weight `R`; `B = −p(ψ(Ge)′ − ψ′Ge)`;
`|Q′|² = (2c²x(y² − 1))² + (2cy)²`, so `|Q′| ≤ 2c²x|y² − 1| + 2cy` on both sides of `y = 1`.
-/

namespace Cvs.L2a.QIdentityIterated

open Real Set Filter Topology MeasureTheory intervalIntegral Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts

/-! ### The boundary term as a bracket -/

/-! ### Higher derivatives of `G = w/Q` -/

/-! ### `R′` and `R″` -/

/-! ### The second Q-step -/

/-! ### The sharp `|Q′|` -/

/-- `|Q′| ≤ 2c²x|y² − 1| + 2cy` for `x, y ≥ 0`, on either side of `y = 1`. -/
theorem norm_qQ₁_le_abs {c y x : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * |y ^ 2 - 1| + 2 * c * y := by
  unfold qQ₁
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * c ^ 2 * x),
    abs_of_nonneg (by positivity : 0 ≤ 2 * c * y)]

/-- **The sharp far-side `|Q′| ≤ 2c²x(y² − 1) + 2cy`** for `y ≥ 1`, `x ≥ 0`. -/
theorem norm_qQ₁_le_far {c y x : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (hc : 0 ≤ c) :
    ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * (y ^ 2 - 1) + 2 * c * y := by
  have := norm_qQ₁_le_abs (c := c) (y := y) hx (by linarith) hc
  rwa [abs_of_nonneg (by nlinarith)] at this

/-- **The near-side `|Q′| ≤ 2c²x(1 − y²) + 2cy`** for `0 ≤ y ≤ 1`, `x ≥ 0`. -/
theorem norm_qQ₁_le_near {c y x : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 1) (hc : 0 ≤ c) :
    ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x * (1 - y ^ 2) + 2 * c * y := by
  have := norm_qQ₁_le_abs (c := c) (y := y) hx hy0 hc
  rwa [abs_of_nonpos (by nlinarith), neg_sub] at this

/-- `|Q″| = 2c²|y² − 1|`, on either side of `y = 1`. -/
theorem norm_qQ₂_eq_abs (c y : ℝ) : ‖qQ₂ c y‖ = 2 * c ^ 2 * |y ^ 2 - 1| := by
  unfold qQ₂
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * c ^ 2)]

/-- The near-side `|Q″| = 2c²(1 − y²)` for `|y| ≤ 1`. -/
theorem norm_qQ₂_eq_near {c y : ℝ} (hy : |y| ≤ 1) : ‖qQ₂ c y‖ = 2 * c ^ 2 * (1 - y ^ 2) := by
  have : y ^ 2 ≤ 1 := by nlinarith [sq_abs y, abs_nonneg y]
  rw [norm_qQ₂_eq_abs, abs_of_nonpos (by linarith), neg_sub]

end Cvs.L2a.QIdentityIterated
