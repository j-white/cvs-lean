import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The orbit gaps grow with `M` and `m`

Over `2 ≤ m ≤ M − 1` the orbit product `(m² − 1)((M/m)² − 1)` is least at `m = M − 1`, where it is
`gapM M = (2M − 1)(1 − 1/(M − 1)²) = 2M − 1 − 2/(M − 1) − 1/(M − 1)² ≥ 2M − 9/4`. Hence `c⁻² Re Q` is at least
`gapM M − (1 − χ/c²)` on the far side, and at most `−(m² − 1)(1 − b²/m²) ≤ −(m² − 1 − b²)` on the near side.
-/

namespace Cvs.L2a.OrbitGapGrowth

open Real

/-! ### The far-side gap as a function of `M` -/

/-- The minimal orbit product at integer `M`: `gapM M = (2M − 1)(1 − 1/(M − 1)²)`. -/
noncomputable def gapM (M : ℝ) : ℝ := (2 * M - 1) * (1 - 1 / (M - 1) ^ 2)

/-- The defect from `2M − 1` is exact: `2M − 1 − gapM M = (2M − 1)/(M − 1)²`. -/
theorem two_mul_sub_one_sub_gapM (M : ℝ) : 2 * M - 1 - gapM M = (2 * M - 1) / (M - 1) ^ 2 := by
  unfold gapM
  ring

/-- **Linear growth in `M`**: `2M − 9/4 ≤ gapM M` for `M ≥ 3`, equality at `M = 3`. -/
theorem gapM_ge {M : ℝ} (hM : 3 ≤ M) : 2 * M - 9 / 4 ≤ gapM M := by
  have h := two_mul_sub_one_sub_gapM M
  have hM1 : 0 < (M - 1) ^ 2 := by nlinarith
  have hfac : 5 * (M - 1) ^ 2 - 4 * (2 * M - 1) = (5 * M - 3) * (M - 3) := by ring
  have hle : (2 * M - 1) / (M - 1) ^ 2 ≤ 5 / 4 := by
    rw [div_le_iff₀ hM1]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 5 * M - 3) (by linarith : (0 : ℝ) ≤ M - 3)]
  linarith

theorem fifteen_fourths_le_gapM {M : ℝ} (hM : 3 ≤ M) : (15 : ℝ) / 4 ≤ gapM M := by
  linarith [gapM_ge hM]

/-! ### The orbit product and its minimum over `m` -/

/-- The excess over the minimum, exactly:
`f(m) − gapM M = ((M − 1)² − m²)(m²(M − 1)² − M²)/(m²(M − 1)²)`. -/
theorem orbit_prod_sub_gapM {M m : ℝ} (hm : m ≠ 0) (hM : M ≠ 1) :
    (m ^ 2 - 1) * ((M / m) ^ 2 - 1) - gapM M
      = ((M - 1) ^ 2 - m ^ 2) * (m ^ 2 * (M - 1) ^ 2 - M ^ 2) / (m ^ 2 * (M - 1) ^ 2) := by
  have h : M - 1 ≠ 0 := sub_ne_zero.2 hM
  unfold gapM
  field_simp
  ring

/-- **The orbit gap grows with `M`**: `gapM M ≤ (m² − 1)((M/m)² − 1)` for integers `2 ≤ m ≤ M − 1`. -/
theorem orbit_gap_growth (M m : ℕ) (hm : 2 ≤ m) (hmM : m ≤ M - 1) :
    gapM M ≤ ((m : ℝ) ^ 2 - 1) * (((M : ℝ) / m) ^ 2 - 1) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) ≠ 1 := by intro h; linarith
  have hd := orbit_prod_sub_gapM (M := (M : ℝ)) hm0 hM1
  have h1 : 0 ≤ ((M : ℝ) - 1) ^ 2 - (m : ℝ) ^ 2 := by nlinarith
  -- `m(M − 1) − M = (m − 1)(M − 1) − 1 ≥ 0`
  have h2 : (M : ℝ) ≤ m * ((M : ℝ) - 1) := by nlinarith
  have h2' : 0 ≤ (m : ℝ) ^ 2 * ((M : ℝ) - 1) ^ 2 - (M : ℝ) ^ 2 := by
    have : (M : ℝ) ^ 2 ≤ (m * ((M : ℝ) - 1)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  have hq : 0 ≤ (((M : ℝ) - 1) ^ 2 - (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 * ((M : ℝ) - 1) ^ 2 - (M : ℝ) ^ 2)
      / ((m : ℝ) ^ 2 * ((M : ℝ) - 1) ^ 2) := by positivity
  linarith

/-! ### The two sides of `Re Q` -/

/-- **Far side**: for `x ≥ m` and `y ≥ M/m`, `gapM M ≤ (x² − 1)(y² − 1)`. -/
theorem far_gap (M m : ℕ) (hm : 2 ≤ m) (hmM : m ≤ M - 1) {x y : ℝ} (hx : (m : ℝ) ≤ x)
    (hy : (M : ℝ) / m ≤ y) : gapM M ≤ (x ^ 2 - 1) * (y ^ 2 - 1) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  have hMm : 1 ≤ (M : ℝ) / m := by rw [le_div_iff₀ hm0, one_mul]; linarith
  have hx2 : (m : ℝ) ^ 2 - 1 ≤ x ^ 2 - 1 := by nlinarith
  have hy2 : ((M : ℝ) / m) ^ 2 - 1 ≤ y ^ 2 - 1 := by nlinarith
  have hA : 0 ≤ (m : ℝ) ^ 2 - 1 := by nlinarith
  have hB : 0 ≤ ((M : ℝ) / m) ^ 2 - 1 := by nlinarith
  exact (orbit_gap_growth M m hm hmM).trans (mul_le_mul hx2 hy2 hB (hA.trans hx2))

/-- **Near side**: for `x ≥ m ≥ 1` and `0 ≤ y ≤ b/m ≤ 1`, `(m² − 1)(1 − b²/m²) ≤ (x² − 1)(1 − y²)`. -/
theorem near_gap {m b x y : ℝ} (hm : 1 ≤ m) (hbm : b ≤ m) (hx : m ≤ x) (hy0 : 0 ≤ y)
    (hy : y ≤ b / m) : (m ^ 2 - 1) * (1 - b ^ 2 / m ^ 2) ≤ (x ^ 2 - 1) * (1 - y ^ 2) := by
  have hm0 : 0 < m := by linarith
  have hbm1 : b / m ≤ 1 := by rw [div_le_iff₀ hm0, one_mul]; exact hbm
  have hb0 : 0 ≤ b / m := hy0.trans hy
  have hy2 : y ^ 2 ≤ b ^ 2 / m ^ 2 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hy0 hy 2
  have hbm2 : b ^ 2 / m ^ 2 ≤ 1 := by
    rw [← div_pow]; nlinarith
  have hx2 : m ^ 2 - 1 ≤ x ^ 2 - 1 := by nlinarith
  have hA : 0 ≤ m ^ 2 - 1 := by nlinarith
  exact mul_le_mul hx2 (by linarith) (by linarith) (hA.trans hx2)

end Cvs.L2a.OrbitGapGrowth
