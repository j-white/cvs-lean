import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The leakage tail's self-similarity, spectral gap, and stationary pairs

The tail modes satisfy `τ_{km}(θ/k) = τ_m(θ)/√k`. With the WKB slope `s(ξ) = ξ/√(ξ²−1)`,
`ξ s(ξ) ≥ 2` (the tail's log-frequencies are at least `2c`), and a pair phase is stationary exactly
when `r s(r b) = s(b)`, `r = km/m′`, forcing `b² = 1 + 1/r²`: on `b > m′`, `km ≥ 2`, only `m′ = 1`.
-/

namespace Cvs.L2a.LeakageTailSelfSimilarity

open Real

/-- The `m`-th mode of the tail of a profile `φ`, at window half-width `λ`. -/
noncomputable def tailMode (φ : ℝ → ℝ) (lam m θ : ℝ) : ℝ := √(lam / θ) * φ (m * θ) / m

/-- **Self-similarity of the tail modes**: `τ_{km}(θ/k) = τ_m(θ)/√k`. -/
theorem tailMode_scale (φ : ℝ → ℝ) {lam k m θ : ℝ} (hlam : 0 ≤ lam) (hk : 0 < k) (hm : 0 < m)
    (hθ : 0 < θ) :
    tailMode φ lam (k * m) (θ / k) = tailMode φ lam m θ / √k := by
  unfold tailMode
  have hkm : k * m * (θ / k) = m * θ := by field_simp
  have hsq : √(lam / (θ / k)) = √(lam / θ) * √k := by
    rw [div_div_eq_mul_div, mul_div_right_comm, sqrt_mul (div_nonneg hlam hθ.le)]
  have hk' : 0 < √k := sqrt_pos.mpr hk
  rw [hkm, hsq]
  field_simp
  rw [sq_sqrt hk.le]
  ring

/-- The WKB slope of the prolate phase outside the window, `s(ξ) = ξ/√(ξ²−1)`. -/
noncomputable def slope (ξ : ℝ) : ℝ := ξ / √(ξ ^ 2 - 1)

/-- **The tail's spectral gap**: for `ξ > 1`, `2 ≤ ξ s(ξ) = ξ²/√(ξ²−1)`, with equality at `ξ = √2`;
the log-phase derivative `c ξ s(ξ)` of the first mode is at least `2c`. -/
theorem two_le_mul_slope {ξ : ℝ} (hξ : 1 < ξ) : 2 ≤ ξ * slope ξ := by
  unfold slope
  have hB : 0 < ξ ^ 2 - 1 := by nlinarith
  set u := √(ξ ^ 2 - 1) with hu
  have hu0 : 0 < u := sqrt_pos.mpr hB
  have hu2 : u ^ 2 = ξ ^ 2 - 1 := sq_sqrt hB.le
  rw [← mul_div_assoc, le_div_iff₀ hu0]
  nlinarith [sq_nonneg (u - 1)]

/-- **Stationary condition**: for `b > 1`, `r b > 1`, `r > 0`, `r ≠ 1`, the equation
`r s(r b) = s(b)` forces `b² = 1 + 1/r²`. -/
theorem sq_eq_of_stationary {r b : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (hb : 1 < b) (hrb : 1 < r * b)
    (h : r * slope (r * b) = slope b) : b ^ 2 = 1 + 1 / r ^ 2 := by
  unfold slope at h
  have hB : 0 < b ^ 2 - 1 := by nlinarith
  have hR : 0 < (r * b) ^ 2 - 1 := by nlinarith
  have hsB := sqrt_pos.mpr hB
  have hsR := sqrt_pos.mpr hR
  -- clear the square roots: r² b √(b²−1) = b √((rb)²−1)
  have h1 : r * (r * b) * √(b ^ 2 - 1) = b * √((r * b) ^ 2 - 1) := by
    rw [← mul_div_assoc, div_eq_div_iff hsR.ne' hsB.ne'] at h
    exact h
  have hb0 : 0 < b := by linarith
  have h2 : r ^ 2 * √(b ^ 2 - 1) = √((r * b) ^ 2 - 1) := by
    have : b * (r ^ 2 * √(b ^ 2 - 1)) = b * √((r * b) ^ 2 - 1) := by rw [← h1]; ring
    exact mul_left_cancel₀ hb0.ne' this
  have h3 : r ^ 4 * (b ^ 2 - 1) = (r * b) ^ 2 - 1 := by
    have : (r ^ 2 * √(b ^ 2 - 1)) ^ 2 = √((r * b) ^ 2 - 1) ^ 2 := by rw [h2]
    rw [mul_pow, sq_sqrt hB.le, sq_sqrt hR.le] at this
    linarith [this]
  -- (r² − 1)(r² b² − (r² + 1)) = 0, and r² ≠ 1
  have hr2 : r ^ 2 - 1 ≠ 0 := by
    intro h0
    have : r ^ 2 = 1 ^ 2 := by linarith
    exact hr1 ((pow_left_inj₀ hr.le zero_le_one two_ne_zero).mp this)
  have h4 : (r ^ 2 - 1) * (r ^ 2 * b ^ 2 - (r ^ 2 + 1)) = 0 := by nlinarith [h3]
  have h5 : r ^ 2 * b ^ 2 = r ^ 2 + 1 := by
    have := (mul_eq_zero.mp h4).resolve_left hr2
    linarith
  have hr0 : r ^ 2 ≠ 0 := by positivity
  field_simp
  linarith

/-- **Only the first mode has a stationary pair**: if `2 ≤ k m`, `1 ≤ m′`, the stationary edge
`b² = 1 + (m′/(km))²` lies inside the support `b > m′` of mode `m′` only when `m′ = 1`. -/
theorem eq_one_of_stationary {k m m' : ℕ} (hkm : 2 ≤ k * m) (hm' : 1 ≤ m') {b : ℝ}
    (hb : b ^ 2 = 1 + ((m' : ℝ) / (k * m)) ^ 2) (hsupp : (m' : ℝ) < b) : m' = 1 := by
  by_contra hne
  have h2 : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
  have hkmR : (2 : ℝ) ≤ (k : ℝ) * m := by exact_mod_cast hkm
  have hpos : (0 : ℝ) < (k : ℝ) * m := by linarith
  -- (m′/(km))² ≤ m′²/4, so b² ≤ 1 + m′²/4 < m′² ≤ b²
  have hq : ((m' : ℝ) / (k * m)) ^ 2 ≤ (m' : ℝ) ^ 2 / 4 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 : ℝ) ≤ ((k : ℝ) * m) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (m' : ℝ)]
  have hb2 : (m' : ℝ) ^ 2 < b ^ 2 := by
    have : (0 : ℝ) ≤ m' := by positivity
    nlinarith
  nlinarith
end Cvs.L2a.LeakageTailSelfSimilarity
