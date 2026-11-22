import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyFactorDecay
import Cvs.L2a.HierarchyModePairNode

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The derivatives decay like `θ⁻³`, and the `f u` constant free of `b`

On `θ ≥ θ₀` with `stθ₀² > t + s`: `|g₁'| ≤ a₁'/θ³`, `|g₂'| ≤ a₂'/θ³` (the proofs of Cvs.L2a.HierarchyFactorSuprema before `θ³ ≥ θ₀³`), the
centred products obey `(tθ² − 1)(c²t²θ² − tχ̄) ≤ c²t³θ⁴` for `0 ≤ χ̄`, and so
`(S'|g₁| + |g₁'|)²(tθ² − 1)(c²t²θ² − tχ̄) ≤ c²t³(S'a₁ + a₁'/θ₀)²` uniformly in `θ` (and the same with `g₂`, `s`):
the constant `Ĉ` of the `f u` term of a node, of order `1/c²`, independent of the length of the interval.
-/

namespace Cvs.L2a.HierarchyFactorDerivativeDecay

open Real Set Cvs.L2a.HierarchyModePairNode Cvs.L2a.HierarchyFactorDecay

/-- **`|g₁'| ≤ a₁'/θ³`** on `θ ≥ θ₀`. -/
theorem abs_g₁'_decay {c s t θ₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hθ₀ : 0 < θ₀)
    (hD : t + s < s * t * θ₀ ^ 2) (hθ : θ₀ ≤ θ) : |g₁' c s t θ| ≤ a₁' c s t θ₀ / θ ^ 3 := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have ht0 : 0 < t := by linarith
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hX₀ : 0 < θ₀ ^ 2 := by positivity
  have hCd := Cd_pos hθ₀ hD
  have hts0 : 0 < t - s := by linarith
  have hK : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) hts0
  have hnum : 0 ≤ s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s := by
    have : s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s = t * (s * θ ^ 2 - 1) ^ 2 + s := by ring
    rw [this]; positivity
  have hst := stθ_ge hs0 ht0 hθ₀ hθ
  have hq : t + s - s * t * θ ^ 2 < 0 := by nlinarith [mul_pos (by positivity : (0:ℝ) < θ ^ 2) hCd]
  have hq2 : 0 < (t + s - s * t * θ ^ 2) ^ 2 := sq_pos_of_neg hq
  have hden : 0 < c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2 :=
    mul_pos (mul_pos hK (by positivity)) hq2
  have hden' : 0 < c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 := mul_pos hK (pow_pos hCd 2)
  unfold g₁' a₁'
  rw [abs_div, abs_of_pos hden, abs_of_nonneg (mul_nonneg (by positivity) hnum), div_div]
  rw [div_le_div_iff₀ hden (by positivity)]
  have hN : s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s ≤ θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) := by
    have h4 : (θ₀ ^ 2) ^ 2 ≤ θ ^ 4 := by
      have := pow_le_pow_left₀ hX₀.le hX 2; nlinarith [this]
    have : t + s ≤ θ ^ 4 * ((t + s) / (θ₀ ^ 2) ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ t + s)]
    nlinarith [mul_pos (mul_pos hs0 ht0) (by positivity : (0:ℝ) < θ ^ 2)]
  have hDen2 : (θ ^ 2 * Cd s t θ₀) ^ 2 ≤ (t + s - s * t * θ ^ 2) ^ 2 := by
    rw [show (t + s - s * t * θ ^ 2) ^ 2 = (s * t * θ ^ 2 - t - s) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hst 2
  have hCn0 : 0 ≤ s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2 := by positivity
  have hA : 2 * θ * (s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3)
      ≤ 2 * θ * (θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by positivity)) (by positivity)
  have hB : 2 * θ * (θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3)
      ≤ 2 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2) := by
    have e : 2 * θ * (θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3)
        = 2 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (θ ^ 2 * Cd s t θ₀) ^ 2) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hCn0)
    exact mul_le_mul_of_nonneg_left hDen2 (mul_nonneg hK.le (by positivity))
  linarith

/-- **`|g₂'| ≤ a₂'/θ³`** on `θ ≥ θ₀`. -/
theorem abs_g₂'_decay {c s t θ₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hθ₀ : 0 < θ₀)
    (hD : t + s < s * t * θ₀ ^ 2) (hθ : θ₀ ≤ θ) : |g₂' c s t θ| ≤ a₂' c s t θ₀ / θ ^ 3 := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have ht0 : 0 < t := by linarith
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hX₀ : 0 < θ₀ ^ 2 := by positivity
  have hCd := Cd_pos hθ₀ hD
  have hts0 : 0 < t - s := by linarith
  have hK : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) hts0
  have hnum : 0 ≤ s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s := by
    have : s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s = s * (t * θ ^ 2 - 1) ^ 2 + t := by ring
    rw [this]; positivity
  have hst := stθ_ge hs0 ht0 hθ₀ hθ
  have hq : t + s - s * t * θ ^ 2 < 0 := by nlinarith [mul_pos (by positivity : (0:ℝ) < θ ^ 2) hCd]
  have hq2 : 0 < (t + s - s * t * θ ^ 2) ^ 2 := sq_pos_of_neg hq
  have hden : 0 < c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2 :=
    mul_pos (mul_pos hK (by positivity)) hq2
  have hden' : 0 < c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 := mul_pos hK (pow_pos hCd 2)
  unfold g₂' a₂'
  rw [abs_div, abs_of_pos hden, abs_of_nonneg (mul_nonneg (by positivity) hnum), div_div]
  rw [div_le_div_iff₀ hden (by positivity)]
  have hN : s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s ≤ θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) := by
    have h4 : (θ₀ ^ 2) ^ 2 ≤ θ ^ 4 := by
      have := pow_le_pow_left₀ hX₀.le hX 2; nlinarith [this]
    have : t + s ≤ θ ^ 4 * ((t + s) / (θ₀ ^ 2) ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ t + s)]
    nlinarith [mul_pos (mul_pos hs0 ht0) (by positivity : (0:ℝ) < θ ^ 2)]
  have hDen2 : (θ ^ 2 * Cd s t θ₀) ^ 2 ≤ (t + s - s * t * θ ^ 2) ^ 2 := by
    rw [show (t + s - s * t * θ ^ 2) ^ 2 = (s * t * θ ^ 2 - t - s) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hst 2
  have hCn0 : 0 ≤ s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2 := by positivity
  have hA : 2 * θ * (s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3)
      ≤ 2 * θ * (θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by positivity)) (by positivity)
  have hB : 2 * θ * (θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3)
      ≤ 2 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2) := by
    have e : 2 * θ * (θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2 * θ ^ 3)
        = 2 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (θ ^ 2 * Cd s t θ₀) ^ 2) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hCn0)
    exact mul_le_mul_of_nonneg_left hDen2 (mul_nonneg hK.le (by positivity))
  linarith

/-- The centred product of a dilation `m` (`s = m²` or `t = m²`) is at most `c²m⁶θ⁴` for `0 ≤ χ̄`, `mθ ≥ 1`. -/
theorem centred_prod_le {c m χb θ : ℝ} (hχb : 0 ≤ χb) (hm : 0 ≤ m) (h1 : 1 ≤ m ^ 2 * θ ^ 2)
    (hq : 0 ≤ c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb) :
    (m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb) ≤ c ^ 2 * (m ^ 2) ^ 3 * θ ^ 4 := by
  have h1' : m ^ 2 * θ ^ 2 - 1 ≤ m ^ 2 * θ ^ 2 := by linarith
  have h2' : c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb ≤ c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 := by
    have : 0 ≤ m ^ 2 * χb := by positivity
    linarith
  calc (m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb)
      ≤ m ^ 2 * θ ^ 2 * (c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2) := mul_le_mul h1' h2' hq (by positivity)
    _ = c ^ 2 * (m ^ 2) ^ 3 * θ ^ 4 := by ring

/-- **The `f u` constant, free of the interval**: with `|g| ≤ a/θ²`, `|g'| ≤ a'/θ³` and the product `≤ c²m⁶θ⁴`,
`(S'|g| + |g'|)² · P ≤ c²m⁶(S'a + a'/θ₀)²` for `θ ≥ θ₀ > 0`, `S', a, a' ≥ 0`. -/
theorem fu_const_le {S' a a' θ₀ θ g g' P c m : ℝ} (hS' : 0 ≤ S') (ha : 0 ≤ a) (ha' : 0 ≤ a') (hθ₀ : 0 < θ₀)
    (hθ : θ₀ ≤ θ) (hg : |g| ≤ a / θ ^ 2) (hg' : |g'| ≤ a' / θ ^ 3) (hP0 : 0 ≤ P) (hP : P ≤ c ^ 2 * (m ^ 2) ^ 3 * θ ^ 4) :
    (S' * |g| + |g'|) ^ 2 * P ≤ c ^ 2 * (m ^ 2) ^ 3 * (S' * a + a' / θ₀) ^ 2 := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have h1 : S' * |g| + |g'| ≤ (S' * a + a' / θ) / θ ^ 2 := by
    have e : a' / θ ^ 3 = a' / θ / θ ^ 2 := by field_simp
    have hA : S' * |g| ≤ S' * a / θ ^ 2 := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hg hS'
    have hB : |g'| ≤ a' / θ / θ ^ 2 := by rw [← e]; exact hg'
    rw [add_div]; linarith
  have h2 : (S' * |g| + |g'|) ^ 2 ≤ ((S' * a + a' / θ) / θ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : a' / θ ≤ a' / θ₀ := div_le_div_of_nonneg_left ha' hθ₀ hθ
  have h4 : (S' * a + a' / θ) ^ 2 ≤ (S' * a + a' / θ₀) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc (S' * |g| + |g'|) ^ 2 * P ≤ ((S' * a + a' / θ) / θ ^ 2) ^ 2 * (c ^ 2 * (m ^ 2) ^ 3 * θ ^ 4) :=
        mul_le_mul h2 hP hP0 (by positivity)
    _ = c ^ 2 * (m ^ 2) ^ 3 * (S' * a + a' / θ) ^ 2 := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

end Cvs.L2a.HierarchyFactorDerivativeDecay
