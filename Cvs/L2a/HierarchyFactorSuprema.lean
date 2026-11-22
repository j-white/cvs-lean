import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyModePairFactors
import Cvs.L2a.HierarchyModePairNode

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The factors and their derivatives at their suprema on `θ ≥ θ₀`

With `X₀ = θ₀²`, `s < t`, `stX₀ > t + s`: `(sθ² − 1)/D⁰` and `(tθ² − 1)/D⁰` are decreasing in `θ²` beyond `X₀`
under a sign condition, so `|g₁| ≤ (sX₀ − 1)/(c²X₀(t − s)(stX₀ − t − s))`, `|g₂| ≤ (tX₀ − 1)/(…)`, and the
derivatives obey `|g₁'| ≤ 2(s²t + (t + s)/X₀²)/(c²(t − s)θ₀³(st − (t + s)/X₀)²)`, `|g₂'|` the same with `st²`:
the sup norms `κ_i, κ_i'` of the path weights on `θ ≥ 19/20` (mode pairs) and on `θ ≥ 4/3` (pairs `(1, k)`).
-/

namespace Cvs.L2a.HierarchyFactorSuprema

open Real Set Cvs.L2a.HierarchyModePairFactors Cvs.L2a.HierarchyModePairNode

/-- `D⁰ < 0` on `θ² ≥ X₀` when `stX₀ > t + s`, `s, t > 0`, `t > s`. -/
theorem D0_neg_of {c s t X₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hX₀ : 0 < X₀)
    (hD : t + s < s * t * X₀) (hθ : X₀ ≤ θ ^ 2) : D0 c s t θ < 0 := by
  unfold D0
  have ht0 : 0 < t := by linarith
  have hθ0 : 0 < θ ^ 2 := lt_of_lt_of_le hX₀ hθ
  have h1 : t + s < s * t * θ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hθ (mul_nonneg hs0.le ht0.le)]
  have : 0 < c ^ 2 * θ ^ 2 * (t - s) * (s * t * θ ^ 2 - t - s) :=
    mul_pos (mul_pos (mul_pos (by positivity) hθ0) (by linarith)) (by linarith)
  linarith

/-- **`|g₁|` at its sup on `θ² ≥ X₀`.** -/
theorem abs_g₁_le_of {c s t X₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hX₀ : 0 < X₀)
    (hs1 : 1 < s * X₀) (hD : t + s < s * t * X₀) (hQ : 0 ≤ s * t * X₀ * (s * X₀ - 2) + t + s) (hθ : X₀ ≤ θ ^ 2) :
    |g₁ c s t θ| ≤ (s * X₀ - 1) / (c ^ 2 * X₀ * (t - s) * (s * t * X₀ - t - s)) := by
  have hDn := D0_neg_of hc hs0 hts hX₀ hD hθ
  have ht0 : 0 < t := by linarith
  have hs1' : 0 < s * X₀ - 1 := by linarith
  have hθ0 : 0 < θ ^ 2 := lt_of_lt_of_le hX₀ hθ
  have hnum : 0 < s * θ ^ 2 - 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ hs0.le]
  have hden : 0 < c ^ 2 * X₀ * (t - s) * (s * t * X₀ - t - s) :=
    mul_pos (mul_pos (mul_pos (by positivity) hX₀) (by linarith)) (by linarith)
  unfold g₁
  rw [abs_div, abs_of_neg hDn, abs_of_pos hnum, div_le_div_iff₀ (by linarith) hden]
  unfold D0
  -- `(sθ² − 1) X₀(stX₀ − t − s) ≤ (sX₀ − 1) θ²(stθ² − t − s)`, from `(θ² − X₀)((sX₀ − 1)stθ² − (stX₀ − t − s)) ≥ 0`
  have hf : 0 ≤ (s * X₀ - 1) * (s * t) * θ ^ 2 - (s * t * X₀ - t - s) := by
    have : (s * X₀ - 1) * (s * t) * X₀ ≤ (s * X₀ - 1) * (s * t) * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hθ (mul_nonneg hs1'.le (mul_nonneg hs0.le ht0.le))
    nlinarith
  have key : (s * θ ^ 2 - 1) * (X₀ * (s * t * X₀ - t - s)) ≤ (s * X₀ - 1) * (θ ^ 2 * (s * t * θ ^ 2 - t - s)) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ θ ^ 2 - X₀) hf]
  have hc2 : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left key hc2.le]

/-- **`|g₂|` at its sup on `θ² ≥ X₀`.** -/
theorem abs_g₂_le_of {c s t X₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hX₀ : 0 < X₀)
    (ht1 : 1 < t * X₀) (hD : t + s < s * t * X₀) (hQ : 0 ≤ s * t * X₀ * (t * X₀ - 2) + t + s) (hθ : X₀ ≤ θ ^ 2) :
    |g₂ c s t θ| ≤ (t * X₀ - 1) / (c ^ 2 * X₀ * (t - s) * (s * t * X₀ - t - s)) := by
  have hDn := D0_neg_of hc hs0 hts hX₀ hD hθ
  have hθ0 : 0 < θ ^ 2 := lt_of_lt_of_le hX₀ hθ
  have ht0 : 0 < t := by linarith
  have ht1' : 0 < t * X₀ - 1 := by linarith
  have hnum : 0 < t * θ ^ 2 - 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ ht0.le]
  have hden : 0 < c ^ 2 * X₀ * (t - s) * (s * t * X₀ - t - s) :=
    mul_pos (mul_pos (mul_pos (by positivity) hX₀) (by linarith)) (by linarith)
  unfold g₂
  rw [abs_div, abs_of_neg hDn, abs_of_pos hnum, div_le_div_iff₀ (by linarith) hden]
  unfold D0
  have hf : 0 ≤ (t * X₀ - 1) * (s * t) * θ ^ 2 - (s * t * X₀ - t - s) := by
    have : (t * X₀ - 1) * (s * t) * X₀ ≤ (t * X₀ - 1) * (s * t) * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hθ (mul_nonneg ht1'.le (mul_nonneg hs0.le ht0.le))
    nlinarith
  have key : (t * θ ^ 2 - 1) * (X₀ * (s * t * X₀ - t - s)) ≤ (t * X₀ - 1) * (θ ^ 2 * (s * t * θ ^ 2 - t - s)) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ θ ^ 2 - X₀) hf]
  have hc2 : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left key hc2.le]

/-- **`|g₁'|` on `θ ≥ θ₀`**, `X₀ = θ₀²`, `stX₀ > t + s`:
`|g₁'| ≤ 2(s²t + (t + s)/X₀²)/(c²(t − s)θ₀³(st − (t + s)/X₀)²)`. -/
theorem abs_g₁'_le_of {c s t θ₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hθ₀ : 0 < θ₀)
    (hD : t + s < s * t * θ₀ ^ 2) (hθ : θ₀ ≤ θ) :
    |g₁' c s t θ| ≤ 2 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)
      / (c ^ 2 * (t - s) * θ₀ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have ht0 : 0 < t := by linarith
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hX₀ : 0 < θ₀ ^ 2 := by positivity
  have hCd : 0 < s * t - (t + s) / θ₀ ^ 2 := by
    rw [sub_pos, div_lt_iff₀ hX₀]; linarith
  have hts0 : 0 < t - s := by linarith
  have hK : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) hts0
  have hnum : 0 ≤ s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s := by
    have : s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s = t * (s * θ ^ 2 - 1) ^ 2 + s := by ring
    rw [this]; positivity
  have hq : t + s - s * t * θ ^ 2 < 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hX (mul_nonneg hs0.le ht0.le)]
  have hq2 : 0 < (t + s - s * t * θ ^ 2) ^ 2 := sq_pos_of_neg hq
  have hden : 0 < c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2 :=
    mul_pos (mul_pos hK (by positivity)) hq2
  have hden' : 0 < c ^ 2 * (t - s) * θ₀ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2 :=
    mul_pos (mul_pos hK (by positivity)) (pow_pos hCd 2)
  unfold g₁'
  rw [abs_div, abs_of_pos hden, abs_of_nonneg (mul_nonneg (by positivity) hnum)]
  rw [div_le_div_iff₀ hden hden']
  have hN : s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s ≤ θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) := by
    have h4 : (θ₀ ^ 2) ^ 2 ≤ θ ^ 4 := by
      have := pow_le_pow_left₀ hX₀.le hX 2; nlinarith [this]
    have : t + s ≤ θ ^ 4 * ((t + s) / (θ₀ ^ 2) ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ t + s)]
    nlinarith [mul_pos (mul_pos hs0 ht0) (by positivity : (0:ℝ) < θ ^ 2)]
  have hDen : θ ^ 2 * (s * t - (t + s) / θ₀ ^ 2) ≤ s * t * θ ^ 2 - t - s := by
    have : (t + s) / θ₀ ^ 2 * θ ^ 2 ≥ t + s := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hX₀]
      nlinarith [mul_le_mul_of_nonneg_left hX (by linarith : (0:ℝ) ≤ t + s)]
    nlinarith
  have hDen2 : (θ ^ 2 * (s * t - (t + s) / θ₀ ^ 2)) ^ 2 ≤ (t + s - s * t * θ ^ 2) ^ 2 := by
    rw [show (t + s - s * t * θ ^ 2) ^ 2 = (s * t * θ ^ 2 - t - s) ^ 2 by ring]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) hCd.le) hDen 2
  have hθ3 : θ₀ ^ 3 ≤ θ ^ 3 := pow_le_pow_left₀ hθ₀.le hθ 3
  have hCn0 : 0 ≤ s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2 := by positivity
  have hA : 2 * θ * (s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s) * (c ^ 2 * (t - s) * θ₀ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2)
      ≤ 2 * θ * (θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * θ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hN (by positivity)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ3 hK.le) (pow_nonneg hCd.le 2)
    · exact hden'.le
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hCn0)
  have hB : 2 * θ * (θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * θ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2)
      ≤ 2 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2) := by
    have e : 2 * θ * (θ ^ 4 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * θ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2)
        = 2 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (θ ^ 2 * (s * t - (t + s) / θ₀ ^ 2)) ^ 2) := by
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hCn0)
    exact mul_le_mul_of_nonneg_left hDen2 (mul_nonneg hK.le (by positivity))
  linarith

/-- **`|g₂'|` on `θ ≥ θ₀`**: `|g₂'| ≤ 2(st² + (t + s)/X₀²)/(c²(t − s)θ₀³(st − (t + s)/X₀)²)`. -/
theorem abs_g₂'_le_of {c s t θ₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hθ₀ : 0 < θ₀)
    (hD : t + s < s * t * θ₀ ^ 2) (hθ : θ₀ ≤ θ) :
    |g₂' c s t θ| ≤ 2 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)
      / (c ^ 2 * (t - s) * θ₀ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have ht0 : 0 < t := by linarith
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hX₀ : 0 < θ₀ ^ 2 := by positivity
  have hCd : 0 < s * t - (t + s) / θ₀ ^ 2 := by
    rw [sub_pos, div_lt_iff₀ hX₀]; linarith
  have hts0 : 0 < t - s := by linarith
  have hK : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) hts0
  have hnum : 0 ≤ s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s := by
    have : s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s = s * (t * θ ^ 2 - 1) ^ 2 + t := by ring
    rw [this]; positivity
  have hq : t + s - s * t * θ ^ 2 < 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hX (mul_nonneg hs0.le ht0.le)]
  have hq2 : 0 < (t + s - s * t * θ ^ 2) ^ 2 := sq_pos_of_neg hq
  have hden : 0 < c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2 :=
    mul_pos (mul_pos hK (by positivity)) hq2
  have hden' : 0 < c ^ 2 * (t - s) * θ₀ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2 :=
    mul_pos (mul_pos hK (by positivity)) (pow_pos hCd 2)
  unfold g₂'
  rw [abs_div, abs_of_pos hden, abs_of_nonneg (mul_nonneg (by positivity) hnum)]
  rw [div_le_div_iff₀ hden hden']
  have hN : s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s ≤ θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) := by
    have h4 : (θ₀ ^ 2) ^ 2 ≤ θ ^ 4 := by
      have := pow_le_pow_left₀ hX₀.le hX 2; nlinarith [this]
    have : t + s ≤ θ ^ 4 * ((t + s) / (θ₀ ^ 2) ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ t + s)]
    nlinarith [mul_pos (mul_pos hs0 ht0) (by positivity : (0:ℝ) < θ ^ 2)]
  have hDen : θ ^ 2 * (s * t - (t + s) / θ₀ ^ 2) ≤ s * t * θ ^ 2 - t - s := by
    have : (t + s) / θ₀ ^ 2 * θ ^ 2 ≥ t + s := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hX₀]
      nlinarith [mul_le_mul_of_nonneg_left hX (by linarith : (0:ℝ) ≤ t + s)]
    nlinarith
  have hDen2 : (θ ^ 2 * (s * t - (t + s) / θ₀ ^ 2)) ^ 2 ≤ (t + s - s * t * θ ^ 2) ^ 2 := by
    rw [show (t + s - s * t * θ ^ 2) ^ 2 = (s * t * θ ^ 2 - t - s) ^ 2 by ring]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) hCd.le) hDen 2
  have hθ3 : θ₀ ^ 3 ≤ θ ^ 3 := pow_le_pow_left₀ hθ₀.le hθ 3
  have hCn0 : 0 ≤ s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2 := by positivity
  have hA : 2 * θ * (s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s) * (c ^ 2 * (t - s) * θ₀ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2)
      ≤ 2 * θ * (θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * θ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hN (by positivity)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ3 hK.le) (pow_nonneg hCd.le 2)
    · exact hden'.le
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hCn0)
  have hB : 2 * θ * (θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * θ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2)
      ≤ 2 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2) := by
    have e : 2 * θ * (θ ^ 4 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2)) * (c ^ 2 * (t - s) * θ ^ 3 * (s * t - (t + s) / θ₀ ^ 2) ^ 2)
        = 2 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) * (c ^ 2 * (t - s) * θ ^ 4 * (θ ^ 2 * (s * t - (t + s) / θ₀ ^ 2)) ^ 2) := by
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hCn0)
    exact mul_le_mul_of_nonneg_left hDen2 (mul_nonneg hK.le (by positivity))
  linarith

end Cvs.L2a.HierarchyFactorSuprema
