import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyFactorSuprema
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
# The factors decay in `θ`, and the `f u` product constant is free of `b`

On `θ ≥ θ₀` with `stθ₀² > t + s`: `|g₁| ≤ a₁/θ²`, `|g₂| ≤ a₂/θ²`, `|g₁'| ≤ a₁'/θ³`, `|g₂'| ≤ a₂'/θ³` with explicit
`a_i, a_i'` of order `1/c²`, while the centred product `(tθ² − 1)(c²t²θ² − tχ̄) ≤ c²t³θ⁴` for `χ̄ ≥ 0`; hence
`(S'|g₁| + |g₁'|)²·(tθ² − 1)(c²t²θ² − tχ̄) ≤ c²t³(S'a₁ + a₁'/θ₀)²` uniformly in `θ`: the constant of the `f u`
term of a node without the sup of the product over a long interval .
-/

namespace Cvs.L2a.HierarchyFactorDecay

open Real Set Cvs.L2a.HierarchyModePairFactors Cvs.L2a.HierarchyModePairNode Cvs.L2a.HierarchyFactorSuprema

/-- The decay constants of the factors at `θ₀`. -/
noncomputable def Cd (s t θ₀ : ℝ) : ℝ := s * t - (t + s) / θ₀ ^ 2
noncomputable def a₁ (c s t θ₀ : ℝ) : ℝ := s / (c ^ 2 * (t - s) * Cd s t θ₀)
noncomputable def a₂ (c s t θ₀ : ℝ) : ℝ := t / (c ^ 2 * (t - s) * Cd s t θ₀)
noncomputable def a₁' (c s t θ₀ : ℝ) : ℝ := 2 * (s ^ 2 * t + (t + s) / (θ₀ ^ 2) ^ 2) / (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2)
noncomputable def a₂' (c s t θ₀ : ℝ) : ℝ := 2 * (s * t ^ 2 + (t + s) / (θ₀ ^ 2) ^ 2) / (c ^ 2 * (t - s) * Cd s t θ₀ ^ 2)

theorem Cd_pos {s t θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hD : t + s < s * t * θ₀ ^ 2) : 0 < Cd s t θ₀ := by
  unfold Cd; rw [sub_pos, div_lt_iff₀ (by positivity)]; linarith

/-- `stθ² − t − s ≥ θ² Cd` on `θ ≥ θ₀`. -/
theorem stθ_ge {s t θ₀ θ : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hθ₀ : 0 < θ₀) (hθ : θ₀ ≤ θ) :
    θ ^ 2 * Cd s t θ₀ ≤ s * t * θ ^ 2 - t - s := by
  unfold Cd
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hX₀ : 0 < θ₀ ^ 2 := by positivity
  have : (t + s) / θ₀ ^ 2 * θ ^ 2 ≥ t + s := by
    rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hX₀]
    nlinarith [mul_le_mul_of_nonneg_left hX (by linarith : (0:ℝ) ≤ t + s)]
  nlinarith

/-- **`|g₁| ≤ a₁/θ²`** on `θ ≥ θ₀`. -/
theorem abs_g₁_decay {c s t θ₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hθ₀ : 0 < θ₀)
    (hD : t + s < s * t * θ₀ ^ 2) (hθ : θ₀ ≤ θ) : |g₁ c s t θ| ≤ a₁ c s t θ₀ / θ ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have hCd := Cd_pos hθ₀ hD
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hDn := D0_neg_of hc hs0 hts (by positivity : 0 < θ₀ ^ 2) hD hX
  have hnum : 0 < s * θ ^ 2 - 1 := by
    have : 1 < s * θ₀ ^ 2 := by
      by_contra hcon
      have hcon' : s * θ₀ ^ 2 ≤ 1 := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' ht0.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hX hs0.le]
  have hden : 0 < c ^ 2 * θ ^ 2 * (t - s) * (s * t * θ ^ 2 - t - s) := by
    have := stθ_ge hs0 ht0 hθ₀ hθ
    have : 0 < s * t * θ ^ 2 - t - s := by nlinarith [mul_pos (by positivity : (0:ℝ) < θ ^ 2) hCd]
    positivity
  unfold g₁ a₁
  rw [abs_div, abs_of_neg hDn, abs_of_pos hnum]
  unfold D0
  rw [show -(c ^ 2 * θ ^ 2 * (t - s) * (t + s - s * t * θ ^ 2)) = c ^ 2 * θ ^ 2 * (t - s) * (s * t * θ ^ 2 - t - s) by ring]
  rw [div_div, div_le_div_iff₀ hden (by positivity)]
  have hst := stθ_ge hs0 ht0 hθ₀ hθ
  have hc2 : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) (by linarith)
  have key : (s * θ ^ 2 - 1) * (θ ^ 2 * Cd s t θ₀) ≤ s * (θ ^ 2 * (s * t * θ ^ 2 - t - s)) := by
    have h1 : s * θ ^ 2 - 1 ≤ s * θ ^ 2 := by linarith
    have h2 : 0 ≤ θ ^ 2 * Cd s t θ₀ := by positivity
    calc (s * θ ^ 2 - 1) * (θ ^ 2 * Cd s t θ₀) ≤ s * θ ^ 2 * (θ ^ 2 * Cd s t θ₀) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ s * θ ^ 2 * (s * t * θ ^ 2 - t - s) := mul_le_mul_of_nonneg_left hst (by positivity)
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_left key hc2.le
  nlinarith [this]

/-- **`|g₂| ≤ a₂/θ²`** on `θ ≥ θ₀`. -/
theorem abs_g₂_decay {c s t θ₀ θ : ℝ} (hc : 0 < c) (hs0 : 0 < s) (hts : s < t) (hθ₀ : 0 < θ₀)
    (hD : t + s < s * t * θ₀ ^ 2) (hθ : θ₀ ≤ θ) : |g₂ c s t θ| ≤ a₂ c s t θ₀ / θ ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le hθ₀ hθ
  have hCd := Cd_pos hθ₀ hD
  have hX : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀.le hθ 2
  have hDn := D0_neg_of hc hs0 hts (by positivity : 0 < θ₀ ^ 2) hD hX
  have hnum : 0 < t * θ ^ 2 - 1 := by
    have : 1 < t * θ₀ ^ 2 := by
      by_contra hcon
      have hcon' : t * θ₀ ^ 2 ≤ 1 := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' hs0.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hX ht0.le]
  have hden : 0 < c ^ 2 * θ ^ 2 * (t - s) * (s * t * θ ^ 2 - t - s) := by
    have := stθ_ge hs0 ht0 hθ₀ hθ
    have : 0 < s * t * θ ^ 2 - t - s := by nlinarith [mul_pos (by positivity : (0:ℝ) < θ ^ 2) hCd]
    positivity
  unfold g₂ a₂
  rw [abs_div, abs_of_neg hDn, abs_of_pos hnum]
  unfold D0
  rw [show -(c ^ 2 * θ ^ 2 * (t - s) * (t + s - s * t * θ ^ 2)) = c ^ 2 * θ ^ 2 * (t - s) * (s * t * θ ^ 2 - t - s) by ring]
  rw [div_div, div_le_div_iff₀ hden (by positivity)]
  have hst := stθ_ge hs0 ht0 hθ₀ hθ
  have hc2 : 0 < c ^ 2 * (t - s) := mul_pos (by positivity) (by linarith)
  have key : (t * θ ^ 2 - 1) * (θ ^ 2 * Cd s t θ₀) ≤ t * (θ ^ 2 * (s * t * θ ^ 2 - t - s)) := by
    have h1 : t * θ ^ 2 - 1 ≤ t * θ ^ 2 := by linarith
    have h2 : 0 ≤ θ ^ 2 * Cd s t θ₀ := by positivity
    calc (t * θ ^ 2 - 1) * (θ ^ 2 * Cd s t θ₀) ≤ t * θ ^ 2 * (θ ^ 2 * Cd s t θ₀) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ ≤ t * θ ^ 2 * (s * t * θ ^ 2 - t - s) := mul_le_mul_of_nonneg_left hst (by positivity)
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_left key hc2.le
  nlinarith [this]

end Cvs.L2a.HierarchyFactorDecay
