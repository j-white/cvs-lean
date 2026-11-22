import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.CrossIntegralAbsBound
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
# The node of the hierarchy for a pair `(1, k)` on an interval `[L, R]`, `L ≥ 4/3`

The cross coefficient `D⁰ = c²θ²(t − 1)(t + 1 − tθ²)` of the pair `(1, k)`, `t = k² ≥ 4`, is negative for
`θ ≥ 4/3`, so the factors `g₁`, `g₂` are differentiable there with the derivatives of an earlier result, an earlier result, and the node
of the hierarchy (Cvs.L2a.HierarchyModePairNode) holds on any `[L, R]` with `4/3 ≤ L`: the boundary term is at `L` and `R`, and vanishes
when the weight `σ` does.
-/

namespace Cvs.L2a.HierarchyFirstPairNodeInterval

open Real Set intervalIntegral Cvs.L2a.HierarchyModePairFactors Cvs.L2a.HierarchyModePairNode

/-- `tθ² − t − 1 > 0` for `θ ≥ 4/3`, `t ≥ 4`. -/
theorem tθ_pos_first {t θ : ℝ} (ht : 4 ≤ t) (hθ : 4 / 3 ≤ θ) : 0 < 1 * t * θ ^ 2 - t - 1 := by
  have hθ2 : 16 / 9 ≤ θ ^ 2 := by nlinarith
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t) (by linarith : (0:ℝ) ≤ θ ^ 2 - 16 / 9)]

theorem D0_neg_first' {c t θ : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hθ : 4 / 3 ≤ θ) : D0 c 1 t θ < 0 := by
  unfold D0
  have h1 := tθ_pos_first ht hθ
  have h3 : 0 < t - 1 := by linarith
  have : 0 < c ^ 2 * θ ^ 2 * (t - 1) * (1 * t * θ ^ 2 - t - 1) :=
    mul_pos (mul_pos (mul_pos (by positivity) (by nlinarith)) h3) h1
  linarith

/-- The derivative of `g₁` for the pair `(1, k)` on `θ ≥ 4/3`. -/
theorem hasDerivAt_g₁_first' {c t θ : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hθ : 4 / 3 ≤ θ) :
    HasDerivAt (fun θ => (1 * θ ^ 2 - 1) / D0 c 1 t θ)
      (2 * θ * (1 ^ 2 * t * θ ^ 4 - 2 * 1 * t * θ ^ 2 + t + 1) / (c ^ 2 * (t - 1) * θ ^ 4 * (t + 1 - 1 * t * θ ^ 2) ^ 2)) θ := by
  have hD := D0_neg_first' hc ht hθ
  have hnum : HasDerivAt (fun θ => 1 * θ ^ 2 - 1) (1 * (2 * θ)) θ := by
    have := ((hasDerivAt_pow 2 θ).const_mul 1).sub_const 1
    simpa using this
  have hden : HasDerivAt (fun θ => D0 c 1 t θ)
      (c ^ 2 * (2 * θ) * (t - 1) * (t + 1 - 1 * t * θ ^ 2) + c ^ 2 * θ ^ 2 * (t - 1) * (-(1 * t * (2 * θ)))) θ := by
    unfold D0
    have h1 := (hasDerivAt_pow 2 θ).const_mul (c ^ 2)
    have h2 := ((hasDerivAt_pow 2 θ).const_mul (1 * t)).const_sub (t + 1)
    have := (h1.mul_const (t - 1)).fun_mul h2
    refine this.congr_deriv ?_
    simp
  have h := hnum.fun_div hden hD.ne
  refine h.congr_deriv ?_
  unfold D0
  have hθ0 : θ ≠ 0 := by linarith
  have hts : t - 1 ≠ 0 := by linarith
  have hq : t + 1 - 1 * t * θ ^ 2 ≠ 0 := by linarith [tθ_pos_first ht hθ]
  field_simp
  ring

/-- The derivative of `g₂` for the pair `(1, k)` on `θ ≥ 4/3`. -/
theorem hasDerivAt_g₂_first' {c t θ : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hθ : 4 / 3 ≤ θ) :
    HasDerivAt (fun θ => (t * θ ^ 2 - 1) / D0 c 1 t θ)
      (2 * θ * (1 * t ^ 2 * θ ^ 4 - 2 * 1 * t * θ ^ 2 + t + 1) / (c ^ 2 * (t - 1) * θ ^ 4 * (t + 1 - 1 * t * θ ^ 2) ^ 2)) θ := by
  have hD := D0_neg_first' hc ht hθ
  have hnum : HasDerivAt (fun θ => t * θ ^ 2 - 1) (t * (2 * θ)) θ := by
    have := ((hasDerivAt_pow 2 θ).const_mul t).sub_const 1
    simpa using this
  have hden : HasDerivAt (fun θ => D0 c 1 t θ)
      (c ^ 2 * (2 * θ) * (t - 1) * (t + 1 - 1 * t * θ ^ 2) + c ^ 2 * θ ^ 2 * (t - 1) * (-(1 * t * (2 * θ)))) θ := by
    unfold D0
    have h1 := (hasDerivAt_pow 2 θ).const_mul (c ^ 2)
    have h2 := ((hasDerivAt_pow 2 θ).const_mul (1 * t)).const_sub (t + 1)
    have := (h1.mul_const (t - 1)).fun_mul h2
    refine this.congr_deriv ?_
    simp
  have h := hnum.fun_div hden hD.ne
  refine h.congr_deriv ?_
  unfold D0
  have hθ0 : θ ≠ 0 := by linarith
  have hts : t - 1 ≠ 0 := by linarith
  have hq : t + 1 - 1 * t * θ ^ 2 ≠ 0 := by linarith [tθ_pos_first ht hθ]
  field_simp
  ring

/-- **The node in absolute value on `[L, R]`**, `4/3 ≤ L ≤ R`, for a pair `(1, k)`. -/
theorem node_abs_le_first' {c t L R : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hL : 4 / 3 ≤ L) (hLR : L ≤ R)
    {σ σ' f₁ u₁ r₁ f₂ u₂ r₂ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Icc L R, HasDerivAt σ (σ' θ) θ) (hσ'c : ContinuousOn σ' (Icc L R))
    (hf₁ : ∀ θ ∈ Icc L R, HasDerivAt f₁ (u₁ θ / (1 * θ ^ 2 - 1)) θ)
    (hu₁ : ∀ θ ∈ Icc L R, HasDerivAt u₁ (-(c ^ 2 * 1 ^ 2 * θ ^ 2 * f₁ θ) + r₁ θ) θ)
    (hf₂ : ∀ θ ∈ Icc L R, HasDerivAt f₂ (u₂ θ / (t * θ ^ 2 - 1)) θ)
    (hu₂ : ∀ θ ∈ Icc L R, HasDerivAt u₂ (-(c ^ 2 * t ^ 2 * θ ^ 2 * f₂ θ) + r₂ θ) θ)
    (hr₁ : ContinuousOn r₁ (Icc L R)) (hr₂ : ContinuousOn r₂ (Icc L R)) :
    |∫ θ in L..R, σ θ * (f₁ θ * f₂ θ)|
      ≤ |σ R * g₁ c 1 t R * (f₁ R * u₂ R) - σ R * g₂ c 1 t R * (u₁ R * f₂ R)
          - (σ L * g₁ c 1 t L * (f₁ L * u₂ L) - σ L * g₂ c 1 t L * (u₁ L * f₂ L))|
        + |∫ θ in L..R, (σ' θ * g₁ c 1 t θ + σ θ * g₁' c 1 t θ) * (f₁ θ * u₂ θ)|
        + |∫ θ in L..R, (σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) * (u₁ θ * f₂ θ)|
        + |∫ θ in L..R, σ θ / D0 c 1 t θ * ((1 * θ ^ 2 - 1) * f₁ θ * r₂ θ - (t * θ ^ 2 - 1) * r₁ θ * f₂ θ)| := by
  have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  have hθL : ∀ θ ∈ Icc L R, 4 / 3 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hD : ∀ θ ∈ Icc L R, (t * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2) - (1 * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2) ≠ 0 := by
    intro θ hθ
    have := D0_neg_first' hc ht (hθL θ hθ)
    unfold D0 at this
    intro h0; apply this.ne
    linear_combination h0
  have hDeq : ∀ θ, (t * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2) - (1 * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2) = D0 c 1 t θ := by
    intro θ; unfold D0; ring
  have hθ2 : ∀ θ ∈ Icc L R, 16 / 9 ≤ θ ^ 2 := fun θ hθ => by nlinarith [hθL θ hθ]
  have hp₁ : ∀ θ ∈ Icc L R, 1 * θ ^ 2 - 1 ≠ 0 := fun θ hθ => by nlinarith [hθ2 θ hθ]
  have hp₂ : ∀ θ ∈ Icc L R, t * θ ^ 2 - 1 ≠ 0 := fun θ hθ => by nlinarith [hθ2 θ hθ]
  -- the weights `σ g_i` and their derivatives
  have hA : ∀ θ ∈ Icc L R, HasDerivAt (fun θ => σ θ * (1 * θ ^ 2 - 1)
      / ((t * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2) - (1 * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2)))
      (σ' θ * g₁ c 1 t θ + σ θ * g₁' c 1 t θ) θ := fun θ hθ => by
    have h := (hσ θ hθ).fun_mul (hasDerivAt_g₁_first' hc ht (hθL θ hθ))
    refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp only [hDeq, mul_div_assoc]
    · unfold g₁ g₁'; ring
  have hB : ∀ θ ∈ Icc L R, HasDerivAt (fun θ => σ θ * (t * θ ^ 2 - 1)
      / ((t * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2) - (1 * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2)))
      (σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) θ := fun θ hθ => by
    have h := (hσ θ hθ).fun_mul (hasDerivAt_g₂_first' hc ht (hθL θ hθ))
    refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp only [hDeq, mul_div_assoc]
    · unfold g₂ g₂'; ring
  -- continuity of the pieces
  have hg₁c : ContinuousOn (g₁ c 1 t) (Icc L R) := fun θ hθ =>
    (hasDerivAt_g₁_first' hc ht (hθL θ hθ)).continuousAt.continuousWithinAt
  have hg₂c : ContinuousOn (g₂ c 1 t) (Icc L R) := fun θ hθ =>
    (hasDerivAt_g₂_first' hc ht (hθL θ hθ)).continuousAt.continuousWithinAt
  have hden : ∀ θ ∈ Icc L R, c ^ 2 * (t - 1) * θ ^ 4 * (t + 1 - 1 * t * θ ^ 2) ^ 2 ≠ 0 := fun θ hθ => by
    have hts : 0 < t - 1 := by linarith
    have hθ0 : 0 < θ := by linarith [hθL θ hθ]
    have hq : t + 1 - 1 * t * θ ^ 2 ≠ 0 := by linarith [tθ_pos_first ht (hθL θ hθ)]
    exact (mul_pos (mul_pos (mul_pos (by positivity) hts) (by positivity)) (by positivity)).ne'
  have hg₁'c : ContinuousOn (g₁' c 1 t) (Icc L R) := by
    have h1 : Continuous (fun θ : ℝ => 2 * θ * (1 ^ 2 * t * θ ^ 4 - 2 * 1 * t * θ ^ 2 + t + 1)) := by
      fun_prop
    have h2 : Continuous (fun θ : ℝ => c ^ 2 * (t - 1) * θ ^ 4 * (t + 1 - 1 * t * θ ^ 2) ^ 2) := by
      fun_prop
    exact (h1.continuousOn.div h2.continuousOn hden : _)
  have hg₂'c : ContinuousOn (g₂' c 1 t) (Icc L R) := by
    have h1 : Continuous (fun θ : ℝ => 2 * θ * (1 * t ^ 2 * θ ^ 4 - 2 * 1 * t * θ ^ 2 + t + 1)) := by
      fun_prop
    have h2 : Continuous (fun θ : ℝ => c ^ 2 * (t - 1) * θ ^ 4 * (t + 1 - 1 * t * θ ^ 2) ^ 2) := by
      fun_prop
    exact (h1.continuousOn.div h2.continuousOn hden : _)
  have hαc : ContinuousOn (fun θ => σ' θ * g₁ c 1 t θ + σ θ * g₁' c 1 t θ) (Icc L R) :=
    (hσ'c.mul hg₁c).add (hσc.mul hg₁'c)
  have hβc : ContinuousOn (fun θ => σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) (Icc L R) :=
    (hσ'c.mul hg₂c).add (hσc.mul hg₂'c)
  have h := Cvs.L2a.CrossIntegralAbsBound.abs_integral_cross_le (p₁ := fun θ => 1 * θ ^ 2 - 1)
    (q₁ := fun θ => c ^ 2 * 1 ^ 2 * θ ^ 2) (p₂ := fun θ => t * θ ^ 2 - 1) (q₂ := fun θ => c ^ 2 * t ^ 2 * θ ^ 2)
    hLR hp₁ hp₂ hD hf₁ hu₁ hf₂ hu₂ hA hB hαc hβc hσc (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hr₁ hr₂
  simp only [hDeq] at h
  have e1 : ∀ θ, σ θ * (1 * θ ^ 2 - 1) / D0 c 1 t θ = σ θ * g₁ c 1 t θ := fun θ => by unfold g₁; ring
  have e2 : ∀ θ, σ θ * (t * θ ^ 2 - 1) / D0 c 1 t θ = σ θ * g₂ c 1 t θ := fun θ => by unfold g₂; ring
  simp only [e1, e2] at h
  exact h

end Cvs.L2a.HierarchyFirstPairNodeInterval
