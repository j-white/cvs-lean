import Mathlib
import Cvs.Finite.CosineModeTransform
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformCubicDecay

/-!
# Bounds on the transform of a cosine mode, and linearity over a cosine polynomial

Two regimes for `W_m(ξ) = −iξ(e^{−iξL} − 1)/(ω_m² − ξ²)` in the strip: the crude
`L e^{L|Im ξ|}` from the length of the window, and the far bound
`‖ξ‖(e^{L|Im ξ|} + 1)/|ω_m² − (Re ξ)²|`. The transform of a cosine polynomial is the coefficient
sum of the mode transforms.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex
open Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.CosineModeTransformBounds

/-- The window transform is linear over a finite real combination. -/
theorem windowTransform_sum_cf {ι : Type*} [Fintype ι] (L : ℝ) (c : ι → ℝ) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf fun y => ∑ i, c i * g i y) ξ
      = ∑ i, (c i : ℂ) * Cvs.Detection.windowTransform L (cf (g i)) ξ := by
  unfold Cvs.Detection.windowTransform
  have h : ∀ s : ℝ, Complex.exp (-((s : ℂ) * ξ) * I) * cf (fun y => ∑ i, c i * g i y) s
      = ∑ i, (c i : ℂ) * (Complex.exp (-((s : ℂ) * ξ) * I) * cf (g i) s) := by
    intro s
    simp only [cf]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]
  · refine ContinuousOn.intervalIntegrable (Continuous.continuousOn ?_)
    unfold cf
    exact continuous_const.mul ((by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (-((s : ℂ) * ξ) * I)).mul (Complex.continuous_ofReal.comp (hg i)))

/-- **The crude bound**: length times the strip factor. -/
theorem norm_windowTransform_cos_le {L : ℝ} (hL : 0 ≤ L) (ω : ℝ) (ξ : ℂ) :
    ‖Cvs.Detection.windowTransform L (cf fun y => Real.cos (ω * y)) ξ‖
      ≤ L * Real.exp (L * |ξ.im|) := by
  have := Cvs.Detection.norm_windowTransform_le hL (M := 1) (f := cf fun y => Real.cos (ω * y))
    (fun s _ => by
      rw [cf, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _) ξ
  simpa using this

/-- `‖e^{−iξL} − 1‖ ≤ e^{L|Im ξ|} + 1` for `L ≥ 0`. -/
theorem norm_exp_sub_one_le {L : ℝ} (hL : 0 ≤ L) (ξ : ℂ) :
    ‖Complex.exp (-((L : ℂ) * ξ) * I) - 1‖ ≤ Real.exp (L * |ξ.im|) + 1 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, Cvs.Detection.norm_char]
  have h : L * ξ.im ≤ L * |ξ.im| := mul_le_mul_of_nonneg_left (le_abs_self _) hL
  linarith [Real.exp_le_exp.mpr h]

/-- **The far bound**, away from the resonance:
`‖W_m(ξ)‖ ≤ ‖ξ‖ (e^{L|Im ξ|} + 1) / |ω_m² − (Re ξ)²|` when `ω_m² ≠ (Re ξ)²`. -/
theorem norm_windowTransform_cos_far {L : ℝ} (hL : 0 < L) (m : ℤ) {ξ : ℂ}
    (hne : (2 * π * m / L : ℝ) ^ 2 ≠ ξ.re ^ 2) :
    ‖Cvs.Detection.windowTransform L (cf fun y => Real.cos (2 * π * m / L * y)) ξ‖
      ≤ ‖ξ‖ * (Real.exp (L * |ξ.im|) + 1) / |(2 * π * m / L : ℝ) ^ 2 - ξ.re ^ 2| := by
  set ω : ℝ := 2 * π * m / L with hωdef
  have hlow1 : |ω - ξ.re| ≤ ‖(ω : ℂ) - ξ‖ := by
    have := Complex.abs_re_le_norm ((ω : ℂ) - ξ)
    simpa using this
  have hlow2 : |ω + ξ.re| ≤ ‖(ω : ℂ) + ξ‖ := by
    have := Complex.abs_re_le_norm ((ω : ℂ) + ξ)
    simpa using this
  have hprod : |ω ^ 2 - ξ.re ^ 2| = |ω - ξ.re| * |ω + ξ.re| := by
    rw [← abs_mul]; congr 1; ring
  have hpos : 0 < |ω ^ 2 - ξ.re ^ 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hden : ((ω : ℂ)) ^ 2 - ξ ^ 2 ≠ 0 := by
    intro h
    have hfac : ((ω : ℂ) - ξ) * ((ω : ℂ) + ξ) = 0 := by rw [← h]; ring
    have hn : ‖(ω : ℂ) - ξ‖ * ‖(ω : ℂ) + ξ‖ = 0 := by rw [← norm_mul, hfac, norm_zero]
    have : |ω - ξ.re| * |ω + ξ.re| = 0 := by
      apply le_antisymm _ (by positivity)
      calc |ω - ξ.re| * |ω + ξ.re| ≤ ‖(ω : ℂ) - ξ‖ * ‖(ω : ℂ) + ξ‖ :=
            mul_le_mul hlow1 hlow2 (abs_nonneg _) (norm_nonneg _)
        _ = 0 := hn
    rw [← hprod] at this
    exact hpos.ne' this
  rw [Cvs.Finite.CosineModeTransform.windowTransform_cos_eq_of_int hL m hden]
  have hfac : ((ω : ℂ)) ^ 2 - ξ ^ 2 = ((ω : ℂ) - ξ) * ((ω : ℂ) + ξ) := by ring
  rw [norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, hfac, norm_mul]
  have hnum : ‖ξ‖ * ‖Complex.exp (-((L : ℂ) * ξ) * I) - 1‖
      ≤ ‖ξ‖ * (Real.exp (L * |ξ.im|) + 1) :=
    mul_le_mul_of_nonneg_left (norm_exp_sub_one_le hL.le ξ) (norm_nonneg _)
  have hdenle : |ω ^ 2 - ξ.re ^ 2| ≤ ‖(ω : ℂ) - ξ‖ * ‖(ω : ℂ) + ξ‖ := by
    rw [hprod]
    exact mul_le_mul hlow1 hlow2 (abs_nonneg _) (norm_nonneg _)
  have hdpos : 0 < ‖(ω : ℂ) - ξ‖ * ‖(ω : ℂ) + ξ‖ := lt_of_lt_of_le hpos hdenle
  calc ‖ξ‖ * ‖Complex.exp (-((L : ℂ) * ξ) * I) - 1‖ / (‖(ω : ℂ) - ξ‖ * ‖(ω : ℂ) + ξ‖)
      ≤ ‖ξ‖ * (Real.exp (L * |ξ.im|) + 1) / (‖(ω : ℂ) - ξ‖ * ‖(ω : ℂ) + ξ‖) :=
        div_le_div_of_nonneg_right hnum hdpos.le
    _ ≤ ‖ξ‖ * (Real.exp (L * |ξ.im|) + 1) / |ω ^ 2 - ξ.re ^ 2| :=
        div_le_div_of_nonneg_left (by positivity) hpos hdenle

end Cvs.Finite.CosineModeTransformBounds
