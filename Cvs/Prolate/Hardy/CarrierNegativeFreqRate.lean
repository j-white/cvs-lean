import Mathlib
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipPhaseDecay
import Cvs.Upstream.HardyHalvesFourier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The negative-frequency part of the positive carrier is `O(c^{−1/2})` in `L²`

`‖k − P₊k‖² = ∫_{ξ<0}|𝓕k|² ≤ ((3/5)Mπ)²/(cδ₀ · 2πB)` with `B = √11/10`, `δ₀ = B − 3/10`: the arc bound integrated
over the negative half-line.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform
open Complex (I)

namespace Cvs.Prolate.Hardy.CarrierNegativeFreqRate
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C posProj)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (kC carH tArc eta0)

/-- A function continuous on `[a, b]`, cut to `(a, b]`, is in `L¹ ∩ L²`. -/
theorem integrable_memLp_indicator {a b : ℝ} {f : ℝ → ℂ} (hf : ContinuousOn f (Icc a b)) :
    Integrable ((Ioc a b).indicator f) ∧ MemLp ((Ioc a b).indicator f) 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨?_, ?_⟩
  swap
  · refine (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 (MemLp.of_bound
      ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) (max C 0) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact le_max_of_le_left (hC x (Ioc_subset_Icc_self hx))
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (hf.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- `∫_{ξ<0} F = ∫_{ξ>0} F(−ξ)`. -/
theorem integral_Iio_eq_Ioi_neg (F : ℝ → ℝ) : ∫ ξ in Iio (0 : ℝ), F ξ = ∫ ξ in Ioi (0 : ℝ), F (-ξ) := by
  rw [← integral_Iic_eq_integral_Iio, integral_comp_neg_Ioi, neg_zero]

theorem continuousOn_carH (c : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    ContinuousOn (carH c A) (Icc (-(3 / 5)) (3 / 5)) := by
  have hAr : ContinuousOn (fun x : ℝ => A x) (Icc (-(3 / 5)) (3 / 5)) := by
    intro x hx
    have : ‖(x : ℂ)‖ ≤ 3 / 5 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact hx
    exact ((hA _ this).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have e2 : Continuous fun x : ℝ => Complex.exp (I * c * x) := by fun_prop
  unfold carH
  exact (hAr.mul e2.continuousOn).mul ((Cvs.Prolate.Hardy.CarrierUpperHalfPlane.continuous_wR (c / 2)).continuousOn.inv₀
    fun x _ => Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_ne_zero _ x)

theorem integrable_kC (c : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    Integrable (kC c A) := (integrable_memLp_indicator (continuousOn_carH c hA)).1

theorem memLp_kC (c : ℝ) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    MemLp (kC c A) 2 (volume : Measure ℝ) := (integrable_memLp_indicator (continuousOn_carH c hA)).2

/-- The arc rate `δ₀ = √11/10 − 3/10 > 0`. -/
theorem delta0_pos : 0 < √11 / 10 - 3 / 10 := by linarith [Cvs.Prolate.Hardy.CarrierNegativeFrequencies.three_lt_sqrt_eleven]

/-- **The arc estimate in `L²`**: `‖k − P₊k‖² ≤ ((3/5)Mπ)²/(cδ₀ · 2π√11/10)`. -/
theorem norm_sub_posProj_kC_sq_le {c M : ℝ} (hc : 0 < c) {A : ℂ → ℂ}
    (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z)
    (hM : ∀ θ ∈ Icc 0 π, ‖A ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * I))‖ ≤ M)
    (h2 : MemLp (kC c A) 2 (volume : Measure ℝ)) :
    ‖h2.toLp _ - posProj (h2.toLp _)‖ ^ 2 ≤
      (M * (3 / 5) * π) ^ 2 * (1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.pi_pos.le⟩)
  set p := c * (√11 / 10 - 3 / 10) with hp
  set q := 2 * π * (√11 / 10) with hq
  have hp0 : 0 < p := mul_pos hc delta0_pos
  have hq0 : 0 < q := by positivity
  rw [Cvs.Upstream.HardyHalvesFourier.norm_sub_posProj_toLp_sq (integrable_kC c hA) h2,
    integral_Iio_eq_Ioi_neg (fun ξ => ‖𝓕 (kC c A) ξ‖ ^ 2),
    ← Cvs.Prolate.Hardy.LipPhaseDecay.integral_inv_sq_Ioi hp0 hq0, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    ((Cvs.Prolate.Hardy.LipPhaseDecay.integrableOn_inv_sq_Ioi hp0 hq0).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hξ0 : -ξ ≤ 0 := by linarith [hξ.out]
  have hb := Cvs.Prolate.Hardy.CarrierNegativeFrequencies.norm_fourier_kC_le hc hξ0 hA hM
  have ht : tArc c (-ξ) = p + q * ξ := by unfold tArc; rw [hp, hq]; ring
  rw [ht] at hb
  have hpq : 0 < p + q * ξ := by nlinarith [hξ.out]
  calc ‖𝓕 (kC c A) (-ξ)‖ ^ 2 ≤ (M * (3 / 5) * (π / (p + q * ξ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (M * (3 / 5) * π) ^ 2 * (1 / (p + q * ξ) ^ 2) := by field_simp

end Cvs.Prolate.Hardy.CarrierNegativeFreqRate

end
