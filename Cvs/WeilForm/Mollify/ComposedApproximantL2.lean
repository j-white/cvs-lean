import Mathlib
import Cvs.Upstream.L2DilationContinuity
import Cvs.Upstream.L2TranslationContinuity
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyDistanceContraction
import Cvs.WeilForm.Mollify.MollifyErrorVanishes
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# The composed approximant converges in `L²`

    ∫ (ξ n x − η x)² dx → 0

each of the three moves compared against the fixed `η`: dilation and translation are
isometries, mollification a contraction, so no moving modulus is ever needed.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Upstream.L2DilationContinuity

namespace Cvs.WeilForm.Mollify.ComposedApproximantL2

variable {L : ℝ} {η : ℝ → ℝ}

/-- The dilations approach the identity from inside the positive axis. -/
theorem tendsto_dila_within :
    Filter.Tendsto Cvs.WeilForm.Mollify.ComposedApproximant.dila Filter.atTop
      (nhdsWithin 1 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    Cvs.WeilForm.Mollify.ComposedApproximant.tendsto_dila ?_
  exact Filter.Eventually.of_forall fun n => Cvs.WeilForm.Mollify.ComposedApproximant.dila_pos n

/-- **The dilation error vanishes along the sequence.** -/
theorem tendsto_dilate_error (hη : MemLp η 2 (volume : Measure ℝ)) :
    Filter.Tendsto (fun n : ℕ => ∫ x : ℝ,
      (dilate (Cvs.WeilForm.Mollify.ComposedApproximant.dila n) η x - η x) ^ 2) Filter.atTop (nhds 0) := by
  have h := Cvs.Upstream.L2DilationContinuity.tendsto_integral_sub_dilate_sq hη
  exact h.comp tendsto_dila_within

/-- **The translation error vanishes along the sequence.** -/
theorem tendsto_translate_error (hη : MemLp η 2 (volume : Measure ℝ)) (L : ℝ) :
    Filter.Tendsto (fun n : ℕ => ∫ x : ℝ,
      (η (x + -(Cvs.WeilForm.Mollify.ComposedApproximant.shift L n)) - η x) ^ 2) Filter.atTop (nhds 0) := by
  have h := Cvs.Upstream.L2TranslationContinuity.tendsto_integral_sub_translate_sq hη
  have hu : Filter.Tendsto (fun n : ℕ => -(Cvs.WeilForm.Mollify.ComposedApproximant.shift L n))
      Filter.atTop (nhds 0) := by
    have := (Cvs.WeilForm.Mollify.ComposedApproximant.tendsto_shift L).neg
    simpa using this
  have hcomp := h.comp hu
  refine hcomp.congr (fun n => ?_)
  simp only [Function.comp_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- **The dilate-and-translate converges to the target.** -/
theorem tendsto_shifted_error (hη : MemLp η 2 (volume : Measure ℝ)) (L : ℝ) :
    Filter.Tendsto (fun n : ℕ => Real.sqrt (∫ x : ℝ,
      (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n x - η x) ^ 2)) Filter.atTop (nhds 0) := by
  set A : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ,
    (dilate (Cvs.WeilForm.Mollify.ComposedApproximant.dila n) η x - η x) ^ 2) with hA
  set B : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ,
    (η (x + -(Cvs.WeilForm.Mollify.ComposedApproximant.shift L n)) - η x) ^ 2) with hB
  have hAt : Filter.Tendsto A Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_dilate_error hη)
    simpa [hA, Real.sqrt_zero, Function.comp_def] using this
  have hBt : Filter.Tendsto B Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_translate_error hη L)
    simpa [hB, Real.sqrt_zero, Function.comp_def] using this
  refine squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => ?_) (by simpa using hAt.add hBt)
  -- the triangle inequality, through the translate of `η`
  set c : ℝ := -(Cvs.WeilForm.Mollify.ComposedApproximant.shift L n) with hc
  have hmid : MemLp (fun x : ℝ => η (x + c)) 2 (volume : Measure ℝ) :=
    Cvs.Upstream.L2TranslationContinuity.memLp_translate c hη
  have hsh : MemLp (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n) 2 (volume : Measure ℝ) :=
    Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hη L n
  have htri := Cvs.Upstream.L2TranslationContinuity.sqrt_integral_sub_sq_triangle hsh hmid hη
  have hfirst : (∫ x : ℝ, (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n x - η (x + c)) ^ 2)
      = ∫ x : ℝ, (dilate (Cvs.WeilForm.Mollify.ComposedApproximant.dila n) η x - η x) ^ 2 := by
    have h := Cvs.Upstream.L2TranslationContinuity.integral_sub_sq_translate
      (dilate (Cvs.WeilForm.Mollify.ComposedApproximant.dila n) η) η c
    refine Eq.trans ?_ h
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => rfl)
  rw [hfirst] at htri
  exact htri

/-- **The composed approximant converges in `L²`.** -/
theorem tendsto_pre_error (hL : 0 < L) (hη : MemLp η 2 (volume : Measure ℝ))
    (hηm : Measurable η) :
    Filter.Tendsto (fun n : ℕ => ∫ x : ℝ,
      (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n x - η x) ^ 2) Filter.atTop (nhds 0) := by
  set ρ : ℕ → ℝ → ℝ := fun n => Cvs.WeilForm.Mollify.MollifierKernel.kernel
    (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n) with hρ
  have hρc : ∀ n, Continuous (ρ n) := fun n => Cvs.WeilForm.Mollify.MollifierKernel.continuous_kernel _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    Cvs.WeilForm.Mollify.MollifierKernel.hasCompactSupport_kernel _
  have hρm : ∀ n, Measurable (ρ n) := fun n => Cvs.WeilForm.Mollify.MollifierKernel.measurable_kernel _
  have hρi : ∀ n, Integrable (ρ n) (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifierKernel.integrable_kernel _
  have hρnn : ∀ n, ∀ t : ℝ, 0 ≤ ρ n t := fun n t => Cvs.WeilForm.Mollify.MollifierKernel.kernel_nonneg _ t
  have hρ1 : ∀ n, (∫ t : ℝ, ρ n t) = 1 := fun n => Cvs.WeilForm.Mollify.MollifierKernel.integral_kernel _
  have hrad : ∀ n, ∀ t : ℝ, Cvs.WeilForm.Mollify.ComposedApproximant.shift L n < |t| → ρ n t = 0 :=
    fun n t ht => Cvs.WeilForm.Mollify.MollifierKernel.kernel_eq_zero _ ht
  -- the mollification error at the fixed target
  have hmoll := Cvs.WeilForm.Mollify.MollifyErrorVanishes.tendsto_integral_conv_sub hη hηm hρc hρs hρm hρi
    hρnn hρ1 hrad (Cvs.WeilForm.Mollify.ComposedApproximant.tendsto_shift L)
  set A : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ,
    (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n x - η x) ^ 2) with hA
  set B : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ,
    (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv η (ρ n) x - η x) ^ 2) with hB
  have hAt : Filter.Tendsto A Filter.atTop (nhds 0) := tendsto_shifted_error hη L
  have hBt : Filter.Tendsto B Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hmoll
    simpa [hB, Real.sqrt_zero, Function.comp_def] using this
  have hsum : Filter.Tendsto (fun n : ℕ => (A n + B n) ^ 2) Filter.atTop (nhds 0) := by
    have := (hAt.add hBt).pow 2
    simpa using this
  refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hsum
  -- the triangle inequality, through the mollification of the target
  have hsh : MemLp (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n) 2 (volume : Measure ℝ) :=
    Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hη L n
  have hshm : Measurable (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n) :=
    Cvs.WeilForm.Mollify.ComposedApproximant.measurable_shifted hηm L n
  have hpre : MemLp (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n) 2 (volume : Measure ℝ) :=
    Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hsh hshm (hρc n) (hρs n) (hρm n) (hρi n) (hρnn n) (hρ1 n)
  have hcη : MemLp (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv η (ρ n)) 2 (volume : Measure ℝ) :=
    Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hη hηm (hρc n) (hρs n) (hρm n) (hρi n) (hρnn n) (hρ1 n)
  have htri := Cvs.Upstream.L2TranslationContinuity.sqrt_integral_sub_sq_triangle hpre hcη hη
  have hcontr := Cvs.WeilForm.Mollify.MollifyDistanceContraction.integral_conv_sub_conv_le hsh hshm hη hηm
    (hρc n) (hρs n) (hρm n) (hρi n) (hρnn n) (hρ1 n)
  have hfirst : Real.sqrt (∫ x : ℝ, (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n x
      - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv η (ρ n) x) ^ 2) ≤ A n := by
    rw [hA]
    exact Real.sqrt_le_sqrt hcontr
  have hbound : Real.sqrt (∫ x : ℝ, (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n x - η x) ^ 2)
      ≤ A n + B n := by
    refine le_trans htri ?_
    exact add_le_add hfirst (le_of_eq rfl)
  have hnn : 0 ≤ ∫ x : ℝ, (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n x - η x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  nlinarith [Real.sq_sqrt hnn, hbound,
    Real.sqrt_nonneg (∫ x : ℝ, (Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n x - η x) ^ 2),
    Real.sqrt_nonneg (∫ x : ℝ, (Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n x - η x) ^ 2),
    Real.sqrt_nonneg (∫ x : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv η (ρ n) x - η x) ^ 2)]

end Cvs.WeilForm.Mollify.ComposedApproximantL2
