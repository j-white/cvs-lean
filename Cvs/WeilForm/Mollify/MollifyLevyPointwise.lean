import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifyArchDecreases
import Cvs.WeilForm.Mollify.MollifyL2Contraction
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.Mollify.ShiftedEnergyReal
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.Zeta.WeilPositivityStatement

/-!
# Mollification lowers the Lévy integrand pointwise

    levy (f⋆ρ) u ≤ levy f u   for every `u > 0`

so the archimedean channel drops, the constraint set's convergence condition is inherited,
and the energy does not rise.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifyLevyPointwise

variable {f ρ : ℝ → ℝ}

/-- **The Lévy integrand drops pointwise.** -/
theorem levy_conv_le (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) {u : ℝ} (hu : 0 < u) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ) u
      ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := by
  have hcm := Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hf hfm hρc hρs hρm hρi hρnn hρ1
  have h1 := Cvs.WeilForm.Mollify.MollifyArchDecreases.deficit_eq hcm (u / 2)
  have h2 := Cvs.WeilForm.Mollify.MollifyArchDecreases.deficit_eq hf (u / 2)
  have h3 := Cvs.WeilForm.Mollify.ShiftedEnergyReal.integral_shift_conv_le hf hfm hρc hρs hρm hρi hρnn hρ1 (u / 2)
  have hd := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu
  rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, h1, h2]
  exact mul_le_mul_of_nonneg_left (by linarith) hd.le

/-- **The mollification stays in the constraint set's convergence condition.** -/
theorem integrableOn_levy_conv (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1)
    (hint : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ)) (Set.Ioi 0)
      (volume : Measure ℝ) := by
  have hcm := Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hf hfm hρc hρs hρm hρi hρnn hρ1
  refine Integrable.mono' hint ?_ ?_
  · exact Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hcm).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    have hnn : 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ) u := by
      rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy]
      refine mul_nonneg (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le ?_
      have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2) hcm
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact levy_conv_le hf hfm hρc hρs hρm hρi hρnn hρ1 hu0

/-- **The archimedean channel drops.** -/
theorem archFull_conv_le (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1)
    (hint : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ)
      ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f := by
  have hconv := integrableOn_levy_conv hf hfm hρc hρs hρm hρi hρnn hρ1 hint
  refine setIntegral_mono_on hconv hint measurableSet_Ioi (fun u hu => ?_)
  exact levy_conv_le hf hfm hρc hρs hρm hρi hρnn hρ1 hu

/-- **The energy does not rise.** -/
theorem integral_conv_sq_le (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    (∫ s : ℝ, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s ^ 2) ≤ ∫ s : ℝ, f s ^ 2 := by
  have hcm := Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hf hfm hρc hρs hρm hρi hρnn hρ1
  have hL : Integrable (fun s : ℝ => Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s ^ 2)
      (volume : Measure ℝ) := hcm.integrable_sq
  have hRnn : 0 ≤ ∫ s : ℝ, f s ^ 2 := integral_nonneg fun s => sq_nonneg _
  have hlint := Cvs.WeilForm.Mollify.MollifyL2Contraction.lintegral_conv_sq_le hf hfm hρc hρs hρm hρi hρnn hρ1
  have hrw : ∀ s : ℝ, (∫ t : ℝ, f (s - t) * ρ t) ^ 2
      = Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s ^ 2 := fun s => by rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv]
  simp only [hrw] at hlint
  rw [← ofReal_integral_eq_lintegral_ofReal hL
    (Filter.Eventually.of_forall fun s => sq_nonneg _)] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff hRnn).mp hlint

end Cvs.WeilForm.Mollify.MollifyLevyPointwise
