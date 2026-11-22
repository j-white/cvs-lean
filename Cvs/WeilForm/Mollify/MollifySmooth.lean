import Mathlib
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# The mollification is smooth, and the kernel is even

    `f⋆ρ` is `C^n` for every `n`, and `ρ (−t) = ρ t`

the two properties of Mathlib's normalised bump that the mode-sum step will use.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.Mollify.MollifySmooth

/-- **The mollifier is even.** -/
theorem kernel_neg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ (-t) = Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ t :=
  ContDiffBump.normed_neg _ t

/-- **The mollifier is smooth.** -/
theorem contDiff_kernel {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ n (Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ) :=
  ContDiffBump.contDiff_normed (Cvs.WeilForm.Mollify.MollifierKernel.bump hδ)

/-- The mollification is Mathlib's convolution. -/
theorem conv_eq_convolution (g ρ : ℝ → ℝ) :
    Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv g ρ
      = MeasureTheory.convolution ρ g (ContinuousLinearMap.mul ℝ ℝ) (volume : Measure ℝ) := by
  funext s
  rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv, MeasureTheory.convolution]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
    simp [ContinuousLinearMap.mul_apply', mul_comm])

/-- **The mollification is smooth.** -/
theorem contDiff_conv {n : ℕ∞} {g : ℝ → ℝ} (hg : MemLp g 2 (volume : Measure ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ n (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv g (Cvs.WeilForm.Mollify.MollifierKernel.kernel hδ)) := by
  rw [conv_eq_convolution]
  exact (Cvs.WeilForm.Mollify.MollifierKernel.hasCompactSupport_kernel hδ).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) (contDiff_kernel hδ)
    (hg.locallyIntegrable (by norm_num))

end Cvs.WeilForm.Mollify.MollifySmooth
