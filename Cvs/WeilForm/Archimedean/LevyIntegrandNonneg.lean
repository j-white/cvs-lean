import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Lévy integrand is nonnegative, so truncation only decreases

    selfConvolution f u ≤ selfConvolution f 0      and      archTrunc δ f ≤ archFull f

The deficit `g 0 − g u` is half the shifted energy `∫ (f s − f (s+u))²`, hence nonnegative.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.LevyIntegrandNonneg

/-- **The self-convolution peaks at the origin.** -/
theorem selfConvolution_le_zero_shift {f : ℝ → ℝ} (u : ℝ)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    selfConvolution f u ≤ selfConvolution f 0 := by
  have hfu : MemLp (fun s => f (s + u)) 2 (volume : Measure ℝ) :=
    hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u)
  have hsq : Integrable (fun s => f s ^ 2) (volume : Measure ℝ) := hf.integrable_sq
  have hcross : Integrable (fun s => f s * f (s + u)) (volume : Measure ℝ) :=
    hf.integrable_mul hfu
  have hkey := Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq u hsq hcross
  have hnn : 0 ≤ ∫ s : ℝ, (f s - f (s + u)) ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  rw [hkey] at hnn
  linarith

/-- The split of `Ioi 0` at the cut. -/
theorem archFull_eq_head_add_trunc {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0) (volume : Measure ℝ)) :
    Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f
      = (∫ u in Set.Ioc (0:ℝ) δ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution f 0 - selfConvolution f (u / 2)))
        + Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ f := by
  rw [Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull, Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc,
    ← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi (le_refl δ)) measurableSet_Ioi
      (hint.mono_set (fun u hu => hu.1)) (hint.mono_set (fun u hu => lt_trans hδ hu)),
    Set.Ioc_union_Ioi_eq_Ioi hδ.le]

/-- **Truncating the Lévy integral only decreases it.** -/
theorem archTrunc_le_archFull {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hint : IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0) (volume : Measure ℝ)) :
    Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ f ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f := by
  rw [archFull_eq_head_add_trunc hδ hint]
  have hhead : 0 ≤ ∫ u in Set.Ioc (0:ℝ) δ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2)) := by
    refine setIntegral_nonneg measurableSet_Ioc fun u hu => ?_
    have hu0 : (0:ℝ) < u := hu.1
    have hd : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    have hg : selfConvolution f (u / 2) ≤ selfConvolution f 0 :=
      selfConvolution_le_zero_shift (u / 2) hf
    exact mul_nonneg hd.le (by linarith)
  linarith

end Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
