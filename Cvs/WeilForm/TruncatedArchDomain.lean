import Mathlib
import Cvs.Upstream.BoundedTruncationsIntegrable
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# Bounded truncated arch forms put a test function in the form's domain

    archTrunc δ f ≤ C for every δ > 0   ⟹   the Lévy integrand of `f` is integrable

so membership of the domain is a consequence of a bound on the truncations, not a separate
hypothesis to be carried.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.TruncatedArchDomain

/-- The Lévy integrand is measurable on the positive axis. -/
theorem aestronglyMeasurable_levy {f : ℝ → ℝ}
    (hfc : AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ)) :
    AEStronglyMeasurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have hd : ContinuousOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioi (0:ℝ)) := by
    refine ContinuousOn.div (f := fun u : ℝ => Real.exp (-(u / 4)))
      (g := fun u : ℝ => 1 - Real.exp (-u)) ?_ ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_id.div_const 4).neg).continuousOn
    · exact (continuous_const.sub (Real.continuous_exp.comp continuous_id.neg)).continuousOn
    · intro u hu
      have hu0 : (0:ℝ) < u := hu
      have : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      show (1:ℝ) - Real.exp (-u) ≠ 0
      exact ne_of_gt (by linarith)
  have hq : QuasiMeasurePreserving (fun u : ℝ => (2⁻¹ : ℝ) • u)
      (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (r := (2⁻¹ : ℝ))
      (by norm_num)
  have hhalf : AEStronglyMeasurable (fun u : ℝ => selfConvolution f (u / 2))
      (volume : Measure ℝ) := by
    have h := hfc.comp_quasiMeasurePreserving hq
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp [smul_eq_mul, div_eq_inv_mul]
  exact ((hd.aestronglyMeasurable measurableSet_Ioi).mul
    ((aestronglyMeasurable_const.sub hhalf).restrict))

/-- **A bound on the truncations puts `f` in the domain.** -/
theorem integrableOn_levy_of_bounded {f : ℝ → ℝ} {C : ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ))
    (hfc : AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ))
    (hbd : ∀ δ : ℝ, 0 < δ → Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ f ≤ C) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ) := by
  refine Cvs.Upstream.BoundedTruncationsIntegrable.integrableOn_of_bounded_truncations (C := C)
    (aestronglyMeasurable_levy hfc) ?_ ?_ ?_
  · intro u hu
    have hu0 : (0:ℝ) < u := hu
    have hd : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
    have hg : selfConvolution f (u / 2) ≤ selfConvolution f 0 :=
      Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (u / 2) hf
    exact mul_nonneg hd.le (by linarith)
  · intro δ hδ
    exact Cvs.WeilForm.Archimedean.TruncatedArchContinuous.integrableOn_archTrunc hδ hf hfc
  · intro δ hδ
    exact hbd δ hδ

end Cvs.WeilForm.TruncatedArchDomain
