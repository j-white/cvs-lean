import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyDensityIntegrable
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The majorant for the arch channel under dilation

    densityU (w/2) · (g 0 − g (w/2))   is integrable on `(0,∞)`

whenever the arch channel itself is, `g = selfConvolution f`: near the origin the two
densities have singularities of the same order, and far out the deficit is bounded.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.ArchDilationMajorant

/-- **The density on `(0,∞)` is continuous.** -/
theorem continuousOn_densityU :
    ContinuousOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioi (0:ℝ)) := by
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp (continuous_id.div_const 4).neg).continuousOn
  · exact (continuous_const.sub (Real.continuous_exp.comp continuous_id.neg)).continuousOn
  · intro u hu
    have hu0 : (0:ℝ) < u := hu
    have : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact (sub_pos.mpr this).ne'

/-- **Halving the displacement raises the density by at most a factor three, up to `1`.**
The two singularities are of the same order, so the comparison is by a constant. -/
theorem densityU_half_le {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2) ≤ 3 * Cvs.WeilForm.Archimedean.LevyDensity.densityU w := by
  set A : ℝ := Real.exp (-(w / 8)) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have hAlt : A < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hA78 : 7 / 8 ≤ A := by
    have h := Real.add_one_le_exp (-(w / 8))
    rw [← hA] at h
    linarith
  have h2 : Real.exp (-(w / 2 / 4)) = A := by rw [hA]; congr 1; ring
  have h4 : Real.exp (-(w / 2)) = A ^ 4 := by
    rw [hA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2' : Real.exp (-(w / 4)) = A ^ 2 := by
    rw [hA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h8 : Real.exp (-w) = A ^ 8 := by
    rw [hA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hp4 : A ^ 4 < 1 := pow_lt_one₀ hA0.le hAlt (by norm_num)
  have hp8 : A ^ 8 < 1 := pow_lt_one₀ hA0.le hAlt (by norm_num)
  have hd1 : 0 < 1 - A ^ 4 := by linarith
  have hd2 : 0 < 1 - A ^ 8 := by linarith
  rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU, Cvs.WeilForm.Archimedean.LevyDensity.densityU, h2, h4, h2', h8,
    mul_div_assoc', div_le_div_iff₀ hd1 hd2]
  have hkey : 1 + A ^ 4 ≤ 3 * A := by nlinarith [hA0, hAlt, hA78]
  have hfac : 1 - A ^ 8 = (1 - A ^ 4) * (1 + A ^ 4) := by ring
  rw [hfac]
  nlinarith [hA0, hd1, hkey, mul_pos hA0 hd1]

/-- **The halved density is integrable away from the origin.** -/
theorem integrableOn_densityU_half {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2)) (Set.Ioi δ)
      (volume : Measure ℝ) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff Cvs.WeilForm.Archimedean.LevyDensity.densityU δ
    (by norm_num : (0:ℝ) < 1 / 2)).mpr
    (Cvs.WeilForm.Archimedean.LevyDensityIntegrable.integrableOn_densityU (δ := (1/2) * δ) (by positivity))
  refine h.congr_fun (fun w _ => ?_) measurableSet_Ioi
  ring_nf

/-- **The majorant is integrable.** -/
theorem integrableOn_majorant {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hint : IntegrableOn (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (selfConvolution f 0 - selfConvolution f (u / 2))) (Set.Ioi 0) (volume : Measure ℝ)) :
    IntegrableOn (fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2)
      * (selfConvolution f 0 - selfConvolution f (w / 2))) (Set.Ioi 0) (volume : Measure ℝ) := by
  set E : ℝ := ∫ x : ℝ, f x ^ 2 with hE
  set D : ℝ → ℝ := fun w => selfConvolution f 0 - selfConvolution f (w / 2) with hD
  have hDnn : ∀ w : ℝ, 0 ≤ D w := fun w => by
    have := Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.selfConvolution_le_zero_shift (w / 2) hf
    rw [hD]; simp only; linarith
  have hDle : ∀ w : ℝ, D w ≤ 2 * E := fun w => by
    have h1 := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le (0:ℝ) hf
    have h2 := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le (w / 2) hf
    rw [hD]; simp only
    rw [← hE] at h1 h2
    linarith [(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp h2).1, (abs_le.mp h2).2]
  have hcontD : Continuous D := by
    rw [hD]
    exact continuous_const.sub ((Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).comp
      (continuous_id.div_const 2))
  have hhalf : ∀ w : ℝ, w ∈ Set.Ioi (0:ℝ) → w / 2 ∈ Set.Ioi (0:ℝ) := by
    intro w hw
    simp only [Set.mem_Ioi] at hw ⊢
    linarith
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2) * D w)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (continuousOn_densityU.comp (continuous_id.div_const 2).continuousOn hhalf).mul
      hcontD.continuousOn
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- near the origin the comparison is by a constant
    have hg : IntegrableOn (fun w : ℝ => 3 * (Cvs.WeilForm.Archimedean.LevyDensity.densityU w * D w))
        (Set.Ioc 0 1) (volume : Measure ℝ) :=
      (hint.mono_set Set.Ioc_subset_Ioi_self).const_mul 3
    refine Integrable.mono' hg (hmeas.mono_set Set.Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun w hw => ?_)
    have hw0 : 0 < w := hw.1
    have hnn : 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2) :=
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (half_pos hw0)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hDnn w))]
    have := densityU_half_le hw0 hw.2
    nlinarith [hDnn w, this]
  · -- far out the deficit is bounded
    have hsub : Set.Ioi (1:ℝ) ⊆ Set.Ioi (0:ℝ) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      linarith
    have hg : IntegrableOn (fun w : ℝ => 2 * E * Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2))
        (Set.Ioi 1) (volume : Measure ℝ) :=
      (integrableOn_densityU_half one_pos).const_mul (2 * E)
    refine Integrable.mono' hg (hmeas.mono_set hsub) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun w hw => ?_)
    have hw0 : 0 < w := lt_trans one_pos hw
    have hnn : 0 ≤ Cvs.WeilForm.Archimedean.LevyDensity.densityU (w / 2) :=
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (half_pos hw0)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (hDnn w))]
    nlinarith [hDle w, hnn]

end Cvs.WeilForm.Archimedean.ArchDilationMajorant
