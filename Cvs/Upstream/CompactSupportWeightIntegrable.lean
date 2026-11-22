import Mathlib

/-!
# A window function integrates against any continuous weight

    supp g ⊆ K compact,  g integrable,  w continuous  ⟹  g·w integrable

which is what supplies `Cvs.WeilForm.HighFrequencyMassBound`'s pole-weight hypotheses without a bound on the weight itself.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set

namespace Cvs.Upstream.CompactSupportWeightIntegrable

/-- **A compactly supported integrable function integrates against a continuous weight.** -/
theorem integrable_mul_weight {a b : ℝ} {g : ℝ → ℝ}
    (hgint : Integrable g (volume : Measure ℝ))
    (hsupp : ∀ x, x ∉ Set.Icc a b → g x = 0) {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable (fun s : ℝ => g s * w s) (volume : Measure ℝ) := by
  classical
  -- the truncated weight is bounded
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : ℝ, ‖Set.indicator (Set.Icc a b) w x‖ ≤ C := by
    by_cases hab : a ≤ b
    · obtain ⟨x₀, _, hx₀⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab)
        (hw.norm.continuousOn)
      refine ⟨‖w x₀‖, fun x => ?_⟩
      by_cases hx : x ∈ Set.Icc a b
      · rw [Set.indicator_of_mem hx]
        exact hx₀ hx
      · rw [Set.indicator_of_notMem hx]
        simpa using (norm_nonneg (w x₀))
    · refine ⟨0, fun x => ?_⟩
      rw [Set.indicator_of_notMem (by
        intro hmem
        exact hab (le_trans hmem.1 hmem.2))]
      simp
  have hmeas : AEStronglyMeasurable (Set.indicator (Set.Icc a b) w) (volume : Measure ℝ) :=
    hw.aestronglyMeasurable.indicator measurableSet_Icc
  have hprod : Integrable
      (fun s : ℝ => Set.indicator (Set.Icc a b) w s * g s) (volume : Measure ℝ) :=
    hgint.bdd_mul hmeas (Filter.Eventually.of_forall hC)
  refine hprod.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  by_cases hs : s ∈ Set.Icc a b
  · rw [Set.indicator_of_mem hs]; ring
  · rw [Set.indicator_of_notMem hs, hsupp s hs]; ring

end Cvs.Upstream.CompactSupportWeightIntegrable
