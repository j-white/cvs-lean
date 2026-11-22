import Mathlib
import Cvs.Upstream.CauchySchwarzLine

/-!
# The pole channel is L²-continuous, because the window truncates its weight

    |∫ f·w − ∫ h·w| ≤ ‖f − h‖₂ · ‖w‖₂

The weight `exp (s/2)` is not in `L²(ℝ)`, so the pole functional is not continuous on the
line; restricted to the window it is bounded, and truncation puts it in `L²`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.PoleChannelL2Continuous

/-- **A continuous weight, truncated to the window, is in `L²`.** -/
theorem memLp_indicator_of_continuous {L : ℝ} {w : ℝ → ℝ} (hw : Continuous w) :
    MemLp (Set.indicator (Set.Ioc 0 L) w) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (Set.indicator (Set.Ioc 0 L) w) (volume : Measure ℝ) :=
    hw.aestronglyMeasurable.indicator measurableSet_Ioc
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hpt : ∀ x : ℝ, ‖Set.indicator (Set.Ioc 0 L) w x‖ ^ 2
      = Set.indicator (Set.Ioc 0 L) (fun y => ‖w y‖ ^ 2) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hon : IntegrableOn (fun y => ‖w y‖ ^ 2) (Set.Ioc (0:ℝ) L) (volume : Measure ℝ) :=
    (hw.norm.pow 2).integrableOn_Ioc
  exact (hon.integrable_indicator measurableSet_Ioc).congr
    (Filter.Eventually.of_forall fun x => (hpt x).symm)

/-- **The pole channel's linear functional is `L²`-continuous.** -/
theorem abs_integral_mul_sub_le {f h w : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hh : MemLp h 2 (volume : Measure ℝ)) (hw : MemLp w 2 (volume : Measure ℝ)) :
    |(∫ s : ℝ, f s * w s) - ∫ s : ℝ, h s * w s|
      ≤ Real.sqrt (∫ x : ℝ, (f x - h x) ^ 2) * Real.sqrt (∫ x : ℝ, w x ^ 2) := by
  have hIf : Integrable (fun s => f s * w s) volume := hf.integrable_mul hw
  have hIh : Integrable (fun s => h s * w s) volume := hh.integrable_mul hw
  have hsub : ((∫ s : ℝ, f s * w s) - ∫ s : ℝ, h s * w s) = ∫ s : ℝ, (f s - h s) * w s := by
    rw [← integral_sub hIf hIh]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  rw [hsub]
  exact Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le (hf.sub hh) hw

end Cvs.WeilForm.PoleChannelL2Continuous
