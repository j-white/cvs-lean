import Mathlib
import Cvs.Finite.ConstantModeWindowDamped
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated constant mode's Lévy deficit, in closed form

    L − g(u/2) = min (u/2) L,    g = selfConvolution (indicator (Ioc 0 L) 1)

so the deficit is bounded by `u/2` uniformly in `L`, and the constant mode's Lévy energy is
bounded by a constant that does not grow with the window.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.ConstantModeLevyDeficit

open Cvs.WeilForm.Archimedean.LevyDensity

/-- **The deficit, exactly.**  Linear until the translate clears the window, flat after. -/
theorem deficit_eq_min {L : ℝ} (hL : 0 ≤ L) {u : ℝ} (hu : 0 ≤ u) :
    L - selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => (1:ℝ))) (u / 2)
      = min (u / 2) L := by
  rcases le_or_gt (u / 2) L with h | h
  · rw [Cvs.Finite.ConstantModeWindowDamped.selfConvolution_indicator_one (by linarith) h, min_eq_left h]
    ring
  · rw [Cvs.WeilForm.AutocorrSelfConvolution.selfConvolution_indicator_eq_zero L (fun _ => (1:ℝ))
      (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u / 2)]; linarith),
      min_eq_right h.le]
    ring

end Cvs.Finite.ConstantModeLevyDeficit
