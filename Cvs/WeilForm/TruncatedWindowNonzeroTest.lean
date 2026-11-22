import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated window carries a nonzero test function

    selfConvolution (indicator (Ioc 0 L) f) 0 = ∫_{Ioc 0 L} f²

which is `L` for the constant test, so the objects `Cvs.WeilForm.SpectralDensityForm` and `Cvs.WeilForm.HighFrequencyMassBound` are about are not
forced to vanish.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.TruncatedWindowNonzeroTest

/-- **The norm of a truncated test is its energy on the window.** -/
theorem selfConvolution_indicator_zero (L : ℝ) (f : ℝ → ℝ) :
    selfConvolution (Set.indicator (Set.Ioc 0 L) f) 0
      = ∫ s in Set.Ioc (0:ℝ) L, (f s) ^ 2 := by
  have hind : (fun s : ℝ => Set.indicator (Set.Ioc (0:ℝ) L) f s
      * Set.indicator (Set.Ioc (0:ℝ) L) f (s + 0))
      = (Set.Ioc (0:ℝ) L).indicator fun s => (f s) ^ 2 := by
    funext s
    by_cases hs : s ∈ Set.Ioc (0:ℝ) L
    · rw [add_zero, Set.indicator_of_mem hs, Set.indicator_of_mem hs, sq]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
  unfold selfConvolution
  rw [hind, integral_indicator measurableSet_Ioc]

/-- **The constant test has energy `L`.** -/
theorem selfConvolution_one_zero {L : ℝ} (hL : 0 ≤ L) :
    selfConvolution (Set.indicator (Set.Ioc (0:ℝ) L) (fun _ => 1)) 0 = L := by
  rw [selfConvolution_indicator_zero]
  simp [Real.volume_real_Ioc_of_le hL]

end Cvs.WeilForm.TruncatedWindowNonzeroTest
