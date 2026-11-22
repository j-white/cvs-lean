import Mathlib

/-!
# The off-window defect of a window function

Outside the window the exponential kernel factors, so the archimedean channel's defect is a
finite exponential sum in the moments `∫₀ᴸ e^{±bu} f(u) du`, while a prime shift contributes
nothing beyond `L + a`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real intervalIntegral

namespace Cvs.WeilForm.Archimedean.OffWindowDefect

/-- The Lévy exponents in the window variable. -/
def bIdx (n : ℕ) : ℝ := 2 * n + 1 / 2

/-- **The convention bridge.**  `Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow`'s density exponents `¼ + k` double under `u = 2v`. -/
theorem bIdx_eq (n : ℕ) : bIdx n = 2 * (1 / 4 + (n : ℝ)) := by
  unfold bIdx; ring

end Cvs.WeilForm.Archimedean.OffWindowDefect
