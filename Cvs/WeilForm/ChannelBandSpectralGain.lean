import Mathlib

/-!
# The channel band and its spectral gain

Between two truncations the pole, the constant and the prime refund are the same, so the
increment is the band of Lévy channels `[N, M)` weighed against the spectral density, and that
weight grows with the frequency: a class whose low-frequency mass is a fraction `θ` of its norm
gains at least `(1 − θ)` of the band's weight at the cut-off frequency.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.ChannelBandSpectralGain

/-- One Lévy channel's spectral weight. -/
def chanWeight (a t : ℝ) : ℝ := 1 / a - a / (a ^ 2 + (t / 2) ^ 2)

/-- **The channel weight in closed form.** -/
theorem chanWeight_eq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    chanWeight a t = (t / 2) ^ 2 / (a * (a ^ 2 + (t / 2) ^ 2)) := by
  have hd : (0:ℝ) < a ^ 2 + (t / 2) ^ 2 := by positivity
  unfold chanWeight
  field_simp
  ring

/-- **The channel weight is nonnegative.** -/
theorem chanWeight_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ chanWeight a t := by
  rw [chanWeight_eq ha]
  positivity

end Cvs.WeilForm.ChannelBandSpectralGain
