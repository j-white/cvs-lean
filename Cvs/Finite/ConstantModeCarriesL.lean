import Mathlib

/-!
# The constant mode carries `L`, not `L/2`

    ∫₀^L cos(0·x)·cos(0·(x+u)) dx = L

so `Cvs.WeilForm.ShiftSumModeDiagonal.integral_shift_mode`'s `L/2`, and every result resting on it, holds for `n ≥ 1`
only.  The exclusion is necessary, not incidental.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real intervalIntegral

namespace Cvs.Finite.ConstantModeCarriesL

/-- **The constant mode's self-overlap is the whole length.** -/
theorem integral_mode_zero (L u : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * (0:ℕ) / L * x)
        * Real.cos (2 * π * (0:ℕ) / L * (x + u))) = L := by
  have hzero : ∀ x : ℝ, Real.cos (2 * π * (0:ℕ) / L * x)
      * Real.cos (2 * π * (0:ℕ) / L * (x + u)) = 1 := by
    intro x
    norm_num
  rw [intervalIntegral.integral_congr (fun x _ => hzero x)]
  simp

end Cvs.Finite.ConstantModeCarriesL
