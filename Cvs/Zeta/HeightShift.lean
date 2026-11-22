import Mathlib

/-!
# `T` versus `T'`

The last bookkeeping gap in the `O(log²T)` chain.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

/-- Recentring a ball at a nearby height, with a radius large enough to swallow the shift. -/
theorem closedBall_shift_subset {T T' r ρ : ℝ} (hTT' : |T' - T| ≤ 1) (hρ : r + 1 ≤ ρ) :
    closedBall (2 + (T' : ℂ) * I) r ⊆ closedBall (2 + (T : ℂ) * I) ρ := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw ⊢
  have hsh : ‖(2 + (T' : ℂ) * I) - (2 + (T : ℂ) * I)‖ = |T' - T| := by
    have : (2 + (T' : ℂ) * I) - (2 + (T : ℂ) * I) = ((T' - T : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖w - (2 + (T : ℂ) * I)‖
      = ‖(w - (2 + (T' : ℂ) * I)) + ((2 + (T' : ℂ) * I) - (2 + (T : ℂ) * I))‖ := by
        congr 1; ring
    _ ≤ ‖w - (2 + (T' : ℂ) * I)‖ + ‖(2 + (T' : ℂ) * I) - (2 + (T : ℂ) * I)‖ :=
        norm_add_le _ _
    _ ≤ r + 1 := by rw [hsh]; linarith
    _ ≤ ρ := hρ

/-- **The zero-free property transfers to the shifted, smaller ball.** `exists_zero_free_height'`
produces `T'` with a gap against the zeros of the ball about `2 + iT`; the Landau bound at
height `T'` wants the gap against the zeros of the ball about `2 + iT'`. -/
theorem zero_free_shift {T T' r ρ gap : ℝ} (hTT' : |T' - T| ≤ 1) (hρ : r + 1 ≤ ρ)
    (hfree : ∀ w : ℂ, w ∈ closedBall (2 + (T : ℂ) * I) ρ → riemannZeta w = 0 →
      gap ≤ |T' - w.im|) :
    ∀ w : ℂ, w ∈ closedBall (2 + (T' : ℂ) * I) r → riemannZeta w = 0 →
      gap ≤ |T' - w.im| :=
  fun w hw hw0 => hfree w (closedBall_shift_subset hTT' hρ hw) hw0

/-- `log|T'| ≤ log 2 + log|T|` when the heights differ by at most `1` and `|T| ≥ 1`. -/
theorem log_abs_shift_le {T T' : ℝ} (hT : 1 ≤ |T|) (hTT' : |T' - T| ≤ 1) :
    Real.log |T'| ≤ Real.log 2 + Real.log |T| := by
  have h1 : |T'| ≤ 2 * |T| := by
    have := abs_sub_abs_le_abs_sub T' T
    linarith
  have h2 : Real.log |T'| ≤ Real.log (2 * |T|) := by
    rcases le_or_gt |T'| 0 with h | h
    · have : |T'| = 0 := le_antisymm h (abs_nonneg _)
      rw [this, Real.log_zero]
      have : 0 ≤ Real.log (2 * |T|) := Real.log_nonneg (by linarith)
      linarith
    · exact Real.log_le_log h h1
  rwa [Real.log_mul (by norm_num) (by linarith)] at h2

end Cvs.Zeta
