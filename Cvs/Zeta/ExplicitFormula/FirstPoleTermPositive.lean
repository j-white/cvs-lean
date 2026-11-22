import Mathlib

/-!
# The first pole term, on the critical line and positive
-/

namespace Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive

open Complex MeasureTheory Filter
open scoped Real

theorem ne_zero_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) : z ≠ 0 := by
  intro h
  rw [h] at hz
  norm_num at hz

/-- `‖1/z‖ ≤ 2` on the strip: `‖z‖ ≥ |Re z| ≥ ½`. -/
theorem norm_one_div_le {z : ℂ} (hz : 1 / 2 ≤ z.re) : ‖(1 : ℂ) / z‖ ≤ 2 := by
  have h1 : (1 : ℝ) / 2 ≤ ‖z‖ := le_trans (le_trans hz (le_abs_self _)) (Complex.abs_re_le_norm z)
  have h2 : (0 : ℝ) < ‖z‖ := by linarith
  rw [norm_div, norm_one]
  rw [div_le_iff₀ h2]
  linarith

/-- `(1+|y|)³ ≥ 1 + y²`, so `an earlier result`'s cubic decay is majorised by the Lorentzian
`integrable_inv_one_add_sq` with no compact-part bookkeeping. -/
theorem cube_ge (y : ℝ) : 1 + y ^ 2 ≤ (1 + |y|) ^ 3 := by
  nlinarith [abs_nonneg y, sq_abs y, pow_nonneg (abs_nonneg y) 3]

/-- `Re (1/(½+iy)) = (½)/(¼+y²)` — a Lorentzian of half-width `½`, the height of
`Γ(s/2)`'s first pole. -/
theorem re_one_div_half (y : ℝ) :
    ((1 : ℂ) / (1 / 2 + (y : ℝ) * I)).re = (1 / 2) / (1 / 4 + y ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  norm_num
  ring

end Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive
