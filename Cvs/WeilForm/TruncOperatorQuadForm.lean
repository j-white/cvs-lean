import Mathlib
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.PoleTermOperator

/-!
# The operator's quadratic form is the truncated Weil form

For a continuous function supported in the window, `∫₀^L truncOp N L f · f` is the truncated
form `weilQWTrunc N P R` of its `L²` class plus the prime side; an eigenfunction therefore
carries its eigenvalue into the form as an exact Rayleigh value.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open Cvs.WeilForm.Archimedean.OffWindowDefect Cvs.WeilForm.PoleTermOperator

namespace Cvs.WeilForm.TruncOperatorQuadForm

variable {L : ℝ} {f : ℝ → ℝ}

/-- The line integral of a window-supported function is its interval integral. -/
theorem integral_eq_interval (hL : 0 ≤ L) {g : ℝ → ℝ} (hg : ∀ x, x ∉ Ioc (0:ℝ) L → g x = 0) :
    (∫ x, g x) = ∫ x in (0:ℝ)..L, g x := by
  rw [intervalIntegral.integral_of_le hL, setIntegral_eq_integral_of_forall_compl_eq_zero hg]

/-- The channel positivity `0 < bIdx k`. -/
theorem bIdx_pos (k : ℕ) : 0 < bIdx k := by
  unfold bIdx; positivity

/-- The rank-one moments over the line are the pole moments on the window. -/
theorem integral_exp_half_eq_poleA (hL : 0 ≤ L) (hs : ∀ x, x ∉ Ioc (0:ℝ) L → f x = 0) :
    (∫ x : ℝ, f x * Real.exp (x / 2)) = poleA L f := by
  rw [integral_eq_interval hL (fun x hx => by rw [hs x hx, zero_mul])]
  unfold poleA
  exact intervalIntegral.integral_congr fun s _ => mul_comm _ _

theorem integral_exp_neg_half_eq_poleB (hL : 0 ≤ L) (hs : ∀ x, x ∉ Ioc (0:ℝ) L → f x = 0) :
    (∫ x : ℝ, f x * Real.exp (-(x / 2))) = poleB L f := by
  rw [integral_eq_interval hL (fun x hx => by rw [hs x hx, zero_mul])]
  unfold poleB
  exact intervalIntegral.integral_congr fun s _ => mul_comm _ _

end Cvs.WeilForm.TruncOperatorQuadForm
