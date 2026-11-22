import Mathlib
import Cvs.Upstream.RemainingPrimeLogBounds

/-!
# `ψ(¼)`, the constant the archimedean place keeps producing

Three separate places in this chain end at the same number.
-/

namespace Cvs.Moments

open scoped Real

/-- `log π`, by one halving.  `e^{1.1447/2} ≤ 1.772429` and `1.772429² < π`;
`1.7725 ≤ e^{1.1448/2}` and `π < 1.7725²`. -/
theorem log_pi_bounds :
    (1.1447 : ℝ) < Real.log π ∧ Real.log π < (1.1448 : ℝ) := by
  have ha : Real.exp (57235 / 100000 : ℝ) ≤ 1.772429 :=
    Cvs.Moments.exp_le_of_sum (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb : (1.7725 : ℝ) ≤ Real.exp (5724 / 10000 : ℝ) :=
    Cvs.Moments.le_exp_of_sum (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  refine Cvs.Moments.log_bounds_sq Real.pi_pos ?_ ?_
  · have he : (1.1447 : ℝ) / 2 = 57235 / 100000 := by norm_num
    rw [he]
    have hp := Real.pi_gt_d6
    nlinarith [ha, hp, (Real.exp_pos (57235 / 100000 : ℝ)).le]
  · have he : (1.1448 : ℝ) / 2 = 5724 / 10000 := by norm_num
    rw [he]
    have hp := Real.pi_lt_d6
    nlinarith [hb, hp]

/-- **`ψ(¼)` from reflection and duplication.**  The two hypotheses are the
logarithmic derivatives of `Gamma_mul_Gamma_one_sub` and
`Gamma_mul_Gamma_add_half` at `s = ¼`. -/
theorem digamma_quarter_of
    (hrefl : Complex.digamma (1 / 4) - Complex.digamma (3 / 4) = -(π : ℂ))
    (hdup : 2 * Complex.digamma (1 / 2)
      = 2 * Complex.log 2 + Complex.digamma (1 / 4) + Complex.digamma (3 / 4)) :
    Complex.digamma (1 / 4)
      = -(Real.eulerMascheroniConstant : ℂ) - 3 * Complex.log 2 - (π : ℂ) / 2 := by
  have hhalf := Complex.digamma_one_half
  linear_combination (-1 / 2) * hdup + (1 / 2) * hrefl + hhalf

end Cvs.Moments
