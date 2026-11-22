import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Cvs.Upstream.RemainingPrimeLogBounds

/-!
# `log 5` and `log 7` at working precision, and the last unhalved value
-/

namespace Cvs.Enclosure

/-- **`log 5`** to `1e−6`. -/
theorem log_five_bounds' :
    (1.609437 : ℝ) < Real.log 5 ∧ Real.log 5 < (1.609439 : ℝ) := by
  have ha : Real.exp (8047185 / 10000000 : ℝ) ≤ 2.2360671 :=
    Cvs.Moments.exp_le_of_sum (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb : (2.2360690 : ℝ) ≤ Real.exp (8047195 / 10000000 : ℝ) :=
    Cvs.Moments.le_exp_of_sum (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  refine Cvs.Moments.log_bounds_sq (by norm_num) ?_ ?_
  · have h : (1.609437 : ℝ) / 2 = 8047185 / 10000000 := by norm_num
    rw [h]
    have hsq : Real.exp (8047185 / 10000000 : ℝ) ^ 2 ≤ (2.2360671 : ℝ) ^ 2 := by gcongr
    have hn : (2.2360671 : ℝ) ^ 2 < 5 := by norm_num
    linarith
  · have h : (1.609439 : ℝ) / 2 = 8047195 / 10000000 := by norm_num
    rw [h]
    have hsq : (2.2360690 : ℝ) ^ 2 ≤ Real.exp (8047195 / 10000000 : ℝ) ^ 2 := by gcongr
    have hn : (5 : ℝ) < (2.2360690 : ℝ) ^ 2 := by norm_num
    linarith

/-- **`log 7`** to `1e−6`.  The lower constant is `√7` to eight digits. -/
theorem log_seven_bounds' :
    (1.945910 : ℝ) < Real.log 7 ∧ Real.log 7 < (1.945911 : ℝ) := by
  have ha : Real.exp (9729550 / 10000000 : ℝ) ≤ 2.6457513 :=
    Cvs.Moments.exp_le_of_sum (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hb : (2.6457524 : ℝ) ≤ Real.exp (9729555 / 10000000 : ℝ) :=
    Cvs.Moments.le_exp_of_sum (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  refine Cvs.Moments.log_bounds_sq (by norm_num) ?_ ?_
  · have h : (1.945910 : ℝ) / 2 = 9729550 / 10000000 := by norm_num
    rw [h]
    have hsq : Real.exp (9729550 / 10000000 : ℝ) ^ 2 ≤ (2.6457513 : ℝ) ^ 2 := by gcongr
    have hn : (2.6457513 : ℝ) ^ 2 < 7 := by norm_num
    linarith
  · have h : (1.945911 : ℝ) / 2 = 9729555 / 10000000 := by norm_num
    rw [h]
    have hsq : (2.6457524 : ℝ) ^ 2 ≤ Real.exp (9729555 / 10000000 : ℝ) ^ 2 := by gcongr
    have hn : (7 : ℝ) < (2.6457524 : ℝ) ^ 2 := by norm_num
    linarith

end Cvs.Enclosure
