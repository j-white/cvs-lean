import Mathlib

/-!
# The bucket step, tightened

`an earlier result` bounds the zeros in bucket `n` by `N(n)`, every zero below `n`, throwing away a
factor of `n`.  Stopping at the bucket's own cardinality gives `N^{-5/2}` in place of
`N^{-3/2}`.  RH.md §3.20 and WHATDIDNTWORK.md carry the measurement.
-/

set_option maxHeartbeats 1600000

noncomputable section

set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

open Real MeasureTheory Set Finset

namespace Cvs.Zeta.ZeroCounting.BucketStepTightened

/-- `log x ≤ 4 x^{1/4}`, the quarter-power form. -/
theorem log_le_four_rpow_quarter {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 4 * x ^ (1/4 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log (x ^ (1/4 : ℝ)) = (1/4) * Real.log x := Real.log_rpow hx0 _
  have h2 : Real.log (x ^ (1/4 : ℝ)) ≤ x ^ (1/4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [h1] at h2
  linarith

/-- `(log x)² ≤ 16 √x`. -/
theorem logsq_le {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 16 * x ^ (1/2 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h := log_le_four_rpow_quarter hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hq : (0:ℝ) ≤ x ^ (1/4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hsq : (x ^ (1/4 : ℝ)) ^ 2 = x ^ (1/2 : ℝ) := by
    rw [← Real.rpow_natCast (x ^ (1/4:ℝ)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  nlinarith [hsq]

end Cvs.Zeta.ZeroCounting.BucketStepTightened
