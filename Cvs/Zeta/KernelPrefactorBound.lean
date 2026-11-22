import Mathlib

/-!
# The kernel prefactor at its geometric value

`ZeroFreeHeightFive` bounds the theta tail by `2/(1 − e^{−πt}) ≤ 2.1` from `e^π > 21`.  The geometric
value is `2/(1 − e^{−π}) = 2.09033`, and `an earlier result`'s sharper `e^π` reaches it.
-/

noncomputable section

open Complex

namespace Cvs.Zeta.KernelPrefactorBound

/-- `e^π > 23.14`, one digit past `an earlier result`. -/
theorem exp_pi_gt_2314 : (23.14 : ℝ) < Real.exp Real.pi := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hmono : Real.exp 3.141592 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr hpi.le
  have hsplit : Real.exp 3.141592 = Real.exp 3 * Real.exp 0.141592 := by
    rw [← Real.exp_add]; norm_num
  have h3 : (20.0855 : ℝ) < Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have hcube : (2.7182818283 : ℝ) ^ 3 < (Real.exp 1) ^ 3 :=
      pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, ← Real.exp_one_pow]
    refine lt_of_le_of_lt ?_ hcube
    norm_num
  have hf : (1.15210 : ℝ) < Real.exp 0.141592 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.141592 : ℝ)) (by norm_num) 5
    refine lt_of_lt_of_le ?_ h
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  have h3p : (0:ℝ) < Real.exp 3 := Real.exp_pos _
  have hfp : (0:ℝ) < Real.exp 0.141592 := Real.exp_pos _
  nlinarith [hmono, hsplit, h3, hf, h3p, hfp]

end Cvs.Zeta.KernelPrefactorBound
