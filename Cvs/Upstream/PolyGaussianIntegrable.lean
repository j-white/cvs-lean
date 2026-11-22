import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Polynomial times Gaussian is integrable
-/

namespace Cvs.Moments

open MeasureTheory
open scoped Real

/-- One term of the exponential series: `xᵐ/m! ≤ eˣ` for `x ≥ 0`. -/
theorem pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ m / (m.factorial) ≤ Real.exp x := by
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx (m + 1))
  refine Finset.single_le_sum (f := fun i => x ^ i / (i.factorial)) ?_ ?_
  · intro i _
    positivity
  · exact Finset.self_mem_range_succ m

/-- **The half-width Gaussian absorbs any even power.** -/
theorem pow_mul_exp_le {lam : ℝ} (hlam : 0 < lam) (m : ℕ) (y : ℝ) :
    y ^ (2 * m) * Real.exp (-lam * y ^ 2)
      ≤ (2 / lam) ^ m * (m.factorial) * Real.exp (-lam * y ^ 2 / 2) := by
  set x : ℝ := lam * y ^ 2 / 2 with hxdef
  have hx : 0 ≤ x := by rw [hxdef]; positivity
  have hser := pow_div_factorial_le_exp hx m
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hxm : x ^ m ≤ (m.factorial : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hfac] at hser
    linarith [hser]
  have hy : y ^ (2 * m) = (2 / lam) ^ m * x ^ m := by
    rw [hxdef, ← mul_pow, pow_mul]
    congr 1
    field_simp
  have hE1 : Real.exp (-lam * y ^ 2) = Real.exp (-x) * Real.exp (-lam * y ^ 2 / 2) := by
    rw [← Real.exp_add, hxdef]
    congr 1
    ring
  have hEx : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hpow : (0 : ℝ) ≤ (2 / lam) ^ m := by positivity
  have hEneg : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hEhalf : (0 : ℝ) < Real.exp (-lam * y ^ 2 / 2) := Real.exp_pos _
  rw [hy, hE1]
  have hstep : (2 / lam) ^ m * x ^ m * Real.exp (-x)
      ≤ (2 / lam) ^ m * (m.factorial : ℝ) := by
    have h1 : x ^ m * Real.exp (-x) ≤ (m.factorial : ℝ) := by
      nlinarith [hxm, hEneg, hEx]
    nlinarith [h1, hpow]
  nlinarith [hstep, hEhalf.le, hpow, hEneg.le]

/-- **Hence integrable.** -/
theorem integrable_pow_mul_gaussian {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    Integrable (fun y : ℝ => y ^ (2 * m) * Real.exp (-lam * y ^ 2)) := by
  have hhalf : (0 : ℝ) < lam / 2 := by linarith
  have hdom : Integrable (fun y : ℝ =>
      (2 / lam) ^ m * (m.factorial : ℝ) * Real.exp (-(lam / 2) * y ^ 2)) :=
    (integrable_exp_neg_mul_sq hhalf).const_mul _
  refine Integrable.mono' hdom (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  have hnn : (0 : ℝ) ≤ y ^ (2 * m) := by rw [pow_mul]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (Real.exp_pos _).le)]
  have h := pow_mul_exp_le hlam m y
  have heq : Real.exp (-lam * y ^ 2 / 2) = Real.exp (-(lam / 2) * y ^ 2) := by
    congr 1; ring
  rwa [heq] at h

end Cvs.Moments
