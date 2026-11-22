import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Cvs.Xi.PhiThetaDifferentialOperator
import Cvs.Xi.RiemannPhiKernel

/-!
# The kernel identity for the sums

The three theta families are summable at every `u`, and the termwise identity of the previous block
passes to the sums: `8Φ + H = 4H₂`, where `H` and `H₂` are the sums of the theta terms and of their
second derivatives.
-/

open Real

namespace Cvs.Xi.PhiKernelIdentitySums

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator

/-- Powers against a weight Gaussian in `n` are summable. -/
theorem summable_pow_mul_exp_neg_sq (k : ℕ) {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * exp (-(A * (n : ℝ) ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_mul_exp_neg_nat_mul k hA)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h := cast_le_sq n
  nlinarith [mul_nonneg hA.le (sub_nonneg.mpr h)]

/-- The series dominating all three families. -/
theorem summable_quartic_exp {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ => ((n : ℝ) ^ 4 + 1) * exp (-(A * (n : ℝ) ^ 2))) := by
  have h := (summable_pow_mul_exp_neg_sq 4 hA).add (summable_pow_mul_exp_neg_sq 0 hA)
  refine h.congr (fun n => ?_)
  rw [pow_zero]
  ring

theorem sq_le_quartic_add_one (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 + 1 := by
  nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]

/-- The theta term as an explicit product. -/
theorem thetaTerm_eq_prod (n : ℕ) (u : ℝ) :
    thetaTerm n u = exp (u / 2) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2)) := by
  unfold thetaTerm
  rw [show -(π * (n : ℝ) ^ 2 * exp (2 * u)) = -(π * exp (2 * u) * (n : ℝ) ^ 2) by ring]

theorem thetaTerm1_eq_prod (n : ℕ) (u : ℝ) :
    thetaTerm1 n u = exp (u / 2) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))
      * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) := by
  unfold thetaTerm1
  rw [thetaTerm_eq_prod]

theorem thetaTerm2_eq_prod (n : ℕ) (u : ℝ) :
    thetaTerm2 n u = exp (u / 2) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))
      * ((1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
        - 4 * π * (n : ℝ) ^ 2 * exp (2 * u)) := by
  unfold thetaTerm2
  rw [thetaTerm_eq_prod]

/-- The theta term is bounded by the dominating series. -/
theorem abs_thetaTerm_le (n : ℕ) (u : ℝ) :
    |thetaTerm n u|
      ≤ exp (u / 2) * (((n : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))) := by
  rw [abs_of_pos (thetaTerm_pos n u), thetaTerm_eq_prod]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hq : (1 : ℝ) ≤ (n : ℝ) ^ 4 + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    linarith
  exact le_mul_of_one_le_left (Real.exp_pos _).le hq

/-- The first derivative term is bounded by the dominating series. -/
theorem abs_thetaTerm1_le (n : ℕ) (u : ℝ) :
    |thetaTerm1 n u| ≤ exp (u / 2) * (1 / 2 + 2 * π * exp (2 * u))
      * (((n : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))) := by
  have hE : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hpi := Real.pi_pos
  have hsq := sq_le_quartic_add_one n
  have hkey : (0 : ℝ) ≤ 2 * π * exp (2 * u) * (((n : ℝ) ^ 4 + 1) - (n : ℝ) ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hsq)
  have hfac : |1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)|
      ≤ (1 / 2 + 2 * π * exp (2 * u)) * ((n : ℝ) ^ 4 + 1) := by
    have hq4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    have hq : (1 : ℝ) ≤ (n : ℝ) ^ 4 + 1 := by linarith
    have hnn : (0 : ℝ) ≤ 2 * π * (n : ℝ) ^ 2 * exp (2 * u) := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  have h1 : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have h2 : (0 : ℝ) < exp (-(π * exp (2 * u) * (n : ℝ) ^ 2)) := Real.exp_pos _
  rw [thetaTerm1_eq_prod, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2]
  nlinarith [mul_le_mul_of_nonneg_left hfac (mul_pos h1 h2).le]

/-- The second derivative term is bounded by the dominating series. -/
theorem abs_thetaTerm2_le (n : ℕ) (u : ℝ) :
    |thetaTerm2 n u|
      ≤ exp (u / 2) * (1 / 4 + 6 * π * exp (2 * u) + 4 * π ^ 2 * exp (2 * u) ^ 2)
        * (((n : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))) := by
  have hE : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hpi := Real.pi_pos
  have hsq := sq_le_quartic_add_one n
  have hq4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hq : (1 : ℝ) ≤ (n : ℝ) ^ 4 + 1 := by linarith
  have hfac : |(1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
      - 4 * π * (n : ℝ) ^ 2 * exp (2 * u)|
      ≤ (1 / 4 + 6 * π * exp (2 * u) + 4 * π ^ 2 * exp (2 * u) ^ 2) * ((n : ℝ) ^ 4 + 1) := by
    have h6 : (0 : ℝ) ≤ 6 * π * exp (2 * u) * (((n : ℝ) ^ 4 + 1) - (n : ℝ) ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hsq)
    have h4 : (0 : ℝ) ≤ 4 * π ^ 2 * exp (2 * u) ^ 2 * (((n : ℝ) ^ 4 + 1) - (n : ℝ) ^ 4) := by
      have : ((n : ℝ) ^ 4 + 1) - (n : ℝ) ^ 4 = 1 := by ring
      rw [this]; positivity
    have hnn2 : (0 : ℝ) ≤ 6 * π * (n : ℝ) ^ 2 * exp (2 * u) := by positivity
    have hnn4 : (0 : ℝ) ≤ 4 * π ^ 2 * (n : ℝ) ^ 4 * exp (2 * u) ^ 2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  have h1 : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have h2 : (0 : ℝ) < exp (-(π * exp (2 * u) * (n : ℝ) ^ 2)) := Real.exp_pos _
  rw [thetaTerm2_eq_prod, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2]
  nlinarith [mul_le_mul_of_nonneg_left hfac (mul_pos h1 h2).le]

theorem summable_thetaTerm (u : ℝ) : Summable (fun n : ℕ => thetaTerm n u) := by
  have hA : 0 < π * exp (2 * u) := by positivity
  exact Summable.of_norm_bounded ((summable_quartic_exp hA).mul_left (exp (u / 2)))
    (fun n => by simpa [Real.norm_eq_abs] using abs_thetaTerm_le n u)

theorem summable_thetaTerm1 (u : ℝ) : Summable (fun n : ℕ => thetaTerm1 n u) := by
  have hA : 0 < π * exp (2 * u) := by positivity
  exact Summable.of_norm_bounded
    ((summable_quartic_exp hA).mul_left (exp (u / 2) * (1 / 2 + 2 * π * exp (2 * u))))
    (fun n => by simpa [Real.norm_eq_abs, mul_assoc] using abs_thetaTerm1_le n u)

theorem summable_thetaTerm2 (u : ℝ) : Summable (fun n : ℕ => thetaTerm2 n u) := by
  have hA : 0 < π * exp (2 * u) := by positivity
  exact Summable.of_norm_bounded
    ((summable_quartic_exp hA).mul_left
      (exp (u / 2) * (1 / 4 + 6 * π * exp (2 * u) + 4 * π ^ 2 * exp (2 * u) ^ 2)))
    (fun n => by simpa [Real.norm_eq_abs, mul_assoc] using abs_thetaTerm2_le n u)

theorem summable_thetaTerm_shift (u : ℝ) : Summable (fun n : ℕ => thetaTerm (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (summable_thetaTerm u)

theorem summable_thetaTerm1_shift (u : ℝ) : Summable (fun n : ℕ => thetaTerm1 (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (summable_thetaTerm1 u)

theorem summable_thetaTerm2_shift (u : ℝ) : Summable (fun n : ℕ => thetaTerm2 (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (summable_thetaTerm2 u)

/-- The theta sum in the variable `u`. -/
noncomputable def thetaSum (u : ℝ) : ℝ := ∑' n : ℕ, thetaTerm (n + 1) u

/-- The sum of the first derivatives. -/
noncomputable def thetaSum1 (u : ℝ) : ℝ := ∑' n : ℕ, thetaTerm1 (n + 1) u

/-- The sum of the second derivatives. -/
noncomputable def thetaSum2 (u : ℝ) : ℝ := ∑' n : ℕ, thetaTerm2 (n + 1) u

/-- **The kernel identity for the sums.** -/
theorem eight_mul_riemannPhi_eq (u : ℝ) :
    8 * riemannPhi u + thetaSum u = 4 * thetaSum2 u := by
  have hp := summable_shifted u
  have ht := summable_thetaTerm_shift u
  unfold riemannPhi thetaSum thetaSum2
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hp.mul_left 8) ht]
  refine tsum_congr fun n => ?_
  have := eight_mul_phiTerm_eq (n + 1) u
  linarith

end Cvs.Xi.PhiKernelIdentitySums
