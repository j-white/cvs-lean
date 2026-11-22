import Mathlib.Analysis.Calculus.SmoothSeries
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
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator

/-!
# The theta sums are twice differentiable, term by term

On a bounded interval the theta families are dominated uniformly, so the sum of the terms has the sum
of the first derivatives as its derivative, and again at the next level: `H' = H₁` and `H₁' = H₂`.
-/

open Real Set

namespace Cvs.Xi.ThetaSumsTwiceDifferentiable

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums

/-- The uniform dominating sequence for the first derivatives on `[A, B]`. -/
noncomputable def bnd1 (A B : ℝ) (n : ℕ) : ℝ :=
  exp (B / 2) * (1 / 2 + 2 * π * exp (2 * B))
    * (((n : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * A) * (n : ℝ) ^ 2)))

/-- The uniform dominating sequence for the second derivatives on `[A, B]`. -/
noncomputable def bnd2 (A B : ℝ) (n : ℕ) : ℝ :=
  exp (B / 2) * (1 / 4 + 6 * π * exp (2 * B) + 4 * π ^ 2 * exp (2 * B) ^ 2)
    * (((n : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * A) * (n : ℝ) ^ 2)))

theorem summable_bnd1 (A B : ℝ) : Summable (bnd1 A B) := by
  have hA : 0 < π * exp (2 * A) := by positivity
  exact (summable_quartic_exp hA).mul_left _

theorem summable_bnd2 (A B : ℝ) : Summable (bnd2 A B) := by
  have hA : 0 < π * exp (2 * A) := by positivity
  exact (summable_quartic_exp hA).mul_left _

theorem exp_neg_mono {A y : ℝ} (hA : A ≤ y) (n : ℕ) :
    exp (-(π * exp (2 * y) * (n : ℝ) ^ 2)) ≤ exp (-(π * exp (2 * A) * (n : ℝ) ^ 2)) := by
  refine Real.exp_le_exp.mpr ?_
  have heA : exp (2 * A) ≤ exp (2 * y) := Real.exp_le_exp.mpr (by linarith)
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_nonneg.mpr heA)]

/-- The first derivatives are uniformly dominated on `[A, B]`. -/
theorem abs_thetaTerm1_le_bnd {A B y : ℝ} (hA : A ≤ y) (hB : y ≤ B) (n : ℕ) :
    |thetaTerm1 n y| ≤ bnd1 A B n := by
  refine (abs_thetaTerm1_le n y).trans ?_
  have hey : exp (y / 2) ≤ exp (B / 2) := Real.exp_le_exp.mpr (by linarith)
  have he2 : exp (2 * y) ≤ exp (2 * B) := Real.exp_le_exp.mpr (by linarith)
  have hb : 1 / 2 + 2 * π * exp (2 * y) ≤ 1 / 2 + 2 * π * exp (2 * B) := by
    nlinarith [Real.pi_pos]
  unfold bnd1
  refine mul_le_mul (mul_le_mul hey hb (by positivity) (Real.exp_pos _).le) ?_
    (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (exp_neg_mono hA n) (by positivity)

/-- The second derivatives are uniformly dominated on `[A, B]`. -/
theorem abs_thetaTerm2_le_bnd {A B y : ℝ} (hA : A ≤ y) (hB : y ≤ B) (n : ℕ) :
    |thetaTerm2 n y| ≤ bnd2 A B n := by
  refine (abs_thetaTerm2_le n y).trans ?_
  have hey : exp (y / 2) ≤ exp (B / 2) := Real.exp_le_exp.mpr (by linarith)
  have he2 : exp (2 * y) ≤ exp (2 * B) := Real.exp_le_exp.mpr (by linarith)
  have hpos : (0 : ℝ) < exp (2 * y) := Real.exp_pos _
  have hb : 1 / 4 + 6 * π * exp (2 * y) + 4 * π ^ 2 * exp (2 * y) ^ 2
      ≤ 1 / 4 + 6 * π * exp (2 * B) + 4 * π ^ 2 * exp (2 * B) ^ 2 := by
    have h6 : (0 : ℝ) ≤ 6 * π * (exp (2 * B) - exp (2 * y)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr he2)
    have hsq : (0 : ℝ)
        ≤ 4 * π ^ 2 * ((exp (2 * B) - exp (2 * y)) * (exp (2 * B) + exp (2 * y))) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr he2) (by positivity))
    nlinarith
  unfold bnd2
  refine mul_le_mul (mul_le_mul hey hb (by positivity) (Real.exp_pos _).le) ?_
    (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (exp_neg_mono hA n) (by positivity)

/-- **The theta sum's derivative is the sum of the first derivatives.** -/
theorem hasDerivAt_thetaSum (y : ℝ) : HasDerivAt thetaSum (thetaSum1 y) y := by
  refine hasDerivAt_tsum_of_isPreconnected
    ((summable_nat_add_iff 1).mpr (summable_bnd1 (y - 1) (y + 1)))
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => hasDerivAt_thetaTerm (n + 1) z) (fun n z hz => ?_)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
    (summable_thetaTerm_shift y)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
  rw [Real.norm_eq_abs]
  exact abs_thetaTerm1_le_bnd hz.1.le hz.2.le (n + 1)

/-- **The first derivative sum's derivative is the sum of the second derivatives.** -/
theorem hasDerivAt_thetaSum1 (y : ℝ) : HasDerivAt thetaSum1 (thetaSum2 y) y := by
  refine hasDerivAt_tsum_of_isPreconnected
    ((summable_nat_add_iff 1).mpr (summable_bnd2 (y - 1) (y + 1)))
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => hasDerivAt_thetaTerm1 (n + 1) z) (fun n z hz => ?_)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
    (summable_thetaTerm1_shift y)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
  rw [Real.norm_eq_abs]
  exact abs_thetaTerm2_le_bnd hz.1.le hz.2.le (n + 1)

end Cvs.Xi.ThetaSumsTwiceDifferentiable
