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
import Cvs.Xi.ThetaSumsTwiceDifferentiable
import Cvs.Xi.ThetaTermThirdDeriv
import Cvs.Xi.ThetaTermThirdDominated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The second derivative sum's derivative

On a bounded interval the third derivative terms are dominated uniformly by a summable sequence:
the cubic coefficient grows with the interval's right end, and the exponential in the index decays
from its left one. Termwise differentiation is then legitimate, so the sum of the third
derivatives is the derivative of the second derivative sum.
-/

noncomputable section

open Real Set

namespace Cvs.Xi.ThetaSecondSumDeriv

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable Cvs.Xi.ThetaTermThirdDeriv Cvs.Xi.ThetaTermThirdDominated

/-- The uniform dominating sequence for the third derivatives on `[A, B]`. -/
noncomputable def bnd3 (A B : ℝ) (n : ℕ) : ℝ :=
  exp (B / 2) * (1 / 8 + 31 / 2 * π * exp (2 * B) + 30 * π ^ 2 * exp (2 * B) ^ 2
      + 8 * π ^ 3 * exp (2 * B) ^ 3)
    * (((n : ℝ) ^ 6 + 1) * exp (-(π * exp (2 * A) * (n : ℝ) ^ 2)))

theorem summable_bnd3 (A B : ℝ) : Summable (bnd3 A B) := by
  have hA : 0 < π * exp (2 * A) := by positivity
  exact (summable_sextic_exp hA).mul_left _

/-- The third derivatives are uniformly dominated on `[A, B]`. -/
theorem abs_thetaTerm3_le_bnd {A B y : ℝ} (hA : A ≤ y) (hB : y ≤ B) (n : ℕ) :
    |thetaTerm3 n y| ≤ bnd3 A B n := by
  refine (abs_thetaTerm3_le n y).trans ?_
  have hey : exp (y / 2) ≤ exp (B / 2) := Real.exp_le_exp.mpr (by linarith)
  have he2 : exp (2 * y) ≤ exp (2 * B) := Real.exp_le_exp.mpr (by linarith)
  have hb : 1 / 8 + 31 / 2 * π * exp (2 * y) + 30 * π ^ 2 * exp (2 * y) ^ 2
        + 8 * π ^ 3 * exp (2 * y) ^ 3
      ≤ 1 / 8 + 31 / 2 * π * exp (2 * B) + 30 * π ^ 2 * exp (2 * B) ^ 2
        + 8 * π ^ 3 * exp (2 * B) ^ 3 := by
    have h1 : (0 : ℝ) ≤ 31 / 2 * π * (exp (2 * B) - exp (2 * y)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr he2)
    have h2 : (0 : ℝ)
        ≤ 30 * π ^ 2 * ((exp (2 * B) - exp (2 * y)) * (exp (2 * B) + exp (2 * y))) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr he2) (by positivity))
    have h3 : (0 : ℝ) ≤ 8 * π ^ 3 * ((exp (2 * B) - exp (2 * y))
        * (exp (2 * B) ^ 2 + exp (2 * B) * exp (2 * y) + exp (2 * y) ^ 2)) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr he2) (by positivity))
    nlinarith [h1, h2, h3]
  unfold bnd3
  refine mul_le_mul (mul_le_mul hey hb (by positivity) (Real.exp_pos _).le) ?_
    (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (exp_neg_mono hA n) (by positivity)

/-- **The second derivative sum's derivative is the sum of the third derivatives.** -/
theorem hasDerivAt_thetaSum2 (y : ℝ) : HasDerivAt thetaSum2 (thetaSum3 y) y := by
  refine hasDerivAt_tsum_of_isPreconnected
    ((summable_nat_add_iff 1).mpr (summable_bnd3 (y - 1) (y + 1)))
    isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => hasDerivAt_thetaTerm2 (n + 1) z) (fun n z hz => ?_)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
    (summable_thetaTerm2_shift y)
    (show y ∈ Ioo (y - 1) (y + 1) by constructor <;> linarith)
  rw [Real.norm_eq_abs]
  exact abs_thetaTerm3_le_bnd hz.1.le hz.2.le (n + 1)

end Cvs.Xi.ThetaSecondSumDeriv
