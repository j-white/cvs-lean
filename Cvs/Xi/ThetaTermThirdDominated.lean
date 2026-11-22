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
import Cvs.Xi.ThetaTermThirdDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The third derivative term is dominated

In the quantity the exponential carries, the cubic factor is a cubic in a single nonnegative
argument, so the triangle inequality bounds it by the same cubic with every sign made positive.
That cubic reaches the sixth power of the index, one power beyond the quartic series that
dominates the lower levels, so the dominating series here is the sextic one.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaTermThirdDominated

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaTermThirdDeriv

/-- The cubic factor, in the single argument the index and the exponential enter through. -/
theorem abs_cubic_factor_le {a : ℝ} (ha : 0 ≤ a) :
    |(1 / 2 - a) ^ 3 - 6 * a * (1 / 2 - a) - 4 * a|
      ≤ 1 / 8 + 31 / 4 * a + 15 / 2 * a ^ 2 + a ^ 3 := by
  have h2 : (0 : ℝ) ≤ a ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ a ^ 3 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

theorem sq_le_sextic_add_one (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have key : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 + 1)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) (by positivity))
    nlinarith [key]

theorem quartic_le_sextic_add_one (n : ℕ) : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 6 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have key : (0 : ℝ) ≤ (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [key]

/-- The series dominating the third derivative family. -/
theorem summable_sextic_exp {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ => ((n : ℝ) ^ 6 + 1) * exp (-(A * (n : ℝ) ^ 2))) := by
  have h := (summable_pow_mul_exp_neg_sq 6 hA).add (summable_pow_mul_exp_neg_sq 0 hA)
  refine h.congr (fun n => ?_)
  rw [pow_zero]
  ring

/-- The cubic factor at the index, with the powers of the index separated. -/
theorem abs_factor3_le (n : ℕ) (u : ℝ) :
    |(1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
        - 12 * π * (n : ℝ) ^ 2 * exp (2 * u)
          * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
        - 8 * π * (n : ℝ) ^ 2 * exp (2 * u)|
      ≤ 1 / 8 + 31 / 2 * π * (n : ℝ) ^ 2 * exp (2 * u)
        + 30 * π ^ 2 * (n : ℝ) ^ 4 * exp (2 * u) ^ 2
        + 8 * π ^ 3 * (n : ℝ) ^ 6 * exp (2 * u) ^ 3 := by
  have ha : (0 : ℝ) ≤ 2 * π * (n : ℝ) ^ 2 * exp (2 * u) := by positivity
  have heq : (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
      - 12 * π * (n : ℝ) ^ 2 * exp (2 * u)
        * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
      - 8 * π * (n : ℝ) ^ 2 * exp (2 * u)
      = (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
        - 6 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u))
          * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
        - 4 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) := by ring
  rw [heq]
  exact (abs_cubic_factor_le ha).trans (le_of_eq (by ring))

/-- The third derivative term is bounded by the dominating series. -/
theorem abs_thetaTerm3_le (n : ℕ) (u : ℝ) :
    |thetaTerm3 n u|
      ≤ exp (u / 2) * (1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
          + 8 * π ^ 3 * exp (2 * u) ^ 3)
        * (((n : ℝ) ^ 6 + 1) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))) := by
  have hE : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hpi := Real.pi_pos
  have hs2 := sq_le_sextic_add_one n
  have hs4 := quartic_le_sextic_add_one n
  have h6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
  have hq : (1 : ℝ) ≤ (n : ℝ) ^ 6 + 1 := by linarith
  have hfac : |(1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
      - 12 * π * (n : ℝ) ^ 2 * exp (2 * u)
        * (1 / 2 - 2 * π * (n : ℝ) ^ 2 * exp (2 * u))
      - 8 * π * (n : ℝ) ^ 2 * exp (2 * u)|
      ≤ (1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
          + 8 * π ^ 3 * exp (2 * u) ^ 3) * ((n : ℝ) ^ 6 + 1) := by
    refine (abs_factor3_le n u).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hs2
        (show (0 : ℝ) ≤ 31 / 2 * π * exp (2 * u) by positivity),
      mul_le_mul_of_nonneg_left hs4
        (show (0 : ℝ) ≤ 30 * π ^ 2 * exp (2 * u) ^ 2 by positivity),
      mul_le_mul_of_nonneg_left (show (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 6 + 1 by linarith)
        (show (0 : ℝ) ≤ 8 * π ^ 3 * exp (2 * u) ^ 3 by positivity),
      mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ (1 : ℝ) / 8 by norm_num)]
  have h1 : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have h2 : (0 : ℝ) < exp (-(π * exp (2 * u) * (n : ℝ) ^ 2)) := Real.exp_pos _
  rw [thetaTerm3_eq_prod, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2]
  nlinarith [mul_le_mul_of_nonneg_left hfac (mul_pos h1 h2).le]

theorem summable_thetaTerm3 (u : ℝ) : Summable (fun n : ℕ => thetaTerm3 n u) := by
  have hA : 0 < π * exp (2 * u) := by positivity
  exact Summable.of_norm_bounded
    ((summable_sextic_exp hA).mul_left
      (exp (u / 2) * (1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
        + 8 * π ^ 3 * exp (2 * u) ^ 3)))
    (fun n => by simpa [Real.norm_eq_abs, mul_assoc] using abs_thetaTerm3_le n u)

theorem summable_thetaTerm3_shift (u : ℝ) : Summable (fun n : ℕ => thetaTerm3 (n + 1) u) :=
  (summable_nat_add_iff (f := fun n : ℕ => thetaTerm3 n u) 1).mpr (summable_thetaTerm3 u)

/-- The sum of the third derivatives of the theta terms. -/
noncomputable def thetaSum3 (u : ℝ) : ℝ := ∑' n : ℕ, thetaTerm3 (n + 1) u

end Cvs.Xi.ThetaTermThirdDominated
