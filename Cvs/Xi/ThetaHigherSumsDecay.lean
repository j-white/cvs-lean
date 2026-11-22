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
import Cvs.Xi.ThetaOcticDominatingSeries
import Cvs.Xi.ThetaTermFourthDeriv
import Cvs.Xi.ThetaTermFourthDominated
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
# The third and fourth derivative sums decay on the half line

Each term of the two families is dominated by the octic series with a polynomial coefficient, and
a quarter of the inner factor pays that coefficient, so termwise the bound is the octic series
scaled by a constant. Summing keeps the scale, and what is left in front is a plain exponential
in the variable times the doubly exponential factor.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaHigherSumsDecay

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaTermThirdDeriv Cvs.Xi.ThetaTermThirdDominated Cvs.Xi.ThetaTermFourthDeriv Cvs.Xi.ThetaTermFourthDominated Cvs.Xi.ThetaOcticDominatingSeries

/-- The sixth power is below the eighth at every shifted index. -/
theorem sextic_le_octic_shift (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ 6 + 1 ≤ ((n + 1 : ℕ) : ℝ) ^ 8 + 1 := by
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    exact_mod_cast h
  have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have key : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 6 * (((n + 1 : ℕ) : ℝ) ^ 2 - 1) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [key]

/-- The third derivative term, against the octic series. -/
theorem abs_thetaTerm3_le_octic (n : ℕ) (u : ℝ) :
    |thetaTerm3 (n + 1) u|
      ≤ exp (u / 2) * (1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
          + 8 * π ^ 3 * exp (2 * u) ^ 3)
        * ((((n + 1 : ℕ) : ℝ) ^ 8 + 1)
          * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
  refine (abs_thetaTerm3_le (n + 1) u).trans ?_
  have hmono : (((n + 1 : ℕ) : ℝ) ^ 6 + 1)
        * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2))
      ≤ (((n + 1 : ℕ) : ℝ) ^ 8 + 1)
        * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_right (sextic_le_octic_shift n) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **The third derivative sum's bound on the half line.** -/
theorem abs_thetaSum3_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaSum3 u|
      ≤ ((216 / π ^ 3 + 26784 / π ^ 2 + 51840 / π + 13824)
          * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * domConst8 := by
  have hbd : ∀ n : ℕ, |thetaTerm3 (n + 1) u|
      ≤ ((216 / π ^ 3 + 26784 / π ^ 2 + 51840 / π + 13824)
        * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom8 n := fun n =>
    term_bound8 hu (by positivity) (prefactor_three_le hu) n (abs_thetaTerm3_le_octic n u)
  have hsummable : Summable (fun n : ℕ => |thetaTerm3 (n + 1) u|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbd (summable_bound8 _ u)
  have hnorm : Summable (fun n : ℕ => ‖thetaTerm3 (n + 1) u‖) := by
    simpa [Real.norm_eq_abs] using hsummable
  have h1 : |thetaSum3 u| ≤ ∑' n : ℕ, |thetaTerm3 (n + 1) u| := by
    unfold thetaSum3
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  refine h1.trans ?_
  have h2 := Summable.tsum_le_tsum hbd hsummable (summable_bound8 _ u)
  rw [tsum_mul_left] at h2
  exact h2

/-- **The fourth derivative sum's bound on the half line.** -/
theorem abs_thetaSum4_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaSum4 u|
      ≤ ((4096 / π ^ 4 + 2555904 / π ^ 3 + 10878976 / π ^ 2 + 7340032 / π + 1048576)
          * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * domConst8 := by
  have hbd : ∀ n : ℕ, |thetaTerm4 (n + 1) u|
      ≤ ((4096 / π ^ 4 + 2555904 / π ^ 3 + 10878976 / π ^ 2 + 7340032 / π + 1048576)
        * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom8 n := fun n =>
    term_bound8 hu (by positivity) (prefactor_four_le hu) n (abs_thetaTerm4_le (n + 1) u)
  have hsummable : Summable (fun n : ℕ => |thetaTerm4 (n + 1) u|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbd (summable_bound8 _ u)
  have hnorm : Summable (fun n : ℕ => ‖thetaTerm4 (n + 1) u‖) := by
    simpa [Real.norm_eq_abs] using hsummable
  have h1 : |thetaSum4 u| ≤ ∑' n : ℕ, |thetaTerm4 (n + 1) u| := by
    unfold thetaSum4
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  refine h1.trans ?_
  have h2 := Summable.tsum_le_tsum hbd hsummable (summable_bound8 _ u)
  rw [tsum_mul_left] at h2
  exact h2

end Cvs.Xi.ThetaHigherSumsDecay
