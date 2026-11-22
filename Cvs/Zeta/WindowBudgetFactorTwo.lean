import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Cvs.Zeta.BudgetFactorTwo
import Cvs.Zeta.BudgetIntegralTermLower
import Cvs.Zeta.BudgetIntegralTermSecondLog
import Cvs.Zeta.BudgetPartialSummation
import Cvs.Zeta.BudgetPartialSummationIntegrals

/-!
# The window, with the factor of two

`BudgetFactorTwo` doubles the constant for the *full* budget `B(x) = ∑_{n ≤ x} Λ(n)/√n`.
-/

namespace Cvs.Deficit

open MeasureTheory ArithmeticFunction

/-- The integrand, bounded above by Chebyshev. -/
theorem integrand_le {t : ℝ} (ht : 1 ≤ t) :
    t ^ (-(3:ℝ)/2) * Chebyshev.psi t ≤ (Real.log 4 + 4) * t ^ (-(1:ℝ)/2) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hr0 : (0:ℝ) < t ^ (-(3:ℝ)/2) := Real.rpow_pos_of_pos ht0 _
  have e1 : t ^ (-(3:ℝ)/2) * t = t ^ (-(1:ℝ)/2) := by
    have h : t ^ (-(3:ℝ)/2) * t ^ (1:ℝ) = t ^ (-(3:ℝ)/2 + (1:ℝ)) :=
      (Real.rpow_add ht0 _ _).symm
    rw [Real.rpow_one] at h
    rw [h]; norm_num
  have hpsi : Chebyshev.psi t ≤ (Real.log 4 + 4) * t :=
    Chebyshev.psi_le_const_mul_self ht0.le
  calc t ^ (-(3:ℝ)/2) * Chebyshev.psi t
      ≤ t ^ (-(3:ℝ)/2) * ((Real.log 4 + 4) * t) :=
        mul_le_mul_of_nonneg_left hpsi hr0.le
    _ = (Real.log 4 + 4) * (t ^ (-(3:ℝ)/2) * t) := by ring
    _ = (Real.log 4 + 4) * t ^ (-(1:ℝ)/2) := by rw [e1]

/-- **The budget, bounded above.**  `B(y) ≤ (log 4 + 4)(2√y − 1)`. -/
theorem budget_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (k : ℝ) ^ (-(1:ℝ)/2) * vonMangoldt k
      ≤ (Real.log 4 + 4) * (2 * y ^ ((1:ℝ)/2) - 1) := by
  have hy0 : (0:ℝ) < y := by linarith
  have habel := Cvs.Deficit.abel_budget y
  rw [Cvs.Deficit.abel_integrand_eq, Cvs.Deficit.sum_Icc_eq_psi] at habel
  -- boundary term
  have hbdry : y ^ (-(1:ℝ)/2) * Chebyshev.psi y ≤ (Real.log 4 + 4) * y ^ ((1:ℝ)/2) := by
    have hr0 : (0:ℝ) < y ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hy0 _
    have e1 : y ^ (-(1:ℝ)/2) * y = y ^ ((1:ℝ)/2) := by
      have h : y ^ (-(1:ℝ)/2) * y ^ (1:ℝ) = y ^ (-(1:ℝ)/2 + (1:ℝ)) :=
        (Real.rpow_add hy0 _ _).symm
      rw [Real.rpow_one] at h
      rw [h]; norm_num
    have hpsi := Chebyshev.psi_le_const_mul_self hy0.le
    calc y ^ (-(1:ℝ)/2) * Chebyshev.psi y
        ≤ y ^ (-(1:ℝ)/2) * ((Real.log 4 + 4) * y) :=
          mul_le_mul_of_nonneg_left hpsi hr0.le
      _ = (Real.log 4 + 4) * (y ^ (-(1:ℝ)/2) * y) := by ring
      _ = (Real.log 4 + 4) * y ^ ((1:ℝ)/2) := by rw [e1]
  -- integral term
  have hmono : ∫ t in Set.Ioc (1:ℝ) y, t ^ (-(3:ℝ)/2) * Chebyshev.psi t
      ≤ ∫ t in Set.Ioc (1:ℝ) y, (Real.log 4 + 4) * t ^ (-(1:ℝ)/2) := by
    refine setIntegral_mono_on (Cvs.Deficit.integrableOn_psi_weighted y)
      ((Cvs.Deficit.integrableOn_rpow (-(1:ℝ)/2) y).const_mul _) measurableSet_Ioc ?_
    intro t ht
    exact integrand_le (le_of_lt (Set.mem_Ioc.mp ht).1)
  have hval : (∫ t in Set.Ioc (1:ℝ) y, (Real.log 4 + 4) * t ^ (-(1:ℝ)/2))
      = (Real.log 4 + 4) * (2 * (y ^ ((1:ℝ)/2) - 1)) := by
    rw [integral_const_mul, Cvs.Deficit.integral_rpow_neg_half hy]
  rw [hval] at hmono
  rw [habel]
  linarith [hbdry, hmono]

end Cvs.Deficit
