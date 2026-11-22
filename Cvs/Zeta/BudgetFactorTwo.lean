import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Cvs.Zeta.BudgetPartialSummation

/-!
# The budget, with the factor of two
-/

namespace Cvs.Deficit

open MeasureTheory ArithmeticFunction

/-- The Abel integrand, evaluated. -/
theorem abel_integrand_eq {x : ℝ} :
    (∫ t in Set.Ioc (1:ℝ) x,
        deriv (fun u : ℝ => u ^ (-(1:ℝ)/2)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k)
      = -(1/2) * ∫ t in Set.Ioc (1:ℝ) x, t ^ (-(3:ℝ)/2) * Chebyshev.psi t := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht0 : t ≠ 0 := by have := (Set.mem_Ioc.mp ht).1; linarith
  rw [Cvs.Deficit.deriv_rpow_half ht0, Cvs.Deficit.sum_Icc_eq_psi,
    show (-(1:ℝ)/2 - 1) = -(3:ℝ)/2 by ring]
  ring

end Cvs.Deficit
