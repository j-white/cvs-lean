import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# Partial summation for the budget
-/

namespace Cvs.Deficit

open Finset MeasureTheory ArithmeticFunction

/-- `t ↦ t^{-1/2}` is differentiable away from `0`. -/
theorem differentiableAt_rpow_half {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (fun u : ℝ => u ^ (-(1:ℝ)/2)) t :=
  (Real.hasDerivAt_rpow_const (Or.inl ht)).differentiableAt

theorem deriv_rpow_half {t : ℝ} (ht : t ≠ 0) :
    deriv (fun u : ℝ => u ^ (-(1:ℝ)/2)) t = (-(1:ℝ)/2) * t ^ (-(1:ℝ)/2 - 1) :=
  (Real.hasDerivAt_rpow_const (Or.inl ht)).deriv

/-- The derivative is continuous on `[1, b]`, hence integrable there. -/
theorem integrableOn_deriv {b : ℝ} :
    IntegrableOn (deriv (fun u : ℝ => u ^ (-(1:ℝ)/2))) (Set.Icc 1 b) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
  refine ContinuousOn.congr (f := fun t : ℝ => (-(1:ℝ)/2) * t ^ (-(1:ℝ)/2 - 1)) ?_ ?_
  · refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id ?_)
    intro t ht
    exact Or.inl (by have := (Set.mem_Icc.mp ht).1; linarith)
  · intro t ht
    exact deriv_rpow_half (by have := (Set.mem_Icc.mp ht).1; linarith)

/-- No hypothesis on `b`: Mathlib's `sum_mul_eq_sub_integral_mul₀` handles `b < 1` by making both
sides collapse. -/
theorem abel_budget (b : ℝ) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, (k : ℝ) ^ (-(1:ℝ)/2) * vonMangoldt k
      = b ^ (-(1:ℝ)/2) * (∑ k ∈ Icc 0 ⌊b⌋₊, vonMangoldt k)
        - ∫ t in Set.Ioc 1 b,
            deriv (fun u : ℝ => u ^ (-(1:ℝ)/2)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, vonMangoldt k := by
  refine sum_mul_eq_sub_integral_mul₀ (c := fun n : ℕ => (vonMangoldt n : ℝ))
    (ArithmeticFunction.map_zero) b ?_ integrableOn_deriv
  intro t ht
  exact differentiableAt_rpow_half (by have := (Set.mem_Icc.mp ht).1; linarith)

/-- The Abel partial sums are Chebyshev's `ψ`: `Λ 0 = 0`, so `Icc` and `Ioc`
agree. -/
theorem sum_Icc_eq_psi (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, vonMangoldt k = Chebyshev.psi t := by
  rw [Chebyshev.psi, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp

end Cvs.Deficit
