import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithms of the primes, from exponential bounds

The prime side at `L = π` is thirteen terms `Λ(n)n^{−1/2}R(log n)`, and `R(log n)` needs
`n^{λ} = n^{ε/2}·e^{iβ log n}` — so every `log n` must be enclosed, and then `cos`/`sin`
evaluated at `β log n`.
-/

namespace Cvs.Moments

/-- A lower bound on `log` from an upper bound on `exp`. -/
theorem lt_log_of_exp_lt {x c : ℝ} (hx : 0 < x) (h : Real.exp c < x) :
    c < Real.log x := by
  have h2 : Real.exp c < Real.exp (Real.log x) := by
    rwa [Real.exp_log hx]
  exact Real.exp_lt_exp.mp h2

/-- An upper bound on `log` from a lower bound on `exp`. -/
theorem log_lt_of_lt_exp {x c : ℝ} (hx : 0 < x) (h : x < Real.exp c) :
    Real.log x < c := by
  have h2 : Real.exp (Real.log x) < Real.exp c := by
    rwa [Real.exp_log hx]
  exact Real.exp_lt_exp.mp h2

/-- Halving, as in. -/
theorem exp_double (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

end Cvs.Moments
