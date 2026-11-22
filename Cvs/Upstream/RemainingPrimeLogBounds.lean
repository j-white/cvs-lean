import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Cvs.Upstream.PrimeLogsFromExpBounds

/-!
# The remaining six prime logarithms

`PrimeLogsFromExpBounds` reduces the prime side's logarithms to the nine primes `2,3,5,7,11,13,17,19,23`,
supplies `log 5`, and notes Mathlib has `2` and `3`.
-/

namespace Cvs.Moments

/-- One halving: bounds on `log p` from `exp(c/2)²`. -/
theorem log_bounds_sq {p clo chi : ℝ} (hp : 0 < p)
    (h1 : Real.exp (clo / 2) ^ 2 < p) (h2 : p < Real.exp (chi / 2) ^ 2) :
    clo < Real.log p ∧ Real.log p < chi := by
  rw [Cvs.Moments.exp_double] at h1 h2
  rw [show 2 * (clo / 2) = clo from by ring] at h1
  rw [show 2 * (chi / 2) = chi from by ring] at h2
  exact ⟨Cvs.Moments.lt_log_of_exp_lt hp h1, Cvs.Moments.log_lt_of_lt_exp hp h2⟩

/-- An upper series bound, twelve terms. -/
theorem exp_le_of_sum {x A : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (h : (∑ m ∈ Finset.range 12, x ^ m / (Nat.factorial m))
      + x ^ 12 * (12 + 1) / ((Nat.factorial 12) * 12) ≤ A) :
    Real.exp x ≤ A :=
  le_trans (Real.exp_bound' h0 h1 (n := 12) (by norm_num)) (by exact_mod_cast h)

/-- A lower series bound, twelve terms. -/
theorem le_exp_of_sum {x A : ℝ} (h0 : 0 ≤ x)
    (h : A ≤ ∑ m ∈ Finset.range 12, x ^ m / (Nat.factorial m)) :
    A ≤ Real.exp x :=
  le_trans h (Real.sum_le_exp_of_nonneg h0 12)

end Cvs.Moments
