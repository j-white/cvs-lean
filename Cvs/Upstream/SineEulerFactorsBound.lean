import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sine is its first `N` Euler factors, up to `exp (‖u‖² / N)`

Euler's product writes `sin (π u)` as `π u ∏ (1 - u² / (j+1)²)`.  The factors past the `N`-th
multiply to at most `exp (‖u‖² ∑_{j ≥ N} 1 / (j+1)²)`, and that sum is at most `1 / N`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset Filter Topology

namespace Cvs.Upstream.SineEulerFactorsBound

/-- **The reciprocal squares past `N` sum to at most `1 / N`**, by telescoping. -/
theorem sum_Ico_inv_sq_le {N : ℕ} (hN : 0 < N) {n : ℕ} (hn : N ≤ n) :
    ∑ j ∈ Ico N n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hN hn
    have hstep : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
      have h1 : (1 : ℝ) / n - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [h1]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith

/-- **The Euler factors from `N` to `n` multiply to at most `exp (‖u‖² / N)`.** -/
theorem norm_prod_Ico_le {N : ℕ} (hN : 0 < N) {n : ℕ} (hn : N ≤ n) (u : ℂ) :
    ‖∏ j ∈ Ico N n, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)‖ ≤ exp (‖u‖ ^ 2 / N) := by
  rw [Complex.norm_prod]
  have hfac : ∀ j ∈ Ico N n, ‖(1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2‖
      ≤ 1 + ‖u‖ ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j _
    have hj : ‖((j : ℂ) + 1) ^ 2‖ = ((j : ℝ) + 1) ^ 2 := by
      rw [norm_pow]
      have : ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2‖
        ≤ ‖(1 : ℂ)‖ + ‖u ^ 2 / ((j : ℂ) + 1) ^ 2‖ := norm_sub_le _ _
      _ = 1 + ‖u‖ ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) := by
          rw [norm_one, norm_div, norm_pow, hj]; ring
  calc ∏ j ∈ Ico N n, ‖(1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2‖
      ≤ ∏ j ∈ Ico N n, (1 + ‖u‖ ^ 2 * (1 / ((j : ℝ) + 1) ^ 2)) :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) hfac
    _ ≤ exp (∑ j ∈ Ico N n, ‖u‖ ^ 2 * (1 / ((j : ℝ) + 1) ^ 2)) :=
        Real.prod_one_add_le_exp_sum _ fun j => by positivity
    _ ≤ exp (‖u‖ ^ 2 / N) := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum, div_eq_mul_one_div (‖u‖ ^ 2)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h := sum_Ico_inv_sq_le hN hn
        have hn0 : (0 : ℝ) ≤ 1 / n := by positivity
        linarith

/-- **The sine is its first `N` Euler factors, up to `exp (‖u‖² / N)`.** -/
theorem norm_sin_le {N : ℕ} (hN : 0 < N) (u : ℂ) :
    ‖Complex.sin (π * u)‖
      ≤ ‖(π : ℂ) * u * ∏ j ∈ range N, ((1 : ℂ) - u ^ 2 / ((j : ℂ) + 1) ^ 2)‖
        * exp (‖u‖ ^ 2 / N) := by
  refine le_of_tendsto (Complex.tendsto_euler_sin_prod u).norm
    (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  rw [← Finset.prod_range_mul_prod_Ico _ hn, ← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_prod_Ico_le hN hn u) (norm_nonneg _)

end Cvs.Upstream.SineEulerFactorsBound
