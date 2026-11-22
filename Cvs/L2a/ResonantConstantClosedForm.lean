import Mathlib
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.ResonantSumModeIndex
import Cvs.L2a.RungSpanFromPlateau

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resonant constant in closed form from trivial and plateau gains

Since `log n ≤ H_n`, a plateau gain `γ_n ≥ gH_n` prices the index `n` at most `1/(gn)`; with the trivial gain
`γ_n ≥ 1 − δ` below `k₀`, `ResonantSumModeIndex`'s sum is at most
`(1/(1 − δ))Σ_{n<k₀} log n/n + (1/g)Σ_{k₀≤n≤M} 1/n + ε₃Σ_{n≤M} log n/n`.
-/

namespace Cvs.L2a.ResonantConstantClosedForm

open Real Finset ArithmeticFunction Cvs.L2a.FarMassPlateau Cvs.L2a.RungSpanFromPlateau Cvs.L2a.ResonantSumModeIndex

/-- `log n ≤ H_n`. -/
theorem log_le_harm (n : ℕ) : Real.log n ≤ harm n := by
  have h1 := log_add_one_le_harmonic n
  have h2 : ((harmonic n : ℚ) : ℝ) = harm n := by
    rw [harmonic_eq_sum_Icc, harm]; push_cast; simp [one_div]
  rw [← h2]
  refine le_trans ?_ h1
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_le_log (by exact_mod_cast h) (by push_cast; linarith)

/-- **The resonant constant in closed form.** -/
theorem resonant_le {γ : ℕ → ℝ} {δ g ε₃ : ℝ} {M k₀ : ℕ} (hδ : δ < 1) (hg : 0 < g)
    (hlow : ∀ n ∈ Icc 1 M, n < k₀ → 1 - δ ≤ γ n) (hhigh : ∀ n ∈ Icc 1 M, k₀ ≤ n → g * harm n ≤ γ n) :
    ∑ k ∈ Icc 1 M, Λ k * tauG γ ε₃ M k / k
      ≤ (1 / (1 - δ)) * ∑ n ∈ (Icc 1 M).filter (· < k₀), Real.log n / n
        + (1 / g) * ∑ n ∈ (Icc 1 M).filter (k₀ ≤ ·), 1 / (n : ℝ)
        + ε₃ * ∑ n ∈ Icc 1 M, Real.log n / n := by
  rw [resonant_sum_eq]
  have hpt : ∀ n ∈ Icc 1 M, Real.log n / n * (1 / γ n + ε₃)
      ≤ (if n < k₀ then (1 / (1 - δ)) * (Real.log n / n) else (1 / g) * (1 / (n : ℝ)))
        + ε₃ * (Real.log n / n) := fun n hn => by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hq0 : 0 ≤ Real.log n / n := div_nonneg hl0 hn0.le
    rw [mul_add]
    refine add_le_add ?_ (by rw [mul_comm])
    split_ifs with hk
    · have hγ := hlow n hn hk
      have hd : 0 < 1 - δ := by linarith
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hd hγ) hq0
    · have hH : 0 < harm n := by
        unfold harm
        exact Finset.sum_pos (fun m hm => by
          have : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
          positivity) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩⟩
      have hγ := hhigh n hn (not_lt.mp hk)
      have hγ0 : 0 < γ n := lt_of_lt_of_le (mul_pos hg hH) hγ
      have hlh := log_le_harm n
      calc Real.log n / n * (1 / γ n) ≤ harm n / n * (1 / (g * harm n)) := by
            apply mul_le_mul (div_le_div_of_nonneg_right hlh hn0.le)
              (one_div_le_one_div_of_le (mul_pos hg hH) hγ) (by positivity) (by positivity)
        _ = 1 / g * (1 / n) := by field_simp
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_ite]
  simp only [not_lt, Finset.mul_sum]

end Cvs.L2a.ResonantConstantClosedForm
