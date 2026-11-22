import Mathlib
import Cvs.L2a.RungSpanFromPlateau

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resonant sum as a single sum over the mode index

With `n = km′`, `(1/k)(1/m′) = 1/n` and `Σ_{k ∣ n} Λ(k) = log n`, so for any gains `γ`,
`Σ_{k≤M} Λ(k)τ_k/k = Σ_{n≤M} (log n/n)(1/γ_n + ε₃)` with `τ_k` the tail fraction of Cvs.L2a.RungSpanFromPlateau: the resonant constant
prices each mode index `n` by its own gain alone, so trivial gains below `k₀` cost `Σ_{n<k₀} log n/(n(1 − δ_n))`.
-/

namespace Cvs.L2a.ResonantSumModeIndex

open Real Finset ArithmeticFunction Cvs.L2a.RungSpanFromPlateau

/-- **The resonant sum by Dirichlet convolution**: `Σ_{k≤M} Λ(k)τ_k/k = Σ_{n≤M} (log n/n)(1/γ_n + ε₃)`. -/
theorem resonant_sum_eq (γ : ℕ → ℝ) (ε₃ : ℝ) (M : ℕ) :
    ∑ k ∈ Icc 1 M, Λ k * tauG γ ε₃ M k / k = ∑ n ∈ Icc 1 M, Real.log n / n * (1 / γ n + ε₃) := by
  set f : ℕ → ℝ := fun n => 1 / γ n + ε₃ with hf
  -- each `k`: reindex `m′ ↦ n = k m′`
  have hk : ∀ k ∈ Icc 1 M, Λ k * tauG γ ε₃ M k / k
      = ∑ n ∈ (Icc 1 M).filter (fun n => k ∣ n), Λ k / n * f n := fun k hkm => by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkm).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    unfold tauG
    rw [mul_sum, sum_div]
    refine Finset.sum_nbij' (fun m' => k * m') (fun n => n / k) ?_ ?_ ?_ ?_ ?_
    · intro m' hm'
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm' ⊢
      refine ⟨⟨?_, hm'.2⟩, dvd_mul_right k m'⟩
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨hn1, hnM⟩, ⟨q, rfl⟩⟩ := hn
      have hq : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · subst h; simp at hn1
        · exact h
      rw [Nat.mul_div_cancel_left q (by omega)]
      exact ⟨⟨hq, le_trans (Nat.le_mul_of_pos_left q (by omega)) hnM⟩, hnM⟩
    · intro m' _
      exact Nat.mul_div_cancel_left m' (by omega)
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m' _
      simp only [hf]
      push_cast
      have : (0 : ℝ) < m' ∨ (m' : ℝ) = 0 := by
        rcases Nat.eq_zero_or_pos m' with h | h
        · right; simp [h]
        · left; exact_mod_cast h
      rcases this with hm | hm
      · field_simp
      · simp [hm]
  rw [sum_congr rfl hk]
  -- swap to a sum over `n` and its divisors
  rw [Finset.sum_comm' (t' := Icc 1 M) (s' := fun n => n.divisors)]
  · apply sum_congr rfl; intro n _
    rw [← sum_mul, ← sum_div, vonMangoldt_sum]
  · intro k n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hk1, hkM⟩, ⟨hn1, hnM⟩, hkn⟩
      exact ⟨⟨hkn, by omega⟩, hn1, hnM⟩
    · rintro ⟨⟨hkn, hn0⟩, hn1, hnM⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hkn (by omega), (Nat.le_of_dvd (by omega) hkn).trans hnM⟩, ⟨hn1, hnM⟩, hkn⟩

end Cvs.L2a.ResonantSumModeIndex
