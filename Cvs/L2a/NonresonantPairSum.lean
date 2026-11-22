import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NearResonantPairHarmonic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The non-resonant pair sum `Σ_{j ≠ n} 1/(j |n − j|) ≤ 3H_n/n`

Each non-stationary prime pair `(m, m′)` at shift `k` is at most `4 G_M √κ/(c² m m′ |km − m′|)`, since
`(1/m + 1/r)/|m² − r²| = 1/(m r |m − r|)`; summing over `m′` needs `Σ_{j ≠ n} 1/(j|n − j|)`, which by partial fractions
is `(2H_{n−1} + H_n)/n ≤ 3H_n/n`, for every truncation.
-/

namespace Cvs.L2a.NonresonantPairSum

open Finset Real Cvs.L2a.NearResonantPairHarmonic

/-- **The tail above `n`**: `Σ_{i<L} 1/((i+1+n)(i+1)) ≤ H_n/n`. -/
theorem tail_le' (n L : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range L, 1 / (((i : ℝ) + 1 + n) * ((i : ℝ) + 1)) ≤ H n / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ i ∈ range L, 1 / (((i : ℝ) + 1 + n) * ((i : ℝ) + 1))
      = (1 / n) * ((fun k : ℕ => 1 / ((k : ℝ) + 1)) i - (fun k : ℕ => 1 / ((k : ℝ) + 1)) (i + n)) := by
    intro i _; push_cast; field_simp; ring
  rw [sum_congr rfl e, ← mul_sum, sum_range_sub_shift]
  have hpos : 0 ≤ ∑ i ∈ range n, (fun k : ℕ => 1 / ((k : ℝ) + 1)) (i + L) :=
    sum_nonneg fun i _ => by positivity
  have : ∑ i ∈ range n, (fun k : ℕ => 1 / ((k : ℝ) + 1)) i = H n := rfl
  rw [this]
  have hd : 0 ≤ (∑ i ∈ range n, (fun k : ℕ => 1 / ((k : ℝ) + 1)) (i + L)) / n := div_nonneg hpos hn'.le
  have e2 : 1 / (n : ℝ) * (H n - ∑ i ∈ range n, (fun k : ℕ => 1 / ((k : ℝ) + 1)) (i + L))
      = H n / n - (∑ i ∈ range n, (fun k : ℕ => 1 / ((k : ℝ) + 1)) (i + L)) / n := by ring
  linarith [e2]

/-- **The head below `n`**: `Σ_{1 ≤ j < n} 1/(j(n−j)) ≤ 2H_n/n`. -/
theorem head_le' (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, 1 / ((j : ℝ) * ((n : ℝ) - j)) ≤ 2 * H n / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ j ∈ Ico 1 n, 1 / ((j : ℝ) * ((n : ℝ) - j)) = (1 / n) * (1 / (j : ℝ) + 1 / ((n : ℝ) - j)) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Ico.mp hj).1
    have hj' : (j : ℝ) < n := by exact_mod_cast (mem_Ico.mp hj).2
    have : (n : ℝ) - j ≠ 0 := by linarith
    have : (j : ℝ) ≠ 0 := by linarith
    field_simp; ring
  rw [sum_congr rfl e, ← mul_sum, sum_add_distrib]
  have h2 : ∑ j ∈ Ico 1 n, 1 / ((n : ℝ) - j) = ∑ i ∈ Ico 1 n, 1 / (i : ℝ) := by
    apply sum_nbij' (fun j => n - j) (fun i => n - i)
    · intro j hj; simp only [mem_Ico] at hj ⊢; omega
    · intro i hi; simp only [mem_Ico] at hi ⊢; omega
    · intro j hj; simp only [mem_Ico] at hj; omega
    · intro i hi; simp only [mem_Ico] at hi; omega
    · intro j hj; simp only [mem_Ico] at hj; push_cast [Nat.cast_sub hj.2.le]; ring
  rw [h2]
  have hH : ∑ i ∈ Ico 1 n, 1 / (i : ℝ) ≤ H n := by
    unfold H
    calc ∑ i ∈ Ico 1 n, 1 / (i : ℝ) ≤ ∑ i ∈ Ico 1 (n + 1), 1 / (i : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
          intro i _ _; positivity
      _ = ∑ i ∈ range n, 1 / ((i : ℝ) + 1) := by
          rw [sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
          apply sum_congr rfl; intro i _; push_cast; ring
  calc 1 / (n : ℝ) * (∑ i ∈ Ico 1 n, 1 / (i : ℝ) + ∑ i ∈ Ico 1 n, 1 / (i : ℝ))
      ≤ 1 / (n : ℝ) * (H n + H n) := mul_le_mul_of_nonneg_left (add_le_add hH hH) (by positivity)
    _ = 2 * H n / n := by ring

/-- **The non-resonant sum**: for `1 ≤ n`, `Σ_{j ∈ [1, M], j ≠ n} 1/(j|n − j|) ≤ 3(1 + log n)/n`. -/
theorem nonresonant_le (n M : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (Icc 1 M).erase n, 1 / ((j : ℝ) * |(n : ℝ) - j|) ≤ 3 * (1 + log n) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set S := (Icc 1 M).erase n
  have hsplit := sum_filter_add_sum_filter_not S (fun j => j < n) (fun j => 1 / ((j : ℝ) * |(n : ℝ) - j|))
  have hlow : ∑ j ∈ S.filter (fun j => j < n), 1 / ((j : ℝ) * |(n : ℝ) - j|) ≤ 2 * H n / n := by
    calc ∑ j ∈ S.filter (fun j => j < n), 1 / ((j : ℝ) * |(n : ℝ) - j|)
        = ∑ j ∈ S.filter (fun j => j < n), 1 / ((j : ℝ) * ((n : ℝ) - j)) := by
          apply sum_congr rfl; intro j hj
          simp only [S, mem_filter, mem_erase, mem_Icc] at hj
          have : (j : ℝ) < n := by exact_mod_cast hj.2
          rw [abs_of_pos (by linarith)]
      _ ≤ ∑ j ∈ Ico 1 n, 1 / ((j : ℝ) * ((n : ℝ) - j)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro j hj; simp only [S, mem_filter, mem_erase, mem_Icc] at hj; simp only [mem_Ico]; omega
          · intro j hj _
            have : (j : ℝ) < n := by exact_mod_cast (mem_Ico.mp hj).2
            have : (0 : ℝ) ≤ j := by positivity
            apply div_nonneg zero_le_one; apply mul_nonneg <;> linarith
      _ ≤ 2 * H n / n := head_le' n hn
  set g : ℕ → ℝ := fun i => 1 / (((i : ℝ) + 1 + n) * ((i : ℝ) + 1))
  have hhigh : ∑ j ∈ S.filter (fun j => ¬ j < n), 1 / ((j : ℝ) * |(n : ℝ) - j|) ≤ H n / n := by
    have hinj : ∀ a ∈ S.filter (fun j => ¬ j < n), ∀ b ∈ S.filter (fun j => ¬ j < n),
        a - n - 1 = b - n - 1 → a = b := by
      intro a ha b hb hab
      simp only [S, mem_filter, mem_erase, mem_Icc] at ha hb; omega
    calc ∑ j ∈ S.filter (fun j => ¬ j < n), 1 / ((j : ℝ) * |(n : ℝ) - j|)
        = ∑ j ∈ S.filter (fun j => ¬ j < n), g (j - n - 1) := by
          apply sum_congr rfl; intro j hj
          simp only [S, mem_filter, mem_erase, mem_Icc] at hj
          have hjn : n + 1 ≤ j := by omega
          have e : ((j - n - 1 : ℕ) : ℝ) = (j : ℝ) - n - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          simp only [g, e]
          have hj' : (n : ℝ) + 1 ≤ j := by exact_mod_cast hjn
          rw [abs_of_neg (by linarith)]
          congr 1; ring
      _ = ∑ i ∈ (S.filter (fun j => ¬ j < n)).image (fun j => j - n - 1), g i := (sum_image hinj).symm
      _ ≤ ∑ i ∈ range (M - n), g i := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro i hi; rw [mem_image] at hi; obtain ⟨j, hj, rfl⟩ := hi
            simp only [S, mem_filter, mem_erase, mem_Icc] at hj; simp only [mem_range]; omega
          · intro i _ _; simp only [g]; positivity
      _ ≤ H n / n := tail_le' n (M - n) hn
  have hH := H_le n
  rw [← hsplit]
  calc _ ≤ 2 * H n / n + H n / n := add_le_add hlow hhigh
    _ = 3 * H n / n := by ring
    _ ≤ 3 * (1 + log n) / n := by
        apply div_le_div_of_nonneg_right _ hn'.le; linarith

end Cvs.L2a.NonresonantPairSum
