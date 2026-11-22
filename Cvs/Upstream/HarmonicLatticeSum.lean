import Mathlib

/-!
# A harmonic-sum bound for reciprocal distances to a lattice

`∑_{1 ≤ m ≤ N, |m − b| ≥ 1} 1/|m − b| ≤ 3(1 + log N)` for `b ≥ 0`: the integers above `b` sit at
distances at least half their offset from `⌊b⌋`, those below at least their offset, and each side
injects into `{1, …, N}`.
-/

noncomputable section

open Finset

namespace Cvs.Upstream.HarmonicLatticeSum

/-- The harmonic number, as a real sum. -/
theorem sum_Icc_inv_le (N : ℕ) : ∑ x ∈ Finset.Icc 1 N, (1 / (x : ℝ)) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- **The reciprocal-distance sum is at most `3(1 + log N)`.** -/
theorem sum_inv_dist_le {b : ℝ} (hb : 0 ≤ b) (N : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|), 1 / |(m : ℝ) - b|
      ≤ 3 * (1 + Real.log N) := by
  set r : ℕ := ⌊b⌋₊ with hr
  have hr1 : (r : ℝ) ≤ b := Nat.floor_le hb
  have hr2 : b < r + 1 := Nat.lt_floor_add_one b
  set S := (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|) with hS
  set Sp := S.filter (fun m : ℕ => b + 1 ≤ (m : ℝ)) with hSp
  set Sm := S.filter (fun m : ℕ => ¬ (b + 1 ≤ (m : ℝ))) with hSm
  have hsplit : ∑ m ∈ S, 1 / |(m : ℝ) - b|
      = ∑ m ∈ Sp, 1 / |(m : ℝ) - b| + ∑ m ∈ Sm, 1 / |(m : ℝ) - b| :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have hH := sum_Icc_inv_le N
  -- the integers above `b`
  have hp : ∑ m ∈ Sp, 1 / |(m : ℝ) - b| ≤ 2 * ∑ x ∈ Finset.Icc 1 N, (1 / (x : ℝ)) := by
    have hmem : ∀ m ∈ Sp, r + 1 ≤ m ∧ m ≤ N ∧ b + 1 ≤ (m : ℝ) := by
      intro m hm
      simp only [hSp, hS, Finset.mem_filter, Finset.mem_Icc] at hm
      refine ⟨?_, hm.1.1.2, hm.2⟩
      have : (r : ℝ) + 1 ≤ m := by linarith [hm.2]
      exact_mod_cast this
    have hle : ∀ m ∈ Sp, 1 / |(m : ℝ) - b| ≤ 2 * (1 / (((m - r : ℕ) : ℕ) : ℝ)) := by
      intro m hm
      obtain ⟨h1, _, h3⟩ := hmem m hm
      have hcast : (((m - r : ℕ) : ℕ) : ℝ) = (m : ℝ) - r := by
        rw [Nat.cast_sub (by omega)]
      rw [hcast, abs_of_nonneg (by linarith)]
      have hpos : (0 : ℝ) < (m : ℝ) - r := by
        have : (r : ℝ) + 1 ≤ m := by exact_mod_cast h1
        linarith
      rw [mul_one_div, div_le_div_iff₀ (by linarith) hpos]
      linarith
    have hinj : Set.InjOn (fun m : ℕ => m - r) ↑Sp := by
      intro m hm m' hm' h
      have := (hmem m hm).1; have := (hmem m' hm').1
      dsimp only at h; omega
    have himg : Sp.image (fun m : ℕ => m - r) ⊆ Finset.Icc 1 N := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h1, h2, _⟩ := hmem m hm
      simp only [Finset.mem_Icc]; omega
    calc ∑ m ∈ Sp, 1 / |(m : ℝ) - b| ≤ ∑ m ∈ Sp, 2 * (1 / (((m - r : ℕ) : ℕ) : ℝ)) :=
          Finset.sum_le_sum hle
      _ = 2 * ∑ x ∈ Sp.image (fun m : ℕ => m - r), (1 / (x : ℝ)) := by
          rw [Finset.mul_sum, Finset.sum_image hinj]
      _ ≤ 2 * ∑ x ∈ Finset.Icc 1 N, (1 / (x : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)) (by norm_num)
  -- the integers below `b`
  have hm : ∑ m ∈ Sm, 1 / |(m : ℝ) - b| ≤ ∑ x ∈ Finset.Icc 1 N, (1 / (x : ℝ)) := by
    set k : ℕ := min r (N + 1) with hk
    have hmem : ∀ m ∈ Sm, 1 ≤ m ∧ m ≤ N ∧ m + 1 ≤ r ∧ (m : ℝ) ≤ b - 1 := by
      intro m hm
      simp only [hSm, hS, Finset.mem_filter, Finset.mem_Icc, not_le] at hm
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm
      have hlt : (m : ℝ) - b < 1 := by linarith
      have hmb : (m : ℝ) ≤ b - 1 := by
        rcases le_or_gt 0 ((m : ℝ) - b) with h | h
        · rw [abs_of_nonneg h] at h3; linarith
        · rw [abs_of_neg h] at h3; linarith
      refine ⟨h1, h2, ?_, hmb⟩
      have : (m : ℝ) + 1 < r + 1 := by linarith
      have : (m : ℝ) < r := by linarith
      have : m < r := by exact_mod_cast this
      omega
    have hle : ∀ m ∈ Sm, 1 / |(m : ℝ) - b| ≤ 1 / (((k - m : ℕ) : ℕ) : ℝ) := by
      intro m hm
      obtain ⟨h1, h2, h3, h4⟩ := hmem m hm
      have hkm : m + 1 ≤ k := le_min h3 (by omega)
      have hcast : (((k - m : ℕ) : ℕ) : ℝ) = (k : ℝ) - m := by rw [Nat.cast_sub (by omega)]
      have hkr : (k : ℝ) ≤ r := by exact_mod_cast (min_le_left r (N + 1))
      rw [hcast, abs_of_neg (by linarith)]
      have hpos : (0 : ℝ) < (k : ℝ) - m := by
        have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hkm
        linarith
      rw [neg_sub]
      exact one_div_le_one_div_of_le hpos (by linarith)
    have hinj : Set.InjOn (fun m : ℕ => k - m) ↑Sm := by
      intro m hm m' hm' h
      obtain ⟨_, h2, h3, _⟩ := hmem m hm
      obtain ⟨_, h2', h3', _⟩ := hmem m' hm'
      have h5 : m + 1 ≤ k := le_min h3 (by omega)
      have h6 : m' + 1 ≤ k := le_min h3' (by omega)
      dsimp only at h; omega
    have himg : Sm.image (fun m : ℕ => k - m) ⊆ Finset.Icc 1 N := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h1, h2, h3, _⟩ := hmem m hm
      have h5 : m + 1 ≤ k := le_min h3 (by omega)
      have h6 : k ≤ N + 1 := min_le_right _ _
      simp only [Finset.mem_Icc]; omega
    calc ∑ m ∈ Sm, 1 / |(m : ℝ) - b| ≤ ∑ m ∈ Sm, 1 / (((k - m : ℕ) : ℕ) : ℝ) :=
          Finset.sum_le_sum hle
      _ = ∑ x ∈ Sm.image (fun m : ℕ => k - m), (1 / (x : ℝ)) := by rw [Finset.sum_image hinj]
      _ ≤ ∑ x ∈ Finset.Icc 1 N, (1 / (x : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
  rw [hsplit]
  linarith

end Cvs.Upstream.HarmonicLatticeSum
