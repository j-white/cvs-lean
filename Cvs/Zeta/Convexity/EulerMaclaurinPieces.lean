import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The pieces of the Euler–Maclaurin identity
-/

open Complex MeasureTheory Set Filter

namespace Cvs.ZetaGrowth

/-- `∫_c^∞ x^{-s-1} dx = c^{-s}/s` for `σ > 0`, `c > 0`. -/
theorem integral_Ioi_cpow_neg {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi c, (x : ℂ) ^ (-s - 1)) = (c : ℂ) ^ (-s) / s := by
  have hre : (-s - 1).re < -1 := by simp; linarith
  rw [integral_Ioi_cpow_of_lt hre hc]
  have hsne : s ≠ 0 := by
    intro hc0; rw [hc0] at hs; simp at hs
  have h1 : (-s - 1) + 1 = -s := by ring
  rw [h1]
  field_simp

/-- The indicator form of the floor: `⌊x⌋ = ∑_{n : ℕ} [n+1 ≤ x]`, as a sum with finitely many
nonzero terms. -/
theorem tsum_indicator_eq_floor {x : ℝ} (hx : 0 ≤ x) (c : ℂ) :
    (∑' n : ℕ, if ((n : ℝ) + 1) ≤ x then c else 0) = (⌊x⌋ : ℂ) * c := by
  have hsupp : ∀ n ∉ Finset.range ⌊x⌋₊, (if ((n : ℝ) + 1) ≤ x then c else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hge : ⌊x⌋₊ ≤ n := by omega
    have : ¬ ((n : ℝ) + 1 ≤ x) := by
      intro hle
      have : n + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    simp [this]
  rw [tsum_eq_sum hsupp]
  have hmem : ∀ n ∈ Finset.range ⌊x⌋₊, (if ((n : ℝ) + 1) ≤ x then c else 0) = c := by
    intro n hn
    rw [Finset.mem_range] at hn
    have : ((n : ℝ) + 1) ≤ x := by
      have h1 : (n : ℝ) + 1 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
      exact le_trans h1 (Nat.floor_le hx)
    simp [this]
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  have := Int.natCast_floor_eq_floor hx
  exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this

/-- **The `n`-th indicator term integrates to `(n+1)^{-s}/s`.**  On `(1,∞)` the constraint
`n+1 ≤ x` cuts the domain down to `(n+1,∞)` up to a single point, which the measure does not
see. -/
theorem integral_indicator_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ x in Ioi (1 : ℝ), (if ((n : ℝ) + 1) ≤ x then (x : ℂ) ^ (-s - 1) else 0))
      = ((n : ℂ) + 1) ^ (-s) / s := by
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hapos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hind : ∀ x : ℝ, (if ((n : ℝ) + 1) ≤ x then (x : ℂ) ^ (-s - 1) else 0)
      = Set.indicator (Ici ((n : ℝ) + 1)) (fun y : ℝ => (y : ℂ) ^ (-s - 1)) x := by
    intro x
    by_cases hx : ((n : ℝ) + 1) ≤ x
    · rw [if_pos hx, Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (by simpa using hx)]
  simp_rw [hind]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hset : Ioi (1 : ℝ) ∩ Ici (((0 : ℕ) : ℝ) + 1) = Ioi (1 : ℝ) := by
      rw [Set.inter_eq_left]
      simpa using Set.Ioi_subset_Ici_self
    rw [hset, integral_Ioi_cpow_neg hs one_pos]
    norm_num
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1a : (1 : ℝ) < (n : ℝ) + 1 := by linarith
    have hset : Ioi (1 : ℝ) ∩ Ici ((n : ℝ) + 1) = Ici ((n : ℝ) + 1) := by
      rw [Set.inter_eq_right]
      intro x hx
      exact lt_of_lt_of_le h1a hx
    rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi,
      integral_Ioi_cpow_neg hs hapos]
    push_cast
    ring

end Cvs.ZetaGrowth
