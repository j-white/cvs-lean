import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The harmonic sums of the weighted Schur test

With weights `1/n` the row sums of the Schur test are the series `Σ 1/(n(n+m))` and the finite sum
`Σ 1/(n(m−n))`; by partial fractions the first telescopes to `H_m/m` and the second reflects to
`2H_{m−1}/m`, both bounded through `H_m ≤ 1 + log m`.
-/

noncomputable section

open Finset Filter Topology

namespace Cvs.Upstream.WeightedSchurHarmonicSums

/-- The harmonic number, as a real sum: `H m = Σ_{k<m} 1/(k+1)`. -/
def H (m : ℕ) : ℝ := ∑ k ∈ range m, 1 / ((k : ℝ) + 1)

theorem H_eq_harmonic (m : ℕ) : H m = ((harmonic m : ℚ) : ℝ) := by
  unfold H harmonic
  push_cast
  simp [one_div]

theorem H_le (m : ℕ) : H m ≤ 1 + Real.log m := by
  rw [H_eq_harmonic]; exact harmonic_le_one_add_log m

theorem H_nonneg (m : ℕ) : 0 ≤ H m := by
  unfold H; positivity

/-- The reciprocals of a block of `m` consecutive integers beyond `N` sum to at most `m/(N+1)`. -/
theorem block_le (m N : ℕ) : ∑ k ∈ range m, 1 / (((N + k : ℕ) : ℝ) + 1) ≤ m / ((N : ℝ) + 1) := by
  calc ∑ k ∈ range m, 1 / (((N + k : ℕ) : ℝ) + 1) ≤ ∑ k ∈ range m, 1 / ((N : ℝ) + 1) := by
        refine Finset.sum_le_sum fun k _ => ?_
        apply one_div_le_one_div_of_le (by positivity)
        push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    _ = m / ((N : ℝ) + 1) := by simp [Finset.sum_const]; ring

/-- **The partial sums of the shifted telescope**: `H m` less a block beyond `N`. -/
theorem sum_telescope (m N : ℕ) :
    ∑ n ∈ range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m))
      = H m - ∑ k ∈ range m, 1 / (((N + k : ℕ) : ℝ) + 1) := by
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ n ∈ range N, 1 / ((n : ℝ) + 1 + m) = ∑ n ∈ range N, 1 / (((m + n : ℕ) : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun n _ => ?_; push_cast; ring_nf
  have h2 := Finset.sum_range_add (fun n : ℕ => 1 / ((n : ℝ) + 1)) m N
  have h3 := Finset.sum_range_add (fun n : ℕ => 1 / ((n : ℝ) + 1)) N m
  rw [add_comm m N] at h2
  unfold H
  rw [h1]
  linarith

/-- **The shifted telescope sums to `H m`.** -/
theorem hasSum_telescope (m : ℕ) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m)) (H m) := by
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + m) := by
    have hb : Summable fun n : ℕ => (m : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) := by
      have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
        (add_left_injective 1)
      refine (this.congr fun n => ?_).mul_left _
      simp [Function.comp]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hb
    · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [div_sub_div _ _ hn.ne' (by positivity), div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [mul_nonneg hm (sq_nonneg ((n : ℝ) + 1)), mul_nonneg hm hm, mul_nonneg (mul_nonneg hm hm) hn.le]
  refine (Summable.hasSum_iff_tendsto_nat hs).mpr ?_
  simp_rw [sum_telescope]
  rw [show (𝓝 (H m)) = 𝓝 (H m - 0) by simp]
  refine tendsto_const_nhds.sub ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    (fun N => Finset.sum_nonneg fun k _ => by positivity) (fun N => block_le m N)

/-- **`Σ_{n≥1} 1/(n(n+m)) = H_m / m`.** -/
theorem hasSum_inv_mul_add {m : ℕ} (hm : 1 ≤ m) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + m))) (H m / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (hasSum_telescope m).div_const (m : ℝ)
  refine h.congr_fun fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp
  ring

end Cvs.Upstream.WeightedSchurHarmonicSums
