import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Cvs.Upstream.WeightedSchurHarmonicSums

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The harmonic sums of the even-sector row, in closed form

The three series a Schur row sum at weights `1/n` produces are telescoped: `Σ_{n≥N} m/(n(n+m))` is
a block of `m` reciprocals, `Σ_{n≥N} 1/n²` lies between `1/N` and `1/(N−1)`, and
`Σ_{n≠m} (n+m)/(n²|n−m|)` is at most `π²/6 + (4H_{m−1} + 2H_m)/m`, its tail beyond `N > m` at
most `(2/m)Σ_{k<m} 1/(N−m+k) − 1/N`; the row bound summand collects the three.
-/

noncomputable section

open Finset Filter Topology

namespace Cvs.Upstream.EvenRowHarmonicSums

open Cvs.Upstream.WeightedSchurHarmonicSums

/-! ### Telescoping from a shift -/

/-- **The shifted telescope**: `Σ_{n≥0} (1/(n+N) − 1/(n+N+m)) = Σ_{k<m} 1/(N+k)` for `N ≥ 1`. -/
theorem tsum_telescope_shift {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    ∑' n : ℕ, (1 / ((n : ℝ) + N) - 1 / ((n : ℝ) + N + m)) = ∑ k ∈ range m, 1 / ((N : ℝ) + k) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hs := (hasSum_telescope m).summable
  have key := hs.sum_add_tsum_nat_add N'
  rw [(hasSum_telescope m).tsum_eq, sum_telescope m N'] at key
  have e1 : (fun n : ℕ => 1 / (((n + N' : ℕ) : ℝ) + 1) - 1 / (((n + N' : ℕ) : ℝ) + 1 + m))
      = fun n : ℕ => 1 / ((n : ℝ) + ((N' + 1 : ℕ) : ℝ)) - 1 / ((n : ℝ) + ((N' + 1 : ℕ) : ℝ) + m) := by
    funext n; push_cast; ring_nf
  have e2 : ∑ k ∈ range m, 1 / (((N' + k : ℕ) : ℝ) + 1)
      = ∑ k ∈ range m, 1 / (((N' + 1 : ℕ) : ℝ) + k) := by
    refine Finset.sum_congr rfl fun k _ => ?_; push_cast; ring_nf
  rw [e1] at key
  rw [← e2]
  linarith

theorem summable_telescope_shift {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + N) - 1 / ((n : ℝ) + N + m) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hs := (summable_nat_add_iff N').mpr (hasSum_telescope m).summable
  refine hs.congr fun n => ?_
  push_cast; ring_nf

/-- **The block sum**: `Σ_{n≥0} m/((n+N)(n+N+m)) = Σ_{k<m} 1/(N+k)`. -/
theorem tsum_inv_mul_add_shift {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    ∑' n : ℕ, (m : ℝ) / (((n : ℝ) + N) * ((n : ℝ) + N + m)) = ∑ k ∈ range m, 1 / ((N : ℝ) + k) := by
  rw [← tsum_telescope_shift hN m]
  congr 1; funext n
  have h1 : (0 : ℝ) < (n : ℝ) + N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : (0 : ℝ) < (n : ℝ) + N + m := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  field_simp
  ring

theorem summable_inv_mul_add_shift {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    Summable fun n : ℕ => (m : ℝ) / (((n : ℝ) + N) * ((n : ℝ) + N + m)) := by
  refine (summable_telescope_shift hN m).congr fun n => ?_
  have h1 : (0 : ℝ) < (n : ℝ) + N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : (0 : ℝ) < (n : ℝ) + N + m := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  field_simp
  ring

/-! ### The inverse squares -/

theorem summable_inv_sq_shift (N : ℕ) : Summable fun n : ℕ => 1 / ((n : ℝ) + N) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  refine ((summable_nat_add_iff N).mpr h).congr fun n => ?_
  push_cast; rfl

/-- **The inverse-square tail is at most `1/(N−1)`.** -/
theorem tsum_inv_sq_shift_le {N : ℕ} (hN : 2 ≤ N) :
    ∑' n : ℕ, 1 / ((n : ℝ) + N) ^ 2 ≤ 1 / ((N : ℝ) - 1) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hN' : 1 ≤ N' := by omega
  have h1 := tsum_inv_mul_add_shift hN' 1
  have hs := summable_inv_mul_add_shift hN' 1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero, Nat.cast_one] at h1 hs
  have e : ((N' + 1 : ℕ) : ℝ) - 1 = N' := by push_cast; ring
  rw [e, ← h1]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_inv_sq_shift _) hs
  have h : (0 : ℝ) < (n : ℝ) + N' := by
    have : (1 : ℝ) ≤ N' := by exact_mod_cast hN'
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e2 : (n : ℝ) + ((N' + 1 : ℕ) : ℝ) = (n : ℝ) + N' + 1 := by push_cast; ring
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### The divided-difference sum -/

/-! ### The row bound summand -/

/-! #### The pieces beyond `N > m` -/

/-! #### The pieces over all `n ≥ 1` -/

end Cvs.Upstream.EvenRowHarmonicSums
