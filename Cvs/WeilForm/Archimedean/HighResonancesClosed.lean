import Mathlib
import Cvs.WeilForm.Archimedean.ArchWeightFilterBank
import Cvs.Zeta.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The high resonances are closed where the fringe lives

`ArchWeightFilterBank` identifies the `k`-th term of the archimedean weight as a high-pass filter of cutoff
`2aₖ = 2k + ½`.
-/

namespace Cvs.Transform

open Cvs.Transform

/-- The `k`-th filter of the bank, gain `1/aₖ` and cutoff `2aₖ`. -/
noncomputable def bankTerm (k : ℕ) (u : ℝ) : ℝ :=
  (1 / (1 / 4 + (k : ℝ))) * highpass (cutoff k) u

/-- Each term is `Cvs.Zeta`'s digamma deficit — termwise, with no series. -/
theorem bankTerm_eq_deficit (k : ℕ) (u : ℝ) :
    bankTerm k u = Cvs.Zeta.digammaDeficit u k :=
  (deficit_eq_highpass u k).symm

theorem bankTerm_nonneg (k : ℕ) (u : ℝ) : 0 ≤ bankTerm k u := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  exact mul_nonneg (by positivity) (highpass_nonneg _ _)

/-- **A filter of cutoff `c` transmits at most `u²/c²`.**  Below cutoff this is
small; it is the quantitative form of "the filter is closed". -/
theorem highpass_le_sq_div {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    highpass c u ≤ u ^ 2 / c ^ 2 := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  rw [highpass]
  gcongr
  linarith [sq_nonneg u]

/-- Hence the `k`-th term is `O(u²)` with a cubically decaying constant. -/
theorem bankTerm_le (k : ℕ) (u : ℝ) :
    bankTerm k u ≤ u ^ 2 / (4 * (1 / 4 + (k : ℝ)) ^ 3) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  have hc : cutoff k ≠ 0 := (cutoff_pos k).ne'
  have h := highpass_le_sq_div hc u
  calc bankTerm k u ≤ (1 / (1 / 4 + (k : ℝ))) * (u ^ 2 / cutoff k ^ 2) := by
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = u ^ 2 / (4 * (1 / 4 + (k : ℝ)) ^ 3) := by
        rw [cutoff]; field_simp; ring

/-- The majorant is dominated by `16/(k+1)³`, because `4aₖ = 1 + 4k ≥ 1 + k`. -/
theorem majorant_le (k : ℕ) :
    1 / (4 * (1 / 4 + (k : ℝ)) ^ 3) ≤ 16 / ((k : ℝ) + 1) ^ 3 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((k : ℝ)), pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ (k:ℝ) + 1)
    (by linarith : (k : ℝ) + 1 ≤ 4 * (1 / 4 + (k : ℝ))) 3]

theorem summable_majorant :
    Summable (fun k : ℕ => 1 / (4 * (1 / 4 + (k : ℝ)) ^ 3)) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
    have h := (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
    refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun k => by positivity) majorant_le ?_
  exact (hbase.mul_left 16).congr fun n => by rw [mul_one_div]

/-- **The bank converges at every frequency.**  The terms fall like `k^{-3}`
for fixed `u`, even though `Σ 1/aₖ` — the `u → ∞` limit of the terms —
diverges, which is what produces the weight's `½ log u` growth. -/
theorem summable_bankTerm (u : ℝ) : Summable (fun k : ℕ => bankTerm k u) :=
  Summable.of_nonneg_of_le (fun k => bankTerm_nonneg k u) (fun k => bankTerm_le k u)
    (by simpa [div_eq_mul_inv, mul_comm] using summable_majorant.mul_left (u ^ 2))

/-- **The bank is `O(u²)` at low frequency**, with an explicit convergent
constant.  Almost all of that constant is the `k = 0` term — the resonance that
`ArchWeightFilterBank` identifies with the envelope's own pole. -/
theorem tsum_bankTerm_le (u : ℝ) :
    ∑' k : ℕ, bankTerm k u ≤ u ^ 2 * ∑' k : ℕ, 1 / (4 * (1 / 4 + (k : ℝ)) ^ 3) := by
  have hsum : Summable (fun k : ℕ => u ^ 2 * (1 / (4 * (1 / 4 + (k : ℝ)) ^ 3))) :=
    summable_majorant.mul_left _
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_bankTerm u) hsum
  simpa [div_eq_mul_inv] using bankTerm_le k u

end Cvs.Transform
