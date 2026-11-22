import Mathlib
import Cvs.Finite.DiagonalLevySymbol
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail-weighted sums, trapped by explicit terms

The tail factor is `exp(−L/2)` times a geometric factor, so a tail-weighted sum of any bounded
sequence is within the bound times the geometric remainder of its first `K` terms; the cut term is
bounded by `1/b²` and the imaginary-half terms by `1/b`, which traps both tail sums of the
diagonal and the off-diagonal entries to explicit width.
-/

noncomputable section

open Real Finset

namespace Cvs.WeilForm.Archimedean.TailWeightedSums

open Cvs.Finite.DiagonalLevySymbol Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

theorem tailFactor_eq (L : ℝ) (k : ℕ) :
    tailFactor L k = Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ k := by
  unfold tailFactor
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring

theorem tailFactor_pos (L : ℝ) (k : ℕ) : 0 < tailFactor L k := Real.exp_pos _

/-- **A tail-weighted sum of a bounded sequence is summable.** -/
theorem summable_tailFactor_mul {L : ℝ} (hL : 0 < L) {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C) :
    Summable fun k => tailFactor L k * f k := by
  have hr : Real.exp (-(2 * L)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_norm_bounded
    (((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (Real.exp (-(L / 2)))).mul_right C)
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (tailFactor_pos L k), tailFactor_eq]
  exact mul_le_mul_of_nonneg_left (hC k) (by positivity)

/-- **The tail-weighted sum is within the bound times the geometric remainder of its first `K`
terms.** -/
theorem abs_tsum_tailFactor_sub_le {L : ℝ} (hL : 0 < L) {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C)
    (K : ℕ) :
    |∑' k, tailFactor L k * f k - ∑ k ∈ range K, tailFactor L k * f k|
      ≤ C * (Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ K / (1 - Real.exp (-(2 * L)))) := by
  have hr : Real.exp (-(2 * L)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 ≤ Real.exp (-(2 * L)) := (Real.exp_pos _).le
  have hs := summable_tailFactor_mul hL hC
  have hsplit := hs.sum_add_tsum_nat_add K
  rw [← hsplit, add_sub_cancel_left]
  have hs' : Summable fun k => tailFactor L (k + K) * f (k + K) := (summable_nat_add_iff K).mpr hs
  have hterm : ∀ k, |tailFactor L (k + K) * f (k + K)|
      ≤ C * Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ K * Real.exp (-(2 * L)) ^ k := by
    intro k
    rw [abs_mul, abs_of_pos (tailFactor_pos L _), tailFactor_eq, pow_add]
    have := hC (k + K)
    have hE : 0 ≤ Real.exp (-(L / 2)) * (Real.exp (-(2 * L)) ^ k * Real.exp (-(2 * L)) ^ K) := by
      positivity
    calc Real.exp (-(L / 2)) * (Real.exp (-(2 * L)) ^ k * Real.exp (-(2 * L)) ^ K) * |f (k + K)|
        ≤ Real.exp (-(L / 2)) * (Real.exp (-(2 * L)) ^ k * Real.exp (-(2 * L)) ^ K) * C :=
          mul_le_mul_of_nonneg_left this hE
      _ = C * Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ K * Real.exp (-(2 * L)) ^ k := by ring
  have hg : Summable fun k : ℕ =>
      C * Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ K * Real.exp (-(2 * L)) ^ k :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hn := norm_tsum_le_tsum_norm hs'.norm
  simp only [Real.norm_eq_abs] at hn
  calc |∑' k, tailFactor L (k + K) * f (k + K)|
      ≤ ∑' k, |tailFactor L (k + K) * f (k + K)| := hn
    _ ≤ ∑' k, C * Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ K * Real.exp (-(2 * L)) ^ k :=
        hs'.abs.tsum_le_tsum hterm hg
    _ = C * (Real.exp (-(L / 2)) * Real.exp (-(2 * L)) ^ K / (1 - Real.exp (-(2 * L)))) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
        field_simp

/-! ### The two instances -/

/-- The imaginary-half term at `t ≠ 0` is bounded by `2/|t|`. -/
theorem abs_imTerm_le {t : ℝ} (ht : t ≠ 0) (k : ℕ) : |imTerm t k| ≤ 2 / |t| := by
  unfold imTerm
  have hy : (t / 2) ^ 2 > 0 := by positivity
  have hD : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD (abs_pos.mpr ht)]
  have h1 : |t / 2| * |t| = (t / 2) ^ 2 * 2 := by
    rw [abs_div, abs_two]
    have := sq_abs t
    nlinarith [this]
  rw [h1]
  nlinarith [sq_nonneg (1 / 4 + (k : ℝ))]

end Cvs.WeilForm.Archimedean.TailWeightedSums
