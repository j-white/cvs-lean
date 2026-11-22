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
# The geometric remainders of the closed-form entries

After `K` terms, each remainder series of `Cvs.Finite.WindowMatrixClosedForm.gen` and `Cvs.Finite.WindowMatrixClosedForm.diag` is bounded by
`tailFactor L K` times an explicit factor, with ratio `e^{−2L}`.
-/

namespace Cvs.Finite.ClosedFormEntryRemainders

open Real
open Cvs.Finite.DiagonalLevySymbol (cutTerm tailFactor)
open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf (imTerm)

theorem tailFactor_add (L : ℝ) (k K : ℕ) :
    tailFactor L (k + K) = tailFactor L K * Real.exp (-(2 * L)) ^ k := by
  unfold tailFactor
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem tailFactor_nonneg (L : ℝ) (k : ℕ) : 0 ≤ tailFactor L k := (Real.exp_pos _).le

theorem ratio_lt_one {L : ℝ} (hL : 0 < L) : Real.exp (-(2 * L)) < 1 := by
  calc Real.exp (-(2 * L)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem abs_imTerm_le (ω : ℝ) (k : ℕ) : |imTerm ω k| ≤ 1 / (2 * (1 / 4 + (k : ℝ))) := by
  unfold imTerm
  set a : ℝ := 1 / 4 + (k : ℝ) with ha
  set b : ℝ := ω / 2
  have ha0 : 0 < a := by rw [ha]; positivity
  have hden : 0 < a ^ 2 + b ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  nlinarith [sq_nonneg (a - |b|), abs_nonneg b, sq_abs b]

/-- The common tail estimate: `|f k| ≤ C r^k` with `r = e^{−2L}` gives `|Σ f| ≤ C/(1 − r)`. -/
theorem abs_tsum_le_of_geometric {L : ℝ} (hL : 0 < L) {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C * Real.exp (-(2 * L)) ^ k) :
    |∑' k, f k| ≤ C / (1 - Real.exp (-(2 * L))) := by
  have hr0 : 0 ≤ Real.exp (-(2 * L)) := (Real.exp_pos _).le
  have hr1 := ratio_lt_one hL
  have hg : Summable fun k : ℕ => C * Real.exp (-(2 * L)) ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hsf : Summable fun k => |f k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hf hg
  calc |∑' k, f k| ≤ ∑' k, |f k| := by
        have := norm_tsum_le_tsum_norm (f := f) (by simpa [Real.norm_eq_abs] using hsf)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' k, C * Real.exp (-(2 * L)) ^ k := hsf.tsum_le_tsum hf hg
    _ = C / (1 - Real.exp (-(2 * L))) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- **Remainder of the digamma series** after `K` terms. -/
theorem abs_tsum_tail_imTerm_le {L : ℝ} (hL : 0 < L) (ω : ℝ) (K : ℕ) :
    |∑' k, tailFactor L (k + K) * imTerm ω (k + K)|
      ≤ tailFactor L K / (2 * (1 / 4 + (K : ℝ))) / (1 - Real.exp (-(2 * L))) := by
  have hK : (0 : ℝ) < 1 / 4 + (K : ℝ) := by positivity
  refine abs_tsum_le_of_geometric hL fun k => ?_
  rw [abs_mul, abs_of_nonneg (tailFactor_nonneg L _), tailFactor_add]
  have h1 := abs_imTerm_le ω (k + K)
  have h2 : 1 / (2 * (1 / 4 + ((k + K : ℕ) : ℝ))) ≤ 1 / (2 * (1 / 4 + (K : ℝ))) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h3 : 0 ≤ tailFactor L K * Real.exp (-(2 * L)) ^ k :=
    mul_nonneg (tailFactor_nonneg L K) (pow_nonneg (Real.exp_pos _).le k)
  calc tailFactor L K * Real.exp (-(2 * L)) ^ k * |imTerm ω (k + K)|
      ≤ tailFactor L K * Real.exp (-(2 * L)) ^ k * (1 / (2 * (1 / 4 + (K : ℝ)))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = tailFactor L K / (2 * (1 / 4 + (K : ℝ))) * Real.exp (-(2 * L)) ^ k := by ring

end Cvs.Finite.ClosedFormEntryRemainders
