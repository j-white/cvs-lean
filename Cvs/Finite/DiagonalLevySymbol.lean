import Mathlib
import Cvs.Finite.BracketMomentsClosed
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyExpMoments
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The diagonal Lévy channel is the symbol at the mode's frequency

The first piece of each diagonal moment is twice the digamma deficit at `t = 2πm/L`, whose series
is the symbol's increment from the origin; so the Lévy pairing of a mode with itself is twice
`archSymbol (2πm/L) − archSymbol 0` plus two cut sums, and on a window no longer than `log 2` the
diagonal pair value is the pole channel plus twice the symbol at the mode's own frequency plus them.
-/

noncomputable section

open Real

namespace Cvs.Finite.DiagonalLevySymbol

/-- The cut term: `(a² − b²)/(a² + b²)²` at the pole `a = k + 1/4` and frequency `b = πm/L`. -/
def cutTerm (L : ℝ) (m : ℤ) (k : ℕ) : ℝ :=
  ((1 / 4 + (k : ℝ)) ^ 2 - (π * m / L) ^ 2) / ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) ^ 2

/-- The tail factor `exp(−(k + 1/4)·2L)`. -/
def tailFactor (L : ℝ) (k : ℕ) : ℝ := Real.exp (-((1 / 4 + (k : ℝ)) * (2 * L)))

theorem abs_cutTerm_le (L : ℝ) (m : ℤ) (k : ℕ) : |cutTerm L m k| ≤ 1 / (1 / 4 + (k : ℝ)) ^ 2 := by
  unfold cutTerm
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ (π * m / L) ^ 2 := by positivity
  have hD : (0 : ℝ) < ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD (by positivity)]
  have h1 : |(1 / 4 + (k : ℝ)) ^ 2 - (π * m / L) ^ 2| ≤ (1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  calc |(1 / 4 + (k : ℝ)) ^ 2 - (π * m / L) ^ 2| * (1 / 4 + (k : ℝ)) ^ 2
      ≤ ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) * ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) :=
        mul_le_mul h1 (by linarith) (by positivity) (by positivity)
    _ = 1 * ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) ^ 2 := by ring

theorem summable_inv_sq_quarter : Summable fun k : ℕ => 1 / (1 / 4 + (k : ℝ)) ^ 2 := by
  have h : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    refine this.congr fun k => ?_
    simp [Function.comp]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h.mul_left 16)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem summable_cutTerm (L : ℝ) (m : ℤ) : Summable (cutTerm L m) :=
  Summable.of_norm_bounded summable_inv_sq_quarter fun k => by
    rw [Real.norm_eq_abs]; exact abs_cutTerm_le L m k

theorem summable_tail_cutTerm {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Summable fun k => tailFactor L k * cutTerm L m k :=
  Summable.of_norm_bounded (summable_cutTerm L m).norm fun k => by
    have h0 : 0 ≤ tailFactor L k := (Real.exp_pos _).le
    rw [norm_mul, Real.norm_of_nonneg h0]
    have : tailFactor L k ≤ 1 := by
      unfold tailFactor
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (1 / 4 + (k : ℝ)) * (2 * L) := by positivity
      linarith
    exact mul_le_of_le_one_left (norm_nonneg _) this

/-- **Each diagonal moment splits** into twice the digamma deficit at `2πm/L` and the cut terms. -/
theorem moment_diag_split {L : ℝ} (hL : 0 < L) (m : ℤ) (k : ℕ) :
    Cvs.Finite.LevyExpMoments.moment L m m k
      = 2 * Cvs.Zeta.digammaDeficit (2 * π * m / L) k
        + 1 / L * cutTerm L m k - 1 / L * (tailFactor L k * cutTerm L m k) := by
  rw [Cvs.Finite.BracketMomentsClosed.moment_diag hL m k, Cvs.Zeta.digammaDeficit_eq]
  unfold cutTerm tailFactor
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by positivity
  have hD : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2 := by positivity
  rw [show 2 * π * m / L / 2 = π * m / L by ring]
  field_simp
  ring

/-- **The diagonal Lévy pairing is the symbol's increment plus the cut sums.** -/
theorem levyPair_diag_eq_symbol {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Cvs.Finite.LevyChannelDoubleSum.levyPair L m m
      = 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * m / L) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        + 1 / L * ∑' k, cutTerm L m k - 1 / L * ∑' k, tailFactor L k * cutTerm L m k := by
  rw [Cvs.Finite.LevyExpMoments.levyPair_eq_tsum hL, tsum_congr (moment_diag_split hL m)]
  have hd : Summable (Cvs.Zeta.digammaDeficit (2 * π * m / L)) :=
    (Cvs.WeilForm.Archimedean.LevyTermsSum.hasSum_digammaDeficit (2 * π * m / L)).summable
  have hc := summable_cutTerm L m
  have ht := summable_tail_cutTerm hL m
  rw [((hd.mul_left 2).add (hc.mul_left (1 / L))).tsum_sub (ht.mul_left (1 / L)),
    (hd.mul_left 2).tsum_add (hc.mul_left (1 / L)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    Cvs.WeilForm.Archimedean.LevyTermsSum.tsum_digammaDeficit]
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  ring

end Cvs.Finite.DiagonalLevySymbol
