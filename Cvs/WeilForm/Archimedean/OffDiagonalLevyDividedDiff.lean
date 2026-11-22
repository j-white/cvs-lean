import Mathlib
import Cvs.Finite.BracketMomentsClosed
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyExpMoments
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-diagonal Lévy channel is a divided difference of the symbol's imaginary half

Each off-diagonal moment of the bracket is a divided difference, over the two lattice frequencies,
of the terms whose series is the symbol's imaginary half; so the Lévy pairing of two distinct modes
is minus the divided difference of `archSymbolIm` at `2πm/L` and `2πn/L` plus a cut sum, and on a
window no longer than `log 2` that is the whole pair value beyond the pole channel.
-/

noncomputable section

open Real

namespace Cvs.WeilForm.Archimedean.OffDiagonalLevyDividedDiff

open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-- The imaginary-half term at mode `m`: `b/(a² + b²)` with `a = k + 1/4`, `b = πm/L`. -/
theorem imTerm_mode (L : ℝ) (m : ℤ) (k : ℕ) :
    imTerm (2 * π * m / L) k = (π * m / L) / ((1 / 4 + (k : ℝ)) ^ 2 + (π * m / L) ^ 2) := by
  unfold imTerm
  rw [show 2 * π * m / L / 2 = π * m / L by ring]

/-- **Each off-diagonal moment is a divided difference of the imaginary-half terms.** -/
theorem moment_off_split {L : ℝ} (hL : 0 < L) {m n : ℤ} (hmn : m ≠ n) (k : ℕ) :
    Cvs.Finite.LevyExpMoments.moment L m n k
      = -(imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m))
        + Cvs.Finite.DiagonalLevySymbol.tailFactor L k
          * ((imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m))) := by
  rw [Cvs.Finite.BracketMomentsClosed.moment_off hL hmn k, imTerm_mode, imTerm_mode]
  unfold Cvs.Finite.DiagonalLevySymbol.tailFactor
  ring

theorem summable_tail_imTerm {L : ℝ} (hL : 0 < L) (m n : ℤ) :
    Summable fun k => Cvs.Finite.DiagonalLevySymbol.tailFactor L k
      * ((imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m))) := by
  have hs : Summable fun k =>
      (imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m)) :=
    ((summable_imTerm _).sub (summable_imTerm _)).div_const _
  refine Summable.of_norm_bounded hs.norm fun k => ?_
  have h0 : 0 ≤ Cvs.Finite.DiagonalLevySymbol.tailFactor L k := (Real.exp_pos _).le
  rw [norm_mul, Real.norm_of_nonneg h0]
  have h1 : Cvs.Finite.DiagonalLevySymbol.tailFactor L k ≤ 1 := by
    unfold Cvs.Finite.DiagonalLevySymbol.tailFactor
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (1 / 4 + (k : ℝ)) * (2 * L) := by positivity
    linarith
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- **The off-diagonal Lévy pairing is a divided difference of the symbol's imaginary half**, plus
a cut sum. -/
theorem levyPair_off_eq_symbolIm {L : ℝ} (hL : 0 < L) {m n : ℤ} (hmn : m ≠ n) :
    Cvs.Finite.LevyChannelDoubleSum.levyPair L m n
      = -(archSymbolIm (2 * π * m / L) - archSymbolIm (2 * π * n / L)) / (π * ((n : ℝ) - m))
        + ∑' k, Cvs.Finite.DiagonalLevySymbol.tailFactor L k
          * ((imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m))) := by
  rw [Cvs.Finite.LevyExpMoments.levyPair_eq_tsum hL, tsum_congr (moment_off_split hL hmn)]
  have hs : Summable fun k =>
      -(imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m)) := by
    have := ((summable_imTerm (2 * π * m / L)).sub (summable_imTerm (2 * π * n / L))).div_const
      (π * ((n : ℝ) - m))
    exact this.neg.congr fun k => by ring
  rw [hs.tsum_add (summable_tail_imTerm hL m n)]
  congr 1
  have e : (fun k => -(imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) / (π * ((n : ℝ) - m)))
      = fun k => (-(1 / (π * ((n : ℝ) - m)))) * (imTerm (2 * π * m / L) k - imTerm (2 * π * n / L) k) := by
    funext k; ring
  rw [e, tsum_mul_left, (summable_imTerm _).tsum_sub (summable_imTerm _),
    (hasSum_imTerm _).tsum_eq, (hasSum_imTerm _).tsum_eq]
  ring

end Cvs.WeilForm.Archimedean.OffDiagonalLevyDividedDiff
