import Mathlib
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffDiagonalLevyDividedDiff
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.EvenSectorSchurTest

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole-free pair function and its even-sector entries

The Lévy pair plus the symbol mass on the diagonal is a symmetric pair function on `ℤ`, even under
the sign change, whose form on an injective family is the Lévy form plus the symbol mass; its
even-sector diagonal is the symbol at the mode plus the cut sums over `2L` plus the imaginary half
over `2πm`, and its off-diagonal entries are two divided differences of the imaginary half.
-/

noncomputable section

open Real Finset

namespace Cvs.WeilForm.Archimedean.PoleFreePairFunction

open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf Cvs.Finite.DiagonalLevySymbol Cvs.WeilForm.EvenSectorSchurTest

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pole-free pair function: the Lévy pair, plus twice the symbol at the origin on the
diagonal. -/
def levySymbolPair (L : ℝ) (m n : ℤ) : ℝ :=
  Cvs.Finite.LevyChannelDoubleSum.levyPair L m n
    + 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * (if m = n then 1 else 0)

/-! ### The imaginary half is odd -/

theorem imTerm_neg (t : ℝ) (k : ℕ) : imTerm (-t) k = -imTerm t k := by
  unfold imTerm
  rw [show (-t / 2) ^ 2 = (t / 2) ^ 2 by ring]
  ring

theorem archSymbolIm_neg (t : ℝ) : archSymbolIm (-t) = -archSymbolIm t := by
  have h1 := hasSum_imTerm (-t)
  have h2 := (hasSum_imTerm t).neg
  have e : imTerm (-t) = fun k => -imTerm t k := funext (imTerm_neg t)
  rw [e] at h1
  exact h1.unique h2

theorem imTerm_zero (k : ℕ) : imTerm 0 k = 0 := by
  unfold imTerm; simp

theorem archSymbolIm_zero : archSymbolIm 0 = 0 := by
  have h := hasSum_imTerm 0
  have e : imTerm 0 = fun _ => (0 : ℝ) := funext imTerm_zero
  rw [e] at h
  exact h.unique hasSum_zero

/-! ### The even-sector entries -/

/-- The Lévy pair at `(m, −m)`: the imaginary half less its tail, over `πm`. -/
theorem levyPair_neg_self {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ≠ 0) :
    Cvs.Finite.LevyChannelDoubleSum.levyPair L m (-m)
      = (archSymbolIm (2 * π * m / L)
          - ∑' k, tailFactor L k * imTerm (2 * π * m / L) k) / (π * m) := by
  have hne : m ≠ -m := by intro h; apply hm; omega
  rw [Cvs.WeilForm.Archimedean.OffDiagonalLevyDividedDiff.levyPair_off_eq_symbolIm hL hne]
  have hneg : 2 * π * (-m : ℤ) / L = -(2 * π * m / L) := by push_cast; ring
  rw [hneg, archSymbolIm_neg]
  simp_rw [imTerm_neg]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hden : π * ((-m : ℤ) - m : ℝ) = -(2 * π * m) := by push_cast; ring
  rw [hden]
  have : ∀ k, tailFactor L k
      * ((imTerm (2 * π * m / L) k - -imTerm (2 * π * m / L) k) / -(2 * π * m))
      = -(1 / (π * m)) * (tailFactor L k * imTerm (2 * π * m / L) k) := by
    intro k; field_simp; ring
  simp_rw [this]
  rw [tsum_mul_left]
  field_simp
  ring

/-- **The even-sector diagonal**: the symbol at the mode, the cut sums over `2L`, and the imaginary
half less its tail over `2πm`. -/
theorem evenPair_diag_eq {L : ℝ} (hL : 0 < L) {m : ℤ} (hm : m ≠ 0) :
    evenPair (levySymbolPair L) m m
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * m / L)
        + (∑' k, cutTerm L m k - ∑' k, tailFactor L k * cutTerm L m k) / (2 * L)
        + (archSymbolIm (2 * π * m / L)
            - ∑' k, tailFactor L k * imTerm (2 * π * m / L) k) / (2 * π * m) := by
  unfold evenPair levySymbolPair
  have hne : m ≠ -m := by intro h; apply hm; omega
  simp only [if_true, hne, if_false, mul_one, mul_zero, add_zero]
  rw [levyPair_diag_eq_symbol hL, levyPair_neg_self hL hm]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Cvs.WeilForm.Archimedean.PoleFreePairFunction
