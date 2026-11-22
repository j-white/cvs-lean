import Mathlib
import Cvs.Finite.DiagonalLevySymbol
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped
import Cvs.WeilForm.Archimedean.SymbolIncrementTails
import Cvs.WeilForm.Archimedean.TailWeightedSums
import Cvs.Zeta.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole-free entries bounded symbolically in the modes

The imaginary half lies within `1/y` of `π/2`, the tail sums within the tail mass times the
termwise bound, and the symbol at `2y` is at least the symbol at the origin plus `K` explicit
deficit terms plus `log(y/(K + ¼))`; so the even-sector diagonal has an explicit lower bound and
every off-diagonal and constant-column entry an explicit upper bound, rational in the modes.
-/

noncomputable section

open Real Finset

namespace Cvs.WeilForm.Archimedean.PoleFreeEntryBounds

open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf Cvs.Finite.DiagonalLevySymbol

/-- The tail mass `Σ_k tailFactor L k = e^{−L/2}/(1 − e^{−2L})`. -/
def tailMass (L : ℝ) : ℝ := Real.exp (-(L / 2)) / (1 - Real.exp (-(2 * L)))

theorem tailMass_pos {L : ℝ} (hL : 0 < L) : 0 < tailMass L := by
  unfold tailMass
  have hr : Real.exp (-(2 * L)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have := Real.exp_pos (-(L / 2))
  exact div_pos this (by linarith)

/-! ### The imaginary half within `1/y` of `π/2` -/

theorem archSymbolIm_ge {y : ℝ} (hy : 0 < y) : π / 2 - 1 / y ≤ archSymbolIm (2 * y) := by
  have h := (Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped.archSymbolIm_bounds (t := 2 * y) (by linarith)).1
  rw [show 2 * y / 2 = y by ring] at h
  have ha := Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped.arctan_le_self' (x := 1 / (4 * y)) (by positivity)
  have : 1 / (4 * y) ≤ 1 / y := by
    rw [div_le_div_iff₀ (by positivity) hy]; linarith
  linarith

theorem archSymbolIm_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ archSymbolIm (2 * y) :=
  (hasSum_imTerm (2 * y)).nonneg fun k => by
    unfold imTerm; positivity

theorem archSymbolIm_le {y : ℝ} (hy : 0 < y) : archSymbolIm (2 * y) ≤ π / 2 + 1 / y := by
  have h := (Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped.archSymbolIm_bounds (t := 2 * y) (by linarith)).2
  rw [show 2 * y / 2 = y by ring] at h
  have ha : 0 ≤ Real.arctan (1 / (4 * y)) := Real.arctan_nonneg.mpr (by positivity)
  have hb : y / (1 / 16 + y ^ 2) ≤ 1 / y := by
    rw [div_le_div_iff₀ (by positivity) hy]; nlinarith
  linarith

theorem abs_archSymbolIm_sub_le' {y : ℝ} (hy : 0 < y) : |archSymbolIm (2 * y) - π / 2| ≤ 1 / y := by
  rw [abs_le]; constructor <;> linarith [archSymbolIm_ge hy, archSymbolIm_le hy]

/-! ### Tail sums against a bounded sequence -/

/-- **A tail-weighted sum of a sequence bounded by `C` is at most `C` times the tail mass.** -/
theorem abs_tsum_tailFactor_le {L : ℝ} (hL : 0 < L) {f : ℕ → ℝ} {C : ℝ} (hC : ∀ k, |f k| ≤ C) :
    |∑' k, tailFactor L k * f k| ≤ C * tailMass L := by
  have h := Cvs.WeilForm.Archimedean.TailWeightedSums.abs_tsum_tailFactor_sub_le hL hC 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one] at h
  exact h

theorem abs_imTerm_le' {y : ℝ} (hy : 0 < y) (k : ℕ) : |imTerm (2 * y) k| ≤ 1 / y := by
  have h := Cvs.WeilForm.Archimedean.TailWeightedSums.abs_imTerm_le (t := 2 * y) (by positivity) k
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * y)] at h
  calc |imTerm (2 * y) k| ≤ 2 / (2 * y) := h
    _ = 1 / y := by field_simp

theorem abs_tail_imTerm_le {L : ℝ} (hL : 0 < L) {y : ℝ} (hy : 0 < y) :
    |∑' k, tailFactor L k * imTerm (2 * y) k| ≤ 1 / y * tailMass L :=
  abs_tsum_tailFactor_le hL (abs_imTerm_le' hy)

/-! ### The symbol at `2y` from `K` explicit deficit terms -/

theorem deficitTerm_ge (y : ℝ) (hy : 0 < y) (k : ℕ) :
    1 / (1 / 4 + (k : ℝ)) - (1 / 4 + (k : ℝ)) / y ^ 2
      ≤ Cvs.Zeta.digammaDeficit (2 * y) k := by
  rw [Cvs.WeilForm.Archimedean.SymbolIncrementTails.digammaDeficit_eq_deficitTerm,
    show 2 * y / 2 = y by ring]
  unfold Cvs.WeilForm.Archimedean.SymbolIncrementTails.deficitTerm
  have ha : (0 : ℝ) < (k : ℝ) + 1 / 4 := by positivity
  have hy2 : 0 < y ^ 2 := by positivity
  rw [show (1 : ℝ) / 4 + (k : ℝ) = (k : ℝ) + 1 / 4 by ring]
  have e : y ^ 2 / (((k : ℝ) + 1 / 4) * (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2))
      = 1 / ((k : ℝ) + 1 / 4) - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) := by
    field_simp; ring
  rw [e]
  have : ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + y ^ 2) ≤ ((k : ℝ) + 1 / 4) / y ^ 2 :=
    div_le_div_of_nonneg_left ha.le hy2 (by nlinarith)
  linarith

/-- **The symbol at `2y`**: at least the symbol at the origin plus `K` explicit terms plus
`log(y/(K + ¼))`. -/
theorem archSymbol_ge_K {y : ℝ} (hy : 0 < y) {K : ℕ} (hK : 1 ≤ K) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
        + ∑ k ∈ range K, (1 / (1 / 4 + (k : ℝ)) - (1 / 4 + (k : ℝ)) / y ^ 2)
        + Real.log (y / ((K : ℝ) + 1 / 4))
      ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * y) := by
  have h := (Cvs.WeilForm.Archimedean.SymbolIncrementTails.increment_bounds (t := 2 * y) (by positivity) hK).1
  rw [show 2 * y / 2 = y by ring] at h
  have hsum : ∑ k ∈ range K, (1 / (1 / 4 + (k : ℝ)) - (1 / 4 + (k : ℝ)) / y ^ 2)
      ≤ ∑ k ∈ range K, Cvs.Zeta.digammaDeficit (2 * y) k :=
    Finset.sum_le_sum fun k _ => deficitTerm_ge y hy k
  have hK' : (0 : ℝ) < (K : ℝ) + 1 / 4 := by positivity
  have hlog : Real.log (y / ((K : ℝ) + 1 / 4)) ≤ Real.log (1 + y ^ 2 / ((K : ℝ) + 1 / 4) ^ 2) / 2 := by
    have hx : 0 < y / ((K : ℝ) + 1 / 4) := by positivity
    have e : y ^ 2 / ((K : ℝ) + 1 / 4) ^ 2 = (y / ((K : ℝ) + 1 / 4)) ^ 2 :=
      (div_pow y ((K : ℝ) + 1 / 4) 2).symm
    rw [e, ← Real.log_sqrt (by positivity)]
    apply Real.log_le_log hx
    rw [Real.le_sqrt hx.le (by positivity)]
    linarith
  linarith

/-! ### The diagonal below and the off-diagonal above -/

end Cvs.WeilForm.Archimedean.PoleFreeEntryBounds
