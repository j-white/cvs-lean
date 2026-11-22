import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.EvenPairCancellation
import Cvs.Finite.LoewnerFoldedDiagonal
import Cvs.Finite.OneModeEntries
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.WeilForm.Archimedean.PoleFreePairFunction
import Cvs.WeilForm.EvenSectorSchurTest
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine-mode diagonal of the window matrix as one Fejér prime sum

`Cvs.Finite.LoewnerFoldedDiagonal.primeFoldedDiag P R L m` is `Cvs.Finite.OneModeEntries.primeSum` of the single Fejér weight `(1 − v/L)cos(ωv) − sin(ωv)/(ωL)` cut
at `v ≤ L`, `ω = 2πm/L`. On any injective mode set with `mode j = −mode i ≠ 0` the folded diagonal of `Cvs.Finite.TruncationQuadraticForm.M` is
`Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) m m + Cvs.Finite.LoewnerFoldedDiagonal.poleFoldedDiag L m − primeSum P R (fejerCut L ω)`, which gives
the unit cosine mode's `L·ξᵀMξ` as arch plus pole minus one Fejér prime sum.
-/

noncomputable section

open Real Matrix

namespace Cvs.Finite.CosineDiagonalFejer
open Cvs.ZeroCounting

open Cvs.Finite.OneModeEntries (primeSum)

/-- The Fejér cosine-mode weight `(1 − v/L)cos(ωv) − sin(ωv)/(ωL)`, cut at the window length. -/
def fejerCut (L ω v : ℝ) : ℝ :=
  if v ≤ L then (1 - v / L) * Real.cos (ω * v) - Real.sin (ω * v) / (ω * L) else 0

/-- **The Fejér regrouping**: `Cvs.Finite.LoewnerFoldedDiagonal.primeFoldedDiag P R L m = primeSum P R (fejerCut L (2πm/L))` for `m ≠ 0`. -/
theorem primeFoldedDiag_eq_fejer (P R : ℕ) {L : ℝ} (hL : L ≠ 0) {m : ℤ} (hm : m ≠ 0) :
    Cvs.Finite.LoewnerFoldedDiagonal.primeFoldedDiag P R L m = primeSum P R (fejerCut L (2 * π * m / L)) := by
  have hωL : 2 * π * m / L * L = 2 * π * m := by field_simp
  unfold Cvs.Finite.LoewnerFoldedDiagonal.primeFoldedDiag primeSum
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  unfold fejerCut Cvs.Finite.DiagonalCutSymbol.cosCut Cvs.Finite.DiagonalCutSymbol.vcosCut
    Cvs.Finite.DiagonalCutSymbol.sinCut
  split_ifs
  · rw [hωL]
    have hπm : (2 * π * m : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (by exact_mod_cast hm)
    field_simp
  · ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The folded diagonal on any injective mode set**: for `mode j = −mode i ≠ 0`,
`M_ii + M_ij = Cvs.Finite.WindowMatrixClosedForm.diag m − Cvs.Finite.WindowMatrixClosedForm.gen m/(2πm)`; `Cvs.Finite.LoewnerFoldedDiagonal.foldedDiag_closed` is the case of `Cvs.Finite.SymmetricModeSet.mode`. -/
theorem M_even_pair {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    {i j : ι} (hj : mode j = -mode i) (hi : mode i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i i + Cvs.Finite.TruncationQuadraticForm.M P R L mode i j
      = Cvs.Finite.WindowMatrixClosedForm.diag P R L (mode i)
        - Cvs.Finite.WindowMatrixClosedForm.gen P R L (mode i) / (2 * π * mode i) := by
  have hij : i ≠ j := by
    intro h; rw [← h] at hj; omega
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R hinj, Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R hinj,
    if_pos rfl, if_neg hij, hj, Cvs.Finite.EvenPairCancellation.gen_neg]
  have hm : (mode i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hπ : π ≠ 0 := pi_ne_zero
  push_cast
  field_simp
  ring

/-- **The folded diagonal as arch + pole − one Fejér prime sum**, on any injective mode set with
`mode j = −mode i = −m ≠ 0`. -/
theorem M_even_pair_fejer {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    {i j : ι} (hj : mode j = -mode i) (hi : mode i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i i + Cvs.Finite.TruncationQuadraticForm.M P R L mode i j
      = Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) (mode i) (mode i)
        + Cvs.Finite.LoewnerFoldedDiagonal.poleFoldedDiag L (mode i)
        - primeSum P R (fejerCut L (2 * π * mode i / L)) := by
  rw [M_even_pair hL P R hinj hj hi,
    Cvs.Finite.LoewnerFoldedDiagonal.diag_sub_gen_div_eq_evenPair_levySymbolPair hL P R hi,
    primeFoldedDiag_eq_fejer P R hL.ne' hi]

/-- **On the symmetric mode set** `Cvs.Finite.SymmetricModeSet.mode N`: the folded diagonal `M_ii + M_{i,−i}` is
arch + pole − `primeSum P R (fejerCut L ω_m)`. -/
theorem foldedDiag_fejer {L : ℝ} (hL : 0 < L) (P R N : ℕ) {i : Cvs.Finite.SymmetricModeSet.Idx N}
    (hi : Cvs.Finite.SymmetricModeSet.mode N i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i i
        + Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i (Cvs.Finite.SymmetricModeSet.negI N i)
      = Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) (Cvs.Finite.SymmetricModeSet.mode N i) (Cvs.Finite.SymmetricModeSet.mode N i)
        + Cvs.Finite.LoewnerFoldedDiagonal.poleFoldedDiag L (Cvs.Finite.SymmetricModeSet.mode N i)
        - primeSum P R (fejerCut L (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L)) := by
  rw [Cvs.Finite.LoewnerFoldedDiagonal.foldedDiag_eq_evenPair_levySymbolPair hL P R N hi,
    primeFoldedDiag_eq_fejer P R hL.ne' hi]

/-- **The diagonal even-pair entry**: `2·Cvs.Finite.EvenPairCancellation.evenPairEntry P R L N i i` is arch + pole − the Fejér prime sum. -/
theorem evenPairEntry_self_fejer {L : ℝ} (hL : 0 < L) (P R N : ℕ) {i : Cvs.Finite.SymmetricModeSet.Idx N}
    (hi : Cvs.Finite.SymmetricModeSet.mode N i ≠ 0) :
    2 * Cvs.Finite.EvenPairCancellation.evenPairEntry P R L N i i
      = Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) (Cvs.Finite.SymmetricModeSet.mode N i) (Cvs.Finite.SymmetricModeSet.mode N i)
        + Cvs.Finite.LoewnerFoldedDiagonal.poleFoldedDiag L (Cvs.Finite.SymmetricModeSet.mode N i)
        - primeSum P R (fejerCut L (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L)) := by
  rw [Cvs.Finite.LoewnerFoldedDiagonal.evenPairEntry_self_closed hL P R N hi,
    Cvs.Finite.LoewnerFoldedDiagonal.diag_sub_gen_div_eq_evenPair_levySymbolPair hL P R hi,
    primeFoldedDiag_eq_fejer P R hL.ne' hi]
  ring

/-- **The unit cosine mode's form**: with `ξ = (δ_i + δ_{neg i})/√(2L)` and `mode (neg i) = −mode i = −m ≠ 0`,
`L·ξᵀMξ` is arch + pole − `primeSum P R (fejerCut L (2πm/L))`. -/
theorem quad_cosMode {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    {neg : ι → ι} (hmode : ∀ k, mode (neg k) = -mode k) {i : ι} (hi : mode i ≠ 0) :
    L * ((1 / √(2 * L)) • (Pi.single i 1 + Pi.single (neg i) 1 : ι → ℝ)
        ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L mode
          *ᵥ (1 / √(2 * L)) • (Pi.single i 1 + Pi.single (neg i) 1 : ι → ℝ)))
      = Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) (mode i) (mode i)
        + Cvs.Finite.LoewnerFoldedDiagonal.poleFoldedDiag L (mode i)
        - primeSum P R (fejerCut L (2 * π * mode i / L)) := by
  rw [← M_even_pair_fejer hL P R hinj (hmode i) hi]
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L mode
  have hnn : M (neg i) (neg i) = M i i := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj hmode i i
  have hsym : M (neg i) i = M i (neg i) := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj _ _
  have hpair : (Pi.single i 1 + Pi.single (neg i) 1 : ι → ℝ) ⬝ᵥ (M *ᵥ (Pi.single i 1 + Pi.single (neg i) 1))
      = M i i + M i (neg i) + M (neg i) i + M (neg i) (neg i) := by
    simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one, single_one_dotProduct,
      Matrix.col_apply]
    ring
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, hpair, hnn, hsym, smul_eq_mul, smul_eq_mul]
  have h2L : (0 : ℝ) < 2 * L := by positivity
  have hs0 : √(2 * L) ≠ 0 := (Real.sqrt_pos.mpr h2L).ne'
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- `quad_cosMode` on the project's symmetric mode set `Cvs.Finite.SymmetricModeSet.mode N`. -/
theorem quad_cosMode_idx {L : ℝ} (hL : 0 < L) (P R N : ℕ) {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : Cvs.Finite.SymmetricModeSet.mode N i ≠ 0) :
    L * ((1 / √(2 * L)) • (Pi.single i 1 + Pi.single (Cvs.Finite.SymmetricModeSet.negI N i) 1 : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)
        ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N)
          *ᵥ (1 / √(2 * L)) • (Pi.single i 1 + Pi.single (Cvs.Finite.SymmetricModeSet.negI N i) 1 : Cvs.Finite.SymmetricModeSet.Idx N → ℝ)))
      = Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) (Cvs.Finite.SymmetricModeSet.mode N i) (Cvs.Finite.SymmetricModeSet.mode N i)
        + Cvs.Finite.LoewnerFoldedDiagonal.poleFoldedDiag L (Cvs.Finite.SymmetricModeSet.mode N i)
        - primeSum P R (fejerCut L (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L)) :=
  quad_cosMode hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hi

end Cvs.Finite.CosineDiagonalFejer
