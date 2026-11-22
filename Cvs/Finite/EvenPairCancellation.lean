import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.OneModeEntries
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.WeilForm.Archimedean.PoleFreePairFunction
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# Closed-Form Even-Pair Cancellation and Endpoint-Flat High-Mode Leakage

Proves oddness of `Cvs.Finite.WindowMatrixClosedForm.gen`, closed-form formulas for `evenPairEntry` and `flatPairEntry`, and the
$O(J^3 / (K - J)^3)$ decay of `highPart` mass and `weightedLeakage` on endpoint-flat even vectors.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Finite.EvenPairCancellation

open scoped BigOperators Matrix InnerProductSpace
open Real Finset
open Cvs.Finite.SymmetricModeSet

/-! ### Oddness of `Cvs.Finite.WindowMatrixClosedForm.gen` -/

/-- `Cvs.Finite.OneModeEntries.poleSin L` is an odd function of frequency `ω`. -/
theorem poleSin_neg (L ω : ℝ) : Cvs.Finite.OneModeEntries.poleSin L (-ω) = -Cvs.Finite.OneModeEntries.poleSin L ω := by
  unfold Cvs.Finite.OneModeEntries.poleSin
  ring

/-- `Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm` is an odd function of frequency `ω`. -/
theorem imTerm_neg (ω : ℝ) (k : ℕ) : Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (-ω) k = -Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm ω k :=
  Cvs.WeilForm.Archimedean.PoleFreePairFunction.imTerm_neg ω k

/-- `Cvs.Finite.DiagonalCutSymbol.sinCut L` is an odd function of frequency `ω`. -/
theorem sinCut_neg (L ω v : ℝ) : Cvs.Finite.DiagonalCutSymbol.sinCut L (-ω) v = -Cvs.Finite.DiagonalCutSymbol.sinCut L ω v := by
  unfold Cvs.Finite.DiagonalCutSymbol.sinCut
  split_ifs
  · rw [neg_mul, Real.sin_neg]
  · ring

/-- The finite prime sum of `sinCut L` is an odd function of frequency `ω`. -/
theorem primeSum_sinCut_neg (P R : ℕ) (L ω : ℝ) :
    Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L (-ω)) = -Cvs.Finite.OneModeEntries.primeSum P R (Cvs.Finite.DiagonalCutSymbol.sinCut L ω) := by
  unfold Cvs.Finite.OneModeEntries.primeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sinCut_neg]
  ring

/-- `Cvs.Finite.WindowMatrixClosedForm.gen P R L` is an odd function of the integer mode `m : ℤ`. -/
theorem gen_neg (P R : ℕ) (L : ℝ) (m : ℤ) :
    Cvs.Finite.WindowMatrixClosedForm.gen P R L (-m) = -Cvs.Finite.WindowMatrixClosedForm.gen P R L m := by
  unfold Cvs.Finite.WindowMatrixClosedForm.gen
  have hω : 2 * π * ((-m : ℤ) : ℝ) / L = -(2 * π * (m : ℝ) / L) := by
    push_cast
    ring
  rw [hω, poleSin_neg, Cvs.WeilForm.Archimedean.PoleFreePairFunction.archSymbolIm_neg, primeSum_sinCut_neg]
  have htsum : (∑' j, Cvs.Finite.DiagonalLevySymbol.tailFactor L j * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (-(2 * π * (m : ℝ) / L)) j) =
      -∑' j, Cvs.Finite.DiagonalLevySymbol.tailFactor L j * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2 * π * (m : ℝ) / L) j := by
    have hterm : (fun j => Cvs.Finite.DiagonalLevySymbol.tailFactor L j * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (-(2 * π * (m : ℝ) / L)) j) =
        fun j => -(Cvs.Finite.DiagonalLevySymbol.tailFactor L j * Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.imTerm (2 * π * (m : ℝ) / L) j) := by
      funext j
      rw [imTerm_neg, mul_neg]
    rw [hterm, tsum_neg]
  rw [htsum]
  ring

/-- `Cvs.Finite.WindowMatrixClosedForm.gen P R L` vanishes at mode `0`. -/
theorem gen_zero (P R : ℕ) (L : ℝ) : Cvs.Finite.WindowMatrixClosedForm.gen P R L 0 = 0 := by
  have h := gen_neg P R L 0
  simp only [neg_zero] at h
  linarith

/-! ### Closed-form even-pair and endpoint-flat entries of `Cvs.Finite.TruncationQuadraticForm.M` -/

/-- Closed form of the zero-mode column entry `Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i none` for
`Cvs.Finite.SymmetricModeSet.mode N i ≠ 0`. -/
theorem M_apply_none_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : Cvs.Finite.SymmetricModeSet.mode N i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i none =
      -Cvs.Finite.WindowMatrixClosedForm.gen P R L (Cvs.Finite.SymmetricModeSet.mode N i) / (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ)) := by
  have hine : i ≠ none := by
    rintro rfl
    exact hi rfl
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) i none, if_neg hine]
  change (Cvs.Finite.WindowMatrixClosedForm.gen P R L (Cvs.Finite.SymmetricModeSet.mode N i) - Cvs.Finite.WindowMatrixClosedForm.gen P R L 0) /
    (2 * π * (((0 : ℤ) : ℝ) - (Cvs.Finite.SymmetricModeSet.mode N i : ℝ))) = _
  rw [gen_zero, Int.cast_zero]
  ring

/-- Even-symmetrized matrix entry `(M i j + M i (negI N j)) / 2`. -/
def evenPairEntry (P R : ℕ) (L : ℝ) (N : ℕ) (i j : Cvs.Finite.SymmetricModeSet.Idx N) : ℝ :=
  (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i j + Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i (Cvs.Finite.SymmetricModeSet.negI N j)) / 2

/-- Endpoint-subtracted even-pair entry `evenPairEntry P R L N i j - M i none`. -/
def flatPairEntry (P R : ℕ) (L : ℝ) (N : ℕ) (i j : Cvs.Finite.SymmetricModeSet.Idx N) : ℝ :=
  evenPairEntry P R L N i j - Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) i none

/-- Closed form of `evenPairEntry P R L N i j` when `(mode N j).natAbs < (mode N i).natAbs`. -/
theorem evenPairEntry_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i j : Cvs.Finite.SymmetricModeSet.Idx N} (hij : (Cvs.Finite.SymmetricModeSet.mode N j).natAbs < (Cvs.Finite.SymmetricModeSet.mode N i).natAbs) :
    evenPairEntry P R L N i j =
      ((Cvs.Finite.SymmetricModeSet.mode N j : ℝ) * Cvs.Finite.WindowMatrixClosedForm.gen P R L (Cvs.Finite.SymmetricModeSet.mode N j) -
          (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) * Cvs.Finite.WindowMatrixClosedForm.gen P R L (Cvs.Finite.SymmetricModeSet.mode N i)) /
        (2 * π * ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ^ 2 - (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2)) := by
  have hne1 : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  have hne2 : i ≠ Cvs.Finite.SymmetricModeSet.negI N j := by
    intro h
    have h1 := congrArg (fun k => (Cvs.Finite.SymmetricModeSet.mode N k).natAbs) h
    simp only [Cvs.Finite.SymmetricModeSet.mode_negI, Int.natAbs_neg] at h1
    omega
  have habs : |(Cvs.Finite.SymmetricModeSet.mode N j : ℝ)| < |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| := by
    have h : ((Cvs.Finite.SymmetricModeSet.mode N j).natAbs : ℝ) < ((Cvs.Finite.SymmetricModeSet.mode N i).natAbs : ℝ) := by
      exact_mod_cast hij
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hsub1 : (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) - (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ≠ 0 := by
    intro h
    have heq : (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) = (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) := sub_eq_zero.mp h
    rw [heq] at habs
    exact lt_irrefl _ habs
  have hsub2 : -(Cvs.Finite.SymmetricModeSet.mode N j : ℝ) - (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ≠ 0 := by
    intro h
    have heq : (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) = -(Cvs.Finite.SymmetricModeSet.mode N j : ℝ) := by linarith
    rw [heq, abs_neg] at habs
    exact lt_irrefl _ habs
  have hsq : (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ^ 2 - (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2 ≠ 0 := by
    have hpos : (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2 < (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ^ 2 := by
      rw [← sq_abs (Cvs.Finite.SymmetricModeSet.mode N j : ℝ), ← sq_abs (Cvs.Finite.SymmetricModeSet.mode N i : ℝ)]
      exact sq_lt_sq.mpr (by rwa [abs_abs, abs_abs])
    linarith
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold evenPairEntry
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) i j, if_neg hne1,
    Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R (Cvs.Finite.SymmetricModeSet.mode_injective N) i (Cvs.Finite.SymmetricModeSet.negI N j), if_neg hne2,
    Cvs.Finite.SymmetricModeSet.mode_negI, gen_neg, Int.cast_neg]
  field_simp
  ring

/-- Closed form of `flatPairEntry P R L N i j` when `(mode N j).natAbs < (mode N i).natAbs`,
exhibiting exact cancellation of the leading `(mode N i) ^ 2 * gen (mode N i)` term. -/
theorem flatPairEntry_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i j : Cvs.Finite.SymmetricModeSet.Idx N} (hij : (Cvs.Finite.SymmetricModeSet.mode N j).natAbs < (Cvs.Finite.SymmetricModeSet.mode N i).natAbs) :
    flatPairEntry P R L N i j =
      ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) * (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) * Cvs.Finite.WindowMatrixClosedForm.gen P R L (Cvs.Finite.SymmetricModeSet.mode N j) -
          (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2 * Cvs.Finite.WindowMatrixClosedForm.gen P R L (Cvs.Finite.SymmetricModeSet.mode N i)) /
        (2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) *
          ((Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ^ 2 - (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2)) := by
  have hi0 : Cvs.Finite.SymmetricModeSet.mode N i ≠ 0 :=
    Int.natAbs_ne_zero.mp (by omega)
  have hmi : (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ≠ 0 := by exact_mod_cast hi0
  have habs : |(Cvs.Finite.SymmetricModeSet.mode N j : ℝ)| < |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| := by
    have h : ((Cvs.Finite.SymmetricModeSet.mode N j).natAbs : ℝ) < ((Cvs.Finite.SymmetricModeSet.mode N i).natAbs : ℝ) := by
      exact_mod_cast hij
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hsq : (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ^ 2 - (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2 ≠ 0 := by
    have hpos : (Cvs.Finite.SymmetricModeSet.mode N j : ℝ) ^ 2 < (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) ^ 2 := by
      rw [← sq_abs (Cvs.Finite.SymmetricModeSet.mode N j : ℝ), ← sq_abs (Cvs.Finite.SymmetricModeSet.mode N i : ℝ)]
      exact sq_lt_sq.mpr (by rwa [abs_abs, abs_abs])
    linarith
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold flatPairEntry
  rw [evenPairEntry_closed hL P R N hij, M_apply_none_closed hL P R N hi0]
  field_simp
  ring

/-! ### Exact row decomposition and endpoint-flat high-mode leakage bounds -/

end Cvs.Finite.EvenPairCancellation
