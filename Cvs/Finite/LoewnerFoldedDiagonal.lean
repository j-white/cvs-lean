import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.EvenPairCancellation
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixClosedForm
import Cvs.StepA.WindowGeneratorZeros
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.PoleFreePairFunction
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.WeilForm.EvenSectorSchurTest
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Closed-Form Loewner Folded Diagonal and Zero-Side Pair Identities

Connects `Cvs.Finite.WindowMatrixClosedForm.M_apply_closed` to the folded even-sector decomposition of `Cvs.WeilForm.Archimedean.PoleFreePairFunction` at general
truncation `(P, R, L)` and to the zero-side partial-fraction expansions of `Cvs.Finite.EvenPairCancellation` and `Cvs.StepA.WindowGeneratorZeros`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Finite.LoewnerFoldedDiagonal
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Finset
open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf (imTerm archSymbolIm)
open Cvs.Finite.SymmetricModeSet (Idx mode negI mode_negI mode_injective)
open Cvs.Finite.DiagonalCutSymbol (cosCut vcosCut sinCut)
open Cvs.Finite.OneModeEntries (poleSin primeSum)
open Cvs.Finite.PairPoleChannelClosed (freq poleFactor)
open Cvs.Finite.DiagonalLevySymbol (cutTerm tailFactor)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

/-! ### Part 1: Closed-form folded even-sector entries at general `(P, R, L)` -/

/-- Closed form of the reflection-paired entry `M i (negI N i)` for `mode N i ≠ 0`. -/
theorem M_apply_negI_self_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i : Idx N} (hi : mode N i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i (negI N i) =
      -Cvs.Finite.WindowMatrixClosedForm.gen P R L (mode N i) / (2 * π * (mode N i : ℝ)) := by
  have hne : i ≠ negI N i := by
    intro h
    have hm := congrArg (mode N) h
    rw [mode_negI] at hm
    exact hi (by omega)
  have hmi : (mode N i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R (mode_injective N) i (negI N i), if_neg hne,
    mode_negI, Cvs.Finite.EvenPairCancellation.gen_neg, Int.cast_neg]
  field_simp
  ring

/-- Closed form of the diagonal even-pair entry `evenPairEntry P R L N i i` for `mode N i ≠ 0`. -/
theorem evenPairEntry_self_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i : Idx N} (hi : mode N i ≠ 0) :
    Cvs.Finite.EvenPairCancellation.evenPairEntry P R L N i i =
      (Cvs.Finite.WindowMatrixClosedForm.diag P R L (mode N i) -
        Cvs.Finite.WindowMatrixClosedForm.gen P R L (mode N i) / (2 * π * (mode N i : ℝ))) / 2 := by
  unfold Cvs.Finite.EvenPairCancellation.evenPairEntry
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R (mode_injective N) i i, if_pos rfl,
    M_apply_negI_self_closed hL P R N hi]
  ring

/-- Closed form of the folded diagonal `M i i + M i (negI N i)` for `mode N i ≠ 0`. -/
theorem foldedDiag_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i : Idx N} (hi : mode N i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i i + Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i (negI N i) =
      Cvs.Finite.WindowMatrixClosedForm.diag P R L (mode N i) -
        Cvs.Finite.WindowMatrixClosedForm.gen P R L (mode N i) / (2 * π * (mode N i : ℝ)) := by
  rw [Cvs.Finite.WindowMatrixClosedForm.M_apply_closed hL P R (mode_injective N) i i, if_pos rfl,
    M_apply_negI_self_closed hL P R N hi]
  ring

/-- Closed form of `evenPairEntry P R L N i none` for `mode N i ≠ 0`. -/
theorem evenPairEntry_none_right_closed {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i : Idx N} (hi : mode N i ≠ 0) :
    Cvs.Finite.EvenPairCancellation.evenPairEntry P R L N i none =
      -Cvs.Finite.WindowMatrixClosedForm.gen P R L (mode N i) / (2 * π * (mode N i : ℝ)) := by
  have hnone : negI N none = none := rfl
  unfold Cvs.Finite.EvenPairCancellation.evenPairEntry
  rw [hnone, Cvs.Finite.EvenPairCancellation.M_apply_none_closed hL P R N hi]
  ring

/-- The folded even-sector pole contribution on the diagonal at mode `m`. -/
def poleFoldedDiag (L : ℝ) (m : ℤ) : ℝ :=
  2 / L * (1 / 4 - freq L m ^ 2) * poleFactor L / (1 / 4 + freq L m ^ 2) ^ 2 -
    poleSin L (2 * π * m / L) / (π * m)

/-- The folded even-sector prime-power contribution on the diagonal at mode `m`. -/
def primeFoldedDiag (P R : ℕ) (L : ℝ) (m : ℤ) : ℝ :=
  primeSum P R (cosCut L (2 * π * m / L)) -
    1 / L * primeSum P R (vcosCut L (2 * π * m / L)) -
    primeSum P R (sinCut L (2 * π * m / L)) / (2 * π * m)

/-- At any `(P, R, L)` and nonzero mode `m`, the folded diagonal `diag - gen / (2πm)` decomposes
into `Cvs.WeilForm.Archimedean.PoleFreePairFunction.evenPair (levySymbolPair L) m m` plus `poleFoldedDiag` minus `primeFoldedDiag`. -/
theorem diag_sub_gen_div_eq_evenPair_levySymbolPair {L : ℝ} (hL : 0 < L) (P R : ℕ)
    {m : ℤ} (hm : m ≠ 0) :
    Cvs.Finite.WindowMatrixClosedForm.diag P R L m - Cvs.Finite.WindowMatrixClosedForm.gen P R L m / (2 * π * (m : ℝ)) =
      Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) m m +
        poleFoldedDiag L m - primeFoldedDiag P R L m := by
  unfold Cvs.Finite.WindowMatrixClosedForm.diag Cvs.Finite.WindowMatrixClosedForm.gen poleFoldedDiag primeFoldedDiag
  rw [Cvs.WeilForm.Archimedean.PoleFreePairFunction.evenPair_diag_eq hL hm, ← Cvs.Finite.WindowMatrixClosedForm.tsum_cutTerm L m]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Entry-level bridge from the folded CvS diagonal `M i i + M i (negI N i)` to `Cvs.WeilForm.Archimedean.PoleFreePairFunction.evenPair`. -/
theorem foldedDiag_eq_evenPair_levySymbolPair {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i : Idx N} (hi : mode N i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i i + Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) i (negI N i) =
      Cvs.WeilForm.EvenSectorSchurTest.evenPair (Cvs.WeilForm.Archimedean.PoleFreePairFunction.levySymbolPair L) (mode N i) (mode N i) +
        poleFoldedDiag L (mode N i) - primeFoldedDiag P R L (mode N i) := by
  rw [foldedDiag_closed hL P R N hi, diag_sub_gen_div_eq_evenPair_levySymbolPair hL P R hi]

/-- At `P = 0`, `primeSum 0 R f` vanishes identically. -/
theorem primeSum_zero_left (R : ℕ) (f : ℝ → ℝ) : primeSum 0 R f = 0 := by
  unfold primeSum
  have h : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by decide
  rw [h, Finset.sum_empty]

/-- Exact split of `Cvs.Finite.WindowMatrixClosedForm.gen P R L m` into the prime-free generator `Cvs.Finite.WindowMatrixClosedForm.gen 0 0 L m` minus
the finite prime sine sum. -/
theorem gen_eq_gen_zero_sub_primeSum (P R : ℕ) (L : ℝ) (m : ℤ) :
    Cvs.Finite.WindowMatrixClosedForm.gen P R L m =
      Cvs.Finite.WindowMatrixClosedForm.gen 0 0 L m - primeSum P R (sinCut L (2 * π * m / L)) := by
  unfold Cvs.Finite.WindowMatrixClosedForm.gen
  rw [primeSum_zero_left]
  ring

/-- Exact split of `Cvs.Finite.WindowMatrixClosedForm.diag P R L m` into the prime-free diagonal `Cvs.Finite.WindowMatrixClosedForm.diag 0 0 L m` minus
the finite prime cosine and `v cos` sums. -/
theorem diag_eq_diag_zero_sub_primeSum (P R : ℕ) (L : ℝ) (m : ℤ) :
    Cvs.Finite.WindowMatrixClosedForm.diag P R L m =
      Cvs.Finite.WindowMatrixClosedForm.diag 0 0 L m -
        (primeSum P R (cosCut L (2 * π * m / L)) -
          1 / L * primeSum P R (vcosCut L (2 * π * m / L))) := by
  unfold Cvs.Finite.WindowMatrixClosedForm.diag
  rw [primeSum_zero_left, primeSum_zero_left]
  ring

/-- Exact split of `evenPairEntry P R L N i j` into the prime-free entry `evenPairEntry 0 0 L N i j`
minus the prime sine Loewner divided difference. -/
theorem evenPairEntry_eq_evenPairEntry_zero_sub_prime {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i j : Idx N} (hij : (mode N j).natAbs < (mode N i).natAbs) :
    Cvs.Finite.EvenPairCancellation.evenPairEntry P R L N i j =
      Cvs.Finite.EvenPairCancellation.evenPairEntry 0 0 L N i j -
        ((mode N j : ℝ) * primeSum P R (sinCut L (2 * π * mode N j / L)) -
            (mode N i : ℝ) * primeSum P R (sinCut L (2 * π * mode N i / L))) /
          (2 * π * ((mode N i : ℝ) ^ 2 - (mode N j : ℝ) ^ 2)) := by
  rw [Cvs.Finite.EvenPairCancellation.evenPairEntry_closed hL P R N hij, Cvs.Finite.EvenPairCancellation.evenPairEntry_closed hL 0 0 N hij,
    gen_eq_gen_zero_sub_primeSum P R L (mode N j), gen_eq_gen_zero_sub_primeSum P R L (mode N i)]
  ring

/-- Exact split of `flatPairEntry P R L N i j` into the prime-free entry `flatPairEntry 0 0 L N i j`
minus the endpoint-flat prime sine Loewner divided difference. -/
theorem flatPairEntry_eq_flatPairEntry_zero_sub_prime {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    {i j : Idx N} (hij : (mode N j).natAbs < (mode N i).natAbs) :
    Cvs.Finite.EvenPairCancellation.flatPairEntry P R L N i j =
      Cvs.Finite.EvenPairCancellation.flatPairEntry 0 0 L N i j -
        ((mode N i : ℝ) * (mode N j : ℝ) * primeSum P R (sinCut L (2 * π * mode N j / L)) -
            (mode N j : ℝ) ^ 2 * primeSum P R (sinCut L (2 * π * mode N i / L))) /
          (2 * π * (mode N i : ℝ) * ((mode N i : ℝ) ^ 2 - (mode N j : ℝ) ^ 2)) := by
  rw [Cvs.Finite.EvenPairCancellation.flatPairEntry_closed hL P R N hij, Cvs.Finite.EvenPairCancellation.flatPairEntry_closed hL 0 0 N hij,
    gen_eq_gen_zero_sub_primeSum P R L (mode N j), gen_eq_gen_zero_sub_primeSum P R L (mode N i)]
  ring

/-! ### Part 2: Zero-side Loewner identities for `M_apply_none`, `evenPairEntry`, `flatPairEntry` -/

/-- At any resonance `z = ±(2πm/L)`, the factor `sin²(Lz/2)` vanishes. -/
theorem sin_sq_eq_zero_of_sq_sub_sq_eq_zero {L : ℝ} (hL : 0 < L) (m : ℤ) {z : ℂ}
    (hz : (((2 * π * m / L : ℝ) : ℂ) ^ 2 - z ^ 2) = 0) :
    Complex.sin ((L : ℂ) * z / 2) ^ 2 = 0 := by
  set ω : ℂ := ((2 * π * m / L : ℝ) : ℂ)
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hfac : (ω - z) * (ω + z) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hfac with h | h
  · have hzω : z = ω := (sub_eq_zero.mp h).symm
    have harg : (L : ℂ) * z / 2 = ((m * π : ℝ) : ℂ) := by
      rw [hzω]; dsimp [ω]; push_cast; field_simp
    rw [harg, ← Complex.ofReal_sin, Real.sin_int_mul_pi, Complex.ofReal_zero, sq, mul_zero]
  · have hzω : z = -ω := by linear_combination h
    have harg : (L : ℂ) * z / 2 = (((-m : ℤ) * π : ℝ) : ℂ) := by
      rw [hzω]; dsimp [ω]; push_cast; field_simp
    rw [harg, ← Complex.ofReal_sin, Real.sin_int_mul_pi, Complex.ofReal_zero, sq, mul_zero]

/-- Complex partial-fraction identity for the even-pair Loewner difference. -/
theorem evenPair_zeroTerm_sub_eq {L : ℝ} (hL : 0 < L) (mi mj : ℤ) (z : ℂ) :
    (mj : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * z / 2) ^ 2 /
        ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - z ^ 2))) -
      (mi : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * z / 2) ^ 2 /
        ((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - z ^ 2))) =
      ((mi : ℂ) ^ 2 - (mj : ℂ) ^ 2) *
        (z ^ 2 * Complex.sin ((L : ℂ) * z / 2) ^ 2 /
          (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - z ^ 2)) *
            ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - z ^ 2)))) := by
  set S : ℂ := Complex.sin ((L : ℂ) * z / 2) ^ 2
  set Di : ℂ := (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - z ^ 2)
  set Dj : ℂ := (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - z ^ 2)
  rcases eq_or_ne Di 0 with hDi | hDi
  · have hS : S = 0 := sin_sq_eq_zero_of_sq_sub_sq_eq_zero hL mi hDi
    simp [hS]
  rcases eq_or_ne Dj 0 with hDj | hDj
  · have hS : S = 0 := sin_sq_eq_zero_of_sq_sub_sq_eq_zero hL mj hDj
    simp [hS]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hDiDj : Di * Dj ≠ 0 := mul_ne_zero hDi hDj
  rw [mul_div_assoc', mul_div_assoc', div_sub_div _ _ hDj hDi,
    mul_div_assoc', div_eq_div_iff (mul_ne_zero hDj hDi) hDiDj]
  dsimp [Di, Dj]
  push_cast
  field_simp
  ring

/-- Complex partial-fraction identity for the endpoint-flat Loewner difference. -/
theorem flatPair_zeroTerm_sub_eq {L : ℝ} (hL : 0 < L) (mi mj : ℤ) (z : ℂ) :
    (mj : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * z / 2) ^ 2 /
        ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - z ^ 2))) -
      (mj : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * z / 2) ^ 2 /
        ((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - z ^ 2))) =
      ((mi : ℂ) ^ 2 - (mj : ℂ) ^ 2) *
        ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 * Complex.sin ((L : ℂ) * z / 2) ^ 2) /
          (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - z ^ 2)) *
            ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - z ^ 2)))) := by
  set S : ℂ := Complex.sin ((L : ℂ) * z / 2) ^ 2
  set Di : ℂ := (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - z ^ 2)
  set Dj : ℂ := (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - z ^ 2)
  rcases eq_or_ne Di 0 with hDi | hDi
  · have hS : S = 0 := sin_sq_eq_zero_of_sq_sub_sq_eq_zero hL mi hDi
    simp [hS]
  rcases eq_or_ne Dj 0 with hDj | hDj
  · have hS : S = 0 := sin_sq_eq_zero_of_sq_sub_sq_eq_zero hL mj hDj
    simp [hS]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hDiDj : Di * Dj ≠ 0 := mul_ne_zero hDi hDj
  rw [mul_div_assoc', mul_div_assoc', div_sub_div _ _ hDj hDi,
    mul_div_assoc', div_eq_div_iff (mul_ne_zero hDj hDi) hDiDj]
  dsimp [Di, Dj]
  push_cast
  field_simp
  ring

/-- Summability of the mode-weighted zero series for any integer mode `m : ℤ` (including `0`). -/
theorem summable_sq_mul_genTerm {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Summable fun rho : nonTrivialZeroSet => (m : ℝ) ^ 2 *
      ((Cvs.Criterion.divisorWeight rho : ℝ) *
        (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [summable_zero]
  · exact (Cvs.StepA.WindowGeneratorZeros.summable_genTerm hL hm).mul_left ((m : ℝ) ^ 2)

/-- Zero-side representation of the constant-mode column `M i none` for `mode N i ≠ 0`. -/
theorem M_apply_none_eq_zeroSide {L : ℝ} (hL : 0 < L) (N : ℕ)
    {i : Idx N} (hi : mode N i ≠ 0) :
    Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N) i none =
      -(4 / L) * ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
        (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mode N i / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
  rw [Cvs.Finite.EvenPairCancellation.M_apply_none_closed hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ N hi,
    Cvs.StepA.WindowGeneratorZeros.gen_eq_zeroSide_int hL (mode N i)]
  have hL0 : L ≠ 0 := hL.ne'
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hmi : (mode N i : ℝ) ≠ 0 := by exact_mod_cast hi
  field_simp
  ring

/-- Zero-side closed form of `evenPairEntry` when `(mode N j).natAbs < (mode N i).natAbs`. -/
theorem evenPairEntry_eq_zeroSide {L : ℝ} (hL : 0 < L) (N : ℕ)
    {i j : Idx N} (hij : (mode N j).natAbs < (mode N i).natAbs) :
    Cvs.Finite.EvenPairCancellation.evenPairEntry ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L N i j =
      (4 / L) * ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
        (Cvs.ZeroCounting.zPoint rho ^ 2 *
          Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((((2 * π * mode N i / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
              ((((2 * π * mode N j / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re := by
  set mi : ℤ := mode N i
  set mj : ℤ := mode N j
  have habs : |(mj : ℝ)| < |(mi : ℝ)| := by
    have h : (mj.natAbs : ℝ) < (mi.natAbs : ℝ) := by exact_mod_cast hij
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hsq : (mi : ℝ) ^ 2 - (mj : ℝ) ^ 2 ≠ 0 := by
    have hpos : (mj : ℝ) ^ 2 < (mi : ℝ) ^ 2 := by
      rw [← sq_abs (mj : ℝ), ← sq_abs (mi : ℝ)]
      exact sq_lt_sq.mpr (by rwa [abs_abs, abs_abs])
    linarith
  have hL0 : L ≠ 0 := hL.ne'
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Cvs.Finite.EvenPairCancellation.evenPairEntry_closed hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ N hij,
    Cvs.StepA.WindowGeneratorZeros.gen_eq_zeroSide_int hL mj, Cvs.StepA.WindowGeneratorZeros.gen_eq_zeroSide_int hL mi]
  change ((mj : ℝ) * (8 * π * (mj : ℝ) / L * _) - (mi : ℝ) * (8 * π * (mi : ℝ) / L * _)) /
      (2 * π * ((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2)) = _
  have hmul : ∀ m : ℤ, (m : ℝ) * (8 * π * (m : ℝ) / L *
      ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
        (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) =
      (8 * π / L) * ∑' rho : nonTrivialZeroSet, (m : ℝ) ^ 2 *
        ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * m / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) := by
    intro m
    rw [tsum_mul_left]
    ring
  rw [hmul mj, hmul mi, ← mul_sub, ← (summable_sq_mul_genTerm hL mj).tsum_sub
    (summable_sq_mul_genTerm hL mi)]
  have hterm : ∀ rho : nonTrivialZeroSet,
      (mj : ℝ) ^ 2 * ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) -
        (mi : ℝ) ^ 2 * ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) =
      ((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2) *
        ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Cvs.ZeroCounting.zPoint rho ^ 2 *
            Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
              (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
                ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re) := by
    intro rho
    have hre := congrArg Complex.re (evenPair_zeroTerm_sub_eq hL mi mj (Cvs.ZeroCounting.zPoint rho))
    have h1 : (((mj : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
        (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re =
        (mj : ℝ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
      rw [show (mj : ℂ) ^ 2 = (((mj : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have h2 : (((mi : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
        (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re =
        (mi : ℝ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
      rw [show (mi : ℂ) ^ 2 = (((mi : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have h3 : ((((mi : ℂ) ^ 2 - (mj : ℂ) ^ 2)) *
        (Cvs.ZeroCounting.zPoint rho ^ 2 *
          Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
              ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2))))).re =
        ((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2) *
          (Cvs.ZeroCounting.zPoint rho ^ 2 *
            Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
              (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
                ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re := by
      rw [show ((mi : ℂ) ^ 2 - (mj : ℂ) ^ 2) =
          ((((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [Complex.sub_re, h1, h2, h3] at hre
    linear_combination (Cvs.Criterion.divisorWeight rho : ℝ) * hre
  rw [tsum_congr hterm, tsum_mul_left]
  set T : ℝ := ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
    (Cvs.ZeroCounting.zPoint rho ^ 2 *
      Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
        (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
          ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re
  field_simp
  ring

/-- Zero-side closed form of `flatPairEntry` when `(mode N j).natAbs < (mode N i).natAbs`,
exhibiting the exact `ω_j² / ((ω_i² − z_ρ²)(ω_j² − z_ρ²))` kernel. -/
theorem flatPairEntry_eq_zeroSide {L : ℝ} (hL : 0 < L) (N : ℕ)
    {i j : Idx N} (hij : (mode N j).natAbs < (mode N i).natAbs) :
    Cvs.Finite.EvenPairCancellation.flatPairEntry ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L N i j =
      (4 / L) * ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
        ((((2 * π * mode N j / L : ℝ) : ℂ) ^ 2 *
          Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2) /
            (((((2 * π * mode N i / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
              ((((2 * π * mode N j / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re := by
  set mi : ℤ := mode N i
  set mj : ℤ := mode N j
  have hi0 : mi ≠ 0 := Int.natAbs_ne_zero.mp (by omega)
  have hmi : (mi : ℝ) ≠ 0 := by exact_mod_cast hi0
  have habs : |(mj : ℝ)| < |(mi : ℝ)| := by
    have h : (mj.natAbs : ℝ) < (mi.natAbs : ℝ) := by exact_mod_cast hij
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hsq : (mi : ℝ) ^ 2 - (mj : ℝ) ^ 2 ≠ 0 := by
    have hpos : (mj : ℝ) ^ 2 < (mi : ℝ) ^ 2 := by
      rw [← sq_abs (mj : ℝ), ← sq_abs (mi : ℝ)]
      exact sq_lt_sq.mpr (by rwa [abs_abs, abs_abs])
    linarith
  have hL0 : L ≠ 0 := hL.ne'
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Cvs.Finite.EvenPairCancellation.flatPairEntry_closed hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ N hij,
    Cvs.StepA.WindowGeneratorZeros.gen_eq_zeroSide_int hL mj, Cvs.StepA.WindowGeneratorZeros.gen_eq_zeroSide_int hL mi]
  change ((mi : ℝ) * (mj : ℝ) * (8 * π * (mj : ℝ) / L * _) -
      (mj : ℝ) ^ 2 * (8 * π * (mi : ℝ) / L * _)) /
      (2 * π * (mi : ℝ) * ((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2)) = _
  have h1 : (mi : ℝ) * (mj : ℝ) * (8 * π * (mj : ℝ) / L *
      ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
        (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) =
      (8 * π * (mi : ℝ) / L) * ∑' rho : nonTrivialZeroSet, (mj : ℝ) ^ 2 *
        ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) := by
    rw [tsum_mul_left]
    ring
  have h2 : (mj : ℝ) ^ 2 * (8 * π * (mi : ℝ) / L *
      ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
        (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) =
      (8 * π * (mi : ℝ) / L) * ∑' rho : nonTrivialZeroSet, (mj : ℝ) ^ 2 *
        ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) := by
    rw [tsum_mul_left]
    ring
  have hsum_i : Summable fun rho : nonTrivialZeroSet => (mj : ℝ) ^ 2 *
      ((Cvs.Criterion.divisorWeight rho : ℝ) *
        (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) :=
    (Cvs.StepA.WindowGeneratorZeros.summable_genTerm hL hi0).mul_left ((mj : ℝ) ^ 2)
  rw [h1, h2, ← mul_sub, ← (summable_sq_mul_genTerm hL mj).tsum_sub hsum_i]
  have hterm : ∀ rho : nonTrivialZeroSet,
      (mj : ℝ) ^ 2 * ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) -
        (mj : ℝ) ^ 2 * ((Cvs.Criterion.divisorWeight rho : ℝ) *
          (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
            (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re) =
      ((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2) *
        ((Cvs.Criterion.divisorWeight rho : ℝ) *
          ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 *
            Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2) /
              (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
                ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re) := by
    intro rho
    have hre := congrArg Complex.re (flatPair_zeroTerm_sub_eq hL mi mj (Cvs.ZeroCounting.zPoint rho))
    have hc1 : (((mj : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
        (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re =
        (mj : ℝ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
      rw [show (mj : ℂ) ^ 2 = (((mj : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have hc2 : (((mj : ℂ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
        (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re =
        (mj : ℝ) ^ 2 * (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2 /
          (((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)).re := by
      rw [show (mj : ℂ) ^ 2 = (((mj : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have hc3 : ((((mi : ℂ) ^ 2 - (mj : ℂ) ^ 2)) *
        ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 *
          Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2) /
            (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
              ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2))))).re =
        ((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2) *
          ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 *
            Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2) /
              (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
                ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re := by
      rw [show ((mi : ℂ) ^ 2 - (mj : ℂ) ^ 2) =
          ((((mi : ℝ) ^ 2 - (mj : ℝ) ^ 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [Complex.sub_re, hc1, hc2, hc3] at hre
    linear_combination (Cvs.Criterion.divisorWeight rho : ℝ) * hre
  rw [tsum_congr hterm, tsum_mul_left]
  set T : ℝ := ∑' rho : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ) *
    ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 *
      Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2) /
        (((((2 * π * mi / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)) *
          ((((2 * π * mj / L : ℝ) : ℂ) ^ 2 - Cvs.ZeroCounting.zPoint rho ^ 2)))).re
  field_simp
  ring

end Cvs.Finite.LoewnerFoldedDiagonal
