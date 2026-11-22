import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.CutModeLevySeries
import Cvs.Finite.DiagonalCutSymbol
import Cvs.Finite.DiagonalLevySymbol
import Cvs.Finite.GeneratorClosedForm
import Cvs.Finite.LevyChannelDoubleSum
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.OneModeEntries
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.PairPoleChannelClosed
import Cvs.Finite.TruncationQuadraticForm
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.TrigammaSeries

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window matrix in closed form: digamma, trigamma, and one generator

Every entry of the CvS matrix `Cvs.Finite.TruncationQuadraticForm.M` is an explicit function of `Re ψ`, `Im ψ` and `Re ψ'` at
`1/4 + iπm/L`, a finite prime sum, and a series geometric in `e^{−2L}`.
-/

namespace Cvs.Finite.WindowMatrixClosedForm

open Real
open Complex (I)
open Cvs.Finite.DiagonalLevySymbol (cutTerm tailFactor)
open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf (imTerm archSymbolIm)
open Cvs.Finite.OneModeEntries Cvs.Finite.DiagonalCutSymbol

/-- The trigamma argument `1/4 + i y`. -/
noncomputable def zq (y : ℝ) : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I

theorem zq_re (y : ℝ) : (zq y).re = 1 / 4 := by simp [zq]

theorem zq_mem (y : ℝ) : zq y ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have h := congrArg Complex.re hn
  rw [zq_re, Complex.intCast_re] at h
  have h4 : ((4 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have : (4 * n : ℤ) = 1 := by exact_mod_cast h4
  omega

/-- The cut term is the real part of `1/(z + k)²` at `z = 1/4 + iπm/L`. -/
theorem cutTerm_eq_re (L : ℝ) (m : ℤ) (k : ℕ) :
    cutTerm L m k = (1 / (zq (π * m / L) + k) ^ 2).re := by
  unfold cutTerm zq
  set a : ℝ := 1 / 4 + (k : ℝ) with ha
  set y : ℝ := π * m / L with hy
  have hz : (1 / 4 : ℂ) + (y : ℂ) * I + (k : ℂ) = ((a : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [ha]; push_cast; ring_nf
  rw [hz]
  have ha0 : 0 < a := by rw [ha]; positivity
  have hne : ((a : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hpos : (a ^ 2 + y ^ 2) ^ 2 ≠ 0 := by positivity
  have hinv : 1 / (((a : ℝ) : ℂ) + (y : ℂ) * I) ^ 2
      = (((a ^ 2 - y ^ 2) / (a ^ 2 + y ^ 2) ^ 2 : ℝ) : ℂ)
        + (((-2 * a * y) / (a ^ 2 + y ^ 2) ^ 2 : ℝ) : ℂ) * I := by
    rw [div_eq_iff (pow_ne_zero 2 hne)]
    apply Complex.ext
    · simp only [Complex.one_re, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, sq,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, zero_sub]
      field_simp
      ring
    · simp only [Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, sq,
        mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, zero_sub]
      field_simp
      ring
  rw [hinv]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- **The cut sum is the real part of the trigamma** at `1/4 + iπm/L`. -/
theorem hasSum_cutTerm (L : ℝ) (m : ℤ) :
    HasSum (cutTerm L m) (deriv Complex.digamma (zq (π * m / L))).re := by
  have h := Complex.hasSum_re (Cvs.Zeta.Base.Stirling.hasSum_trigamma (zq_mem (π * m / L)))
  have hf : (fun k : ℕ => (1 / (zq (π * m / L) + k) ^ 2).re) = cutTerm L m :=
    funext fun k => (cutTerm_eq_re L m k).symm
  rwa [hf] at h

theorem tsum_cutTerm (L : ℝ) (m : ℤ) :
    ∑' k, cutTerm L m k = (deriv Complex.digamma (zq (π * m / L))).re :=
  (hasSum_cutTerm L m).tsum_eq

/-- **The diagonal Lévy pairing in closed form**: digamma, trigamma, and a geometric remainder. -/
theorem levyPair_diag_closed {L : ℝ} (hL : 0 < L) (m : ℤ) :
    Cvs.Finite.LevyChannelDoubleSum.levyPair L m m
      = 2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * m / L) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        + 1 / L * (deriv Complex.digamma (zq (π * m / L))).re
        - 1 / L * ∑' k, tailFactor L k * cutTerm L m k := by
  rw [Cvs.Finite.DiagonalLevySymbol.levyPair_diag_eq_symbol hL m, tsum_cutTerm]

theorem summable_tail_imTerm {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    Summable fun k => tailFactor L k * imTerm ω k := by
  refine Summable.of_norm_bounded (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.summable_imTerm ω).norm fun k => ?_
  have h0 : 0 ≤ tailFactor L k := (Real.exp_pos _).le
  rw [norm_mul, Real.norm_of_nonneg h0]
  have h1 : tailFactor L k ≤ 1 := by
    unfold tailFactor
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (1 / 4 + (k : ℝ)) * (2 * L) := by positivity
    linarith
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- The sine Lévy series is the symbol's imaginary half, less a geometric remainder. -/
theorem tsum_levySin {L : ℝ} (hL : 0 < L) (ω : ℝ) :
    ∑' k, levySin L ω k = -archSymbolIm ω + ∑' k, tailFactor L k * imTerm ω k := by
  have hterm : ∀ k, levySin L ω k = -imTerm ω k + tailFactor L k * imTerm ω k := by
    intro k
    simp only [levySin, imTerm, tailFactor, Cvs.Finite.CutModeLevySeries.cq]
    ring
  rw [tsum_congr hterm,
    Summable.tsum_add (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.summable_imTerm ω).neg (summable_tail_imTerm hL ω),
    tsum_neg, (Cvs.WeilForm.Archimedean.SymbolImaginaryHalf.hasSum_imTerm ω).tsum_eq]

/-- cvsnum's off-diagonal generator `F`. -/
noncomputable def gen (P R : ℕ) (L : ℝ) (m : ℤ) : ℝ :=
  2 * poleSin L (2 * π * m / L) - archSymbolIm (2 * π * m / L)
    + ∑' j, tailFactor L j * imTerm (2 * π * m / L) j
    - primeSum P R (sinCut L (2 * π * m / L))

theorem bval_eq_gen (P R : ℕ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    Cvs.Finite.PairFormDividedDifference.bval P R L k = -(gen P R L k) / L := by
  rw [Cvs.Finite.GeneratorClosedForm.bval_closed P R hL k, tsum_levySin hL]
  unfold gen
  ring

/-- **Off the diagonal, the window matrix is the Loewner matrix of `gen`.** -/
theorem pairQ_off_closed {L : ℝ} (hL : 0 < L) (P R : ℕ) {m n : ℤ} (hmn : m ≠ n) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L m n / 2
      = (gen P R L m - gen P R L n) / (2 * π * ((n : ℝ) - m)) := by
  rw [Cvs.Finite.PairFormDividedDifference.pairQ_off hL P R hmn, bval_eq_gen P R hL, bval_eq_gen P R hL]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hL' : L ≠ 0 := hL.ne'
  have hnm : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  have hmn' : ((m : ℝ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hden : 2 * π * m / L - 2 * π * n / L = 2 * π * ((m : ℝ) - n) / L := by ring
  rw [hden]
  field_simp
  ring

/-- The diagonal of the prime pairing through the cut cosine sums. -/
theorem primePair_diag (P R : ℕ) (L : ℝ) (m : ℤ) :
    Cvs.Finite.ModeSumPairValues.primePair P R L m m
      = 2 * primeSum P R (cosCut L (2 * π * m / L))
        - 2 / L * primeSum P R (vcosCut L (2 * π * m / L)) := by
  unfold Cvs.Finite.ModeSumPairValues.primePair primeSum
  rw [Kc_diag_eq]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem K_self_zero (L : ℝ) (m : ℤ) : Cvs.Finite.CosineModeOverlap.K L m m 0 = 2 := by
  simp [Cvs.Finite.CosineModeOverlap.K]

/-- cvsnum's diagonal entry `Diag`. -/
noncomputable def diag (P R : ℕ) (L : ℝ) (m : ℤ) : ℝ :=
  (2 * (2 / L * (1 / 4 - Cvs.Finite.PairPoleChannelClosed.freq L m ^ 2) * Cvs.Finite.PairPoleChannelClosed.poleFactor L
          / (1 / 4 + Cvs.Finite.PairPoleChannelClosed.freq L m ^ 2) ^ 2)
    + 2 * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
    + (2 * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * m / L) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        + 1 / L * (deriv Complex.digamma (zq (π * m / L))).re
        - 1 / L * ∑' k, tailFactor L k * cutTerm L m k)
    - (2 * primeSum P R (cosCut L (2 * π * m / L))
        - 2 / L * primeSum P R (vcosCut L (2 * π * m / L)))) / 2

/-- **On the diagonal, the window matrix is `diag`.** -/
theorem pairQ_diag_closed {L : ℝ} (hL : 0 < L) (P R : ℕ) (m : ℤ) :
    Cvs.Finite.ModeSumPairValues.pairQ P R L m m / 2 = diag P R L m := by
  unfold Cvs.Finite.ModeSumPairValues.pairQ diag
  rw [Cvs.Finite.PairPoleChannelClosed.polePair_diag hL m, K_self_zero, levyPair_diag_closed hL m,
    primePair_diag]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The CvS matrix in closed form**, entry by entry: cvsnum's `pair_entry`. -/
theorem M_apply_closed {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ}
    (hinj : Function.Injective mode) (i j : ι) :
    Cvs.Finite.TruncationQuadraticForm.M P R L mode i j
      = if i = j then diag P R L (mode i)
        else (gen P R L (mode i) - gen P R L (mode j))
          / (2 * π * ((mode j : ℝ) - mode i)) := by
  rw [Cvs.Finite.TruncationQuadraticForm.M_apply hL P R hinj i j]
  by_cases hij : i = j
  · subst hij; simp [pairQ_diag_closed hL P R]
  · rw [if_neg hij]
    exact pairQ_off_closed hL P R (fun h => hij (hinj h))

end Cvs.Finite.WindowMatrixClosedForm
