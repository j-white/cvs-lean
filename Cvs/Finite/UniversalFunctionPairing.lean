import Mathlib
import Cvs.Finite.CosineModeTransform
import Cvs.Finite.CosineModeTransformBounds
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-!
# The CvS quadratic form is the zero measure paired with one universal function
With `Cvs.Finite.CosineModeTransform`'s closed form `W_k(ξ) = −iξ(e^{−iξL} − 1)/(ω_k² − ξ²)` the transform of a cosine
polynomial is `−iξ(e^{−iξL} − 1)·S(ξ)`, `S(ξ) = ∑ xi_k/(ω_k² − ξ²)`, and its square transform is
`4ξ² sin²(ξL/2)·S(ξ)²`. Since `S(ξ) = L²·R(Lξ)` with `R(u) = ∑ xi_k/((2πk)² − u²)`, `Cvs.Finite.ZeroSideGramMatrix`'s
zero-side identity reads `xiᵀ·M_L·xi = L·∑_ρ m_ρ·Re F(L·z_ρ)`, `F(u) = 4u² sin²(u/2) R(u)²`:
the same entire function `F`, fixed by the coefficients alone, sampled at the dilated zeros.
-/

noncomputable section

open Real Filter Topology Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.UniversalFunctionPairing
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- The rational factor of a cosine polynomial's transform. -/
def S (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (ξ : ℂ) : ℂ :=
  ∑ k, (xi k : ℂ) / (((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2)

/-- The universal rational factor, in the dilated variable `u = Lξ`. -/
def R (mode : ι → ℤ) (xi : ι → ℝ) (u : ℂ) : ℂ :=
  ∑ k, (xi k : ℂ) / (((2 * π * mode k : ℝ) : ℂ) ^ 2 - u ^ 2)

/-- The universal function: `4u² sin²(u/2) R(u)²`. -/
def F (mode : ι → ℤ) (xi : ι → ℝ) (u : ℂ) : ℂ :=
  4 * u ^ 2 * Complex.sin (u / 2) ^ 2 * R mode xi u ^ 2

theorem S_neg (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (ξ : ℂ) : S L mode xi (-ξ) = S L mode xi ξ := by
  unfold S; simp only [neg_sq]

/-- **The transform of a cosine polynomial**, off the mode frequencies. -/
theorem transform_cosPoly_eq {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) {ξ : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) ξ
      = -Complex.I * ξ * (Complex.exp (-((L : ℂ) * ξ) * Complex.I) - 1) * S L mode xi ξ := by
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly
  rw [Cvs.Finite.CosineModeTransformBounds.windowTransform_sum_cf L xi
    (fun k y => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode k * y)) (fun k => by fun_prop) ξ]
  unfold S
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := Cvs.Finite.CosineModeTransform.windowTransform_cos_eq_of_int hL (mode k) (hgen k)
  unfold Cvs.Finite.TruncationZeroFreeOffAxes.omega
  rw [h]
  field_simp

/-- **The square transform of a cosine polynomial** is `4ξ² sin²(ξL/2) S(ξ)²`. -/
theorem sqTransform_cosPoly_eq {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) {ξ : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) ξ
      = 4 * ξ ^ 2 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 * S L mode xi ξ ^ 2 := by
  have hgen' : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (-ξ) ^ 2 ≠ 0 := by
    intro k; rw [neg_sq]; exact hgen k
  unfold Cvs.Detection.sqTransform
  rw [transform_cosPoly_eq hL mode xi hgen, transform_cosPoly_eq hL mode xi hgen', S_neg]
  -- `(e^{-w} - 1)(e^{w} - 1) = 2 - 2cos(Lξ) = 4 sin²(Lξ/2)`
  have hcos : Complex.exp (-((L : ℂ) * ξ) * Complex.I) + Complex.exp (((L : ℂ) * ξ) * Complex.I)
      = 2 * Complex.cos ((L : ℂ) * ξ) := by
    rw [Complex.two_cos]; ring_nf
  have hsin : Complex.cos ((L : ℂ) * ξ) = 1 - 2 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 := by
    have := Complex.cos_two_mul ((L : ℂ) * ξ / 2)
    rw [show 2 * ((L : ℂ) * ξ / 2) = (L : ℂ) * ξ by ring] at this
    rw [this, Complex.cos_sq']
    ring
  have hexp : Complex.exp (-((L : ℂ) * -ξ) * Complex.I) = Complex.exp (((L : ℂ) * ξ) * Complex.I) := by
    ring_nf
  rw [hexp]
  have key : (Complex.exp (-((L : ℂ) * ξ) * Complex.I) - 1)
      * (Complex.exp (((L : ℂ) * ξ) * Complex.I) - 1)
      = 4 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 := by
    have hprod : Complex.exp (-((L : ℂ) * ξ) * Complex.I)
        * Complex.exp (((L : ℂ) * ξ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    have e1 : (Complex.exp (-((L : ℂ) * ξ) * Complex.I) - 1)
        * (Complex.exp (((L : ℂ) * ξ) * Complex.I) - 1)
        = Complex.exp (-((L : ℂ) * ξ) * Complex.I) * Complex.exp (((L : ℂ) * ξ) * Complex.I)
          - (Complex.exp (-((L : ℂ) * ξ) * Complex.I) + Complex.exp (((L : ℂ) * ξ) * Complex.I))
          + 1 := by ring
    rw [e1, hprod, hcos, hsin]
    ring
  calc -Complex.I * ξ * (Complex.exp (-((L : ℂ) * ξ) * Complex.I) - 1) * S L mode xi ξ
        * (-Complex.I * -ξ * (Complex.exp (((L : ℂ) * ξ) * Complex.I) - 1) * S L mode xi ξ)
      = (-Complex.I * -Complex.I * -1) * ξ ^ 2
          * ((Complex.exp (-((L : ℂ) * ξ) * Complex.I) - 1)
            * (Complex.exp (((L : ℂ) * ξ) * Complex.I) - 1)) * S L mode xi ξ ^ 2 := by ring
    _ = 4 * ξ ^ 2 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 * S L mode xi ξ ^ 2 := by
        rw [key, show -Complex.I * -Complex.I * -1 = (1 : ℂ) by
          rw [neg_mul_neg, Complex.I_mul_I]; ring]
        ring

/-- **The scale enters only through the dilated variable**: `S(ξ) = L²·R(Lξ)`. -/
theorem S_eq_R {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) (ξ : ℂ) :
    S L mode xi ξ = ((L : ℂ)) ^ 2 * R mode xi ((L : ℂ) * ξ) := by
  unfold S R
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

/-- **The square transform in the dilated variable**: `L²·F(Lξ)`. -/
theorem sqTransform_cosPoly_eq_F {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) {ξ : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) ξ
      = ((L : ℂ)) ^ 2 * F mode xi ((L : ℂ) * ξ) := by
  rw [sqTransform_cosPoly_eq hL mode xi hgen, S_eq_R hL]
  unfold F
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

/-- **The CvS quadratic form is the zero measure paired with the universal function**:
`xiᵀ·M_L·xi = L·∑_ρ m_ρ·Re F(L·z_ρ)`, for injective modes and generic `L`. -/
theorem quadForm_eq_universal [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0) :
    xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ xi)
      = L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
  have h := Cvs.Finite.ZeroSideGramMatrix.zeroSide_eq_ddMatrix hL hinj hinv hmode hxieven 0 0
  unfold Cvs.ZeroCounting.kernelZeroSide at h
  have hsum : ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi))
          (Cvs.ZeroCounting.zPoint rho)).re
      = L ^ 2 * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
    rw [← tsum_mul_left]
    refine tsum_congr fun rho => ?_
    rw [sqTransform_cosPoly_eq_F hL mode xi (hgen rho)]
    have : (((L : ℂ)) ^ 2 * F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re
        = L ^ 2 * (F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
      rw [show ((L : ℂ)) ^ 2 = ((L ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [this]; ring
  rw [hsum] at h
  have hM : Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode
      = Cvs.Finite.DividedDifferenceCommutator.ddMatrix
          (fun k => Cvs.Finite.PairFormDividedDifference.aval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (fun k => Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) := rfl
  rw [hM]
  have hL' : L ≠ 0 := hL.ne'
  have : L * (xi ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix
          (fun k => Cvs.Finite.PairFormDividedDifference.aval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (fun k => Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ xi))
      = L * (L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re) := by
    rw [← h]; ring
  exact mul_left_cancel₀ hL' this

end Cvs.Finite.UniversalFunctionPairing
