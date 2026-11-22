import Mathlib
import Cvs.Finite.CosineModeTransformBounds
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-!
# The odd sector's universal function: sine sums are the same zero-side Gram
The sine mode's window transform is `ω(1 − e^{−iξL})/(ω² − ξ²)`, so a sine polynomial's square
transform is `4 sin²(ξL/2)·S_odd(ξ)²`, `S_odd(ξ) = ∑ o_k ω_k/(ω_k² − ξ²) = L·R_odd(Lξ)`. With
`Cvs.Finite.OddSectorZeroSide`'s zero side and `Cvs.Finite.OddSectorSineSums`'s matrix form, `o ⬝ᵥ M_L o = L·∑_ρ m_ρ·Re G_o(L z_ρ)` with
`G_o(u) = 4 sin²(u/2) R_odd(u)²` for odd `o`: the odd sector is the zero measure paired with its
own universal function, without the even sector's `u²`. Both sectors now share one measure.
-/

noncomputable section

open Real Complex Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.OddUniversalFunction
open Cvs.ZeroCounting

/-! ### The sine mode transform -/

/-- The antiderivative of `e^{−isξ} sin(ωs)`. -/
def sinAnti (ω : ℝ) (ξ : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (-((s : ℂ) * ξ) * I) * (-I * ξ * (Real.sin (ω * s) : ℂ) - (ω : ℂ) * (Real.cos (ω * s) : ℂ))
    / ((ω : ℂ) ^ 2 - ξ ^ 2)

theorem hasDerivAt_sinAnti (ω : ℝ) {ξ : ℂ} (hξ : (ω : ℂ) ^ 2 - ξ ^ 2 ≠ 0) (s : ℝ) :
    HasDerivAt (sinAnti ω ξ)
      (Complex.exp (-((s : ℂ) * ξ) * I) * (Real.sin (ω * s) : ℂ)) s := by
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I))
      (Complex.exp (-((s : ℂ) * ξ) * I) * (-ξ * I)) s := by
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * ξ) * I) (-ξ * I) s := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ξ).neg.mul_const I
      simpa using this
    exact (Complex.hasDerivAt_exp _).comp s h1
  have hcos : HasDerivAt (fun s : ℝ => (Real.cos (ω * s) : ℂ))
      (((-Real.sin (ω * s) * ω : ℝ) : ℂ)) s := by
    have h := ((hasDerivAt_mul_const ω).cos (x := s))
    have h' : HasDerivAt (fun y => Real.cos (ω * y)) (-Real.sin (ω * s) * ω) s := by
      simpa [mul_comm] using h
    exact h'.ofReal_comp
  have hsin : HasDerivAt (fun s : ℝ => (Real.sin (ω * s) : ℂ))
      (((Real.cos (ω * s) * ω : ℝ) : ℂ)) s := by
    have h := ((hasDerivAt_mul_const ω).sin (x := s))
    have h' : HasDerivAt (fun y => Real.sin (ω * y)) (Real.cos (ω * s) * ω) s := by
      simpa [mul_comm] using h
    exact h'.ofReal_comp
  have hin : HasDerivAt (fun s : ℝ => -I * ξ * (Real.sin (ω * s) : ℂ) - (ω : ℂ) * (Real.cos (ω * s) : ℂ))
      (-I * ξ * (((Real.cos (ω * s) * ω : ℝ) : ℂ)) - (ω : ℂ) * (((-Real.sin (ω * s) * ω : ℝ) : ℂ))) s :=
    (hsin.const_mul _).sub (hcos.const_mul _)
  have hprod := (hexp.mul hin).div_const ((ω : ℂ) ^ 2 - ξ ^ 2)
  refine hprod.congr_deriv ?_
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem windowTransform_sin_eq {L : ℝ} (ω : ℝ) {ξ : ℂ} (hξ : (ω : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.windowTransform L (cf fun y => Real.sin (ω * y)) ξ
      = sinAnti ω ξ L - sinAnti ω ξ 0 := by
  unfold Cvs.Detection.windowTransform
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_sinAnti ω hξ s) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine Continuous.continuousOn ?_
  unfold cf
  fun_prop

/-- **The window transform of a sine mode, in closed form.** -/
theorem windowTransform_sin_eq_of_int {L : ℝ} (hL : 0 < L) (m : ℤ) {ξ : ℂ}
    (hξ : ((2 * π * m / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.windowTransform L (cf fun y => Real.sin (2 * π * m / L * y)) ξ
      = ((2 * π * m / L : ℝ) : ℂ) * (1 - Complex.exp (-((L : ℂ) * ξ) * I))
        / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - ξ ^ 2) := by
  rw [windowTransform_sin_eq _ hξ]
  unfold sinAnti
  have hcos : Real.cos (2 * π * m / L * L) = 1 := by
    rw [show 2 * π * m / L * L = (m : ℝ) * (2 * π) by rw [div_mul_cancel₀ _ hL.ne']; ring,
      Real.cos_int_mul_two_pi]
  have hsin : Real.sin (2 * π * m / L * L) = 0 := by
    rw [show 2 * π * m / L * L = ((2 * m : ℤ) : ℝ) * π by
      push_cast; rw [div_mul_cancel₀ _ hL.ne']; ring, Real.sin_int_mul_pi]
  rw [hcos, hsin]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul, mul_one, add_zero, neg_zero, Complex.exp_zero, one_mul, zero_sub, sub_zero]
  field_simp
  ring

/-! ### The odd universal function -/

variable {ι : Type*} [Fintype ι]

/-- The odd rational factor at scale `L`. -/
def Sodd (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (ξ : ℂ) : ℂ :=
  ∑ k, (o k : ℂ) * ((2 * π * mode k / L : ℝ) : ℂ) / (((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2)

/-- The odd universal rational factor, in the dilated variable. -/
def Rodd (mode : ι → ℤ) (o : ι → ℝ) (u : ℂ) : ℂ :=
  ∑ k, (o k : ℂ) * ((2 * π * mode k : ℝ) : ℂ) / (((2 * π * mode k : ℝ) : ℂ) ^ 2 - u ^ 2)

/-- The odd universal function `G(u) = 4 sin²(u/2) R_odd(u)²`. -/
def G (mode : ι → ℤ) (o : ι → ℝ) (u : ℂ) : ℂ :=
  4 * Complex.sin (u / 2) ^ 2 * Rodd mode o u ^ 2

theorem Sodd_neg (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (ξ : ℂ) : Sodd L mode o (-ξ) = Sodd L mode o ξ := by
  unfold Sodd; simp only [neg_sq]

/-- **The transform of a sine polynomial.** -/
theorem transform_sinePoly_eq {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) {ξ : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.windowTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L mode o)) ξ
      = (1 - Complex.exp (-((L : ℂ) * ξ) * I)) * Sodd L mode o ξ := by
  unfold Cvs.Finite.OddSectorZeroSide.sinePoly
  rw [Cvs.Finite.CosineModeTransformBounds.windowTransform_sum_cf L o
    (fun k y => Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode k * y)) (fun k => by fun_prop) ξ]
  unfold Sodd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := windowTransform_sin_eq_of_int hL (mode k) (hgen k)
  unfold Cvs.Finite.TruncationZeroFreeOffAxes.omega
  rw [h]
  field_simp

/-- **The square transform of a sine polynomial is `4 sin²(ξL/2)·S_odd(ξ)²`.** -/
theorem sqTransform_sinePoly_eq {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) {ξ : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.sqTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L mode o)) ξ
      = 4 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 * Sodd L mode o ξ ^ 2 := by
  have hgen' : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (-ξ) ^ 2 ≠ 0 := by
    intro k; rw [neg_sq]; exact hgen k
  unfold Cvs.Detection.sqTransform
  rw [transform_sinePoly_eq hL mode o hgen, transform_sinePoly_eq hL mode o hgen', Sodd_neg]
  have hcos : Complex.exp (-((L : ℂ) * ξ) * I) + Complex.exp (((L : ℂ) * ξ) * I)
      = 2 * Complex.cos ((L : ℂ) * ξ) := by
    rw [Complex.two_cos]; ring_nf
  have hsin : Complex.cos ((L : ℂ) * ξ) = 1 - 2 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 := by
    have := Complex.cos_two_mul ((L : ℂ) * ξ / 2)
    rw [show 2 * ((L : ℂ) * ξ / 2) = (L : ℂ) * ξ by ring] at this
    rw [this, Complex.cos_sq']
    ring
  have hexp : Complex.exp (-((L : ℂ) * -ξ) * I) = Complex.exp (((L : ℂ) * ξ) * I) := by
    ring_nf
  rw [hexp]
  have hprod : Complex.exp (-((L : ℂ) * ξ) * I) * Complex.exp (((L : ℂ) * ξ) * I) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  have key : (1 - Complex.exp (-((L : ℂ) * ξ) * I)) * (1 - Complex.exp (((L : ℂ) * ξ) * I))
      = 4 * Complex.sin ((L : ℂ) * ξ / 2) ^ 2 := by
    have e1 : (1 - Complex.exp (-((L : ℂ) * ξ) * I)) * (1 - Complex.exp (((L : ℂ) * ξ) * I))
        = 1 - (Complex.exp (-((L : ℂ) * ξ) * I) + Complex.exp (((L : ℂ) * ξ) * I))
          + Complex.exp (-((L : ℂ) * ξ) * I) * Complex.exp (((L : ℂ) * ξ) * I) := by ring
    rw [e1, hprod, hcos, hsin]
    ring
  calc (1 - Complex.exp (-((L : ℂ) * ξ) * I)) * Sodd L mode o ξ
        * ((1 - Complex.exp (((L : ℂ) * ξ) * I)) * Sodd L mode o ξ)
      = ((1 - Complex.exp (-((L : ℂ) * ξ) * I)) * (1 - Complex.exp (((L : ℂ) * ξ) * I)))
          * Sodd L mode o ξ ^ 2 := by ring
    _ = _ := by rw [key]

/-- **The scale enters only through the dilated variable**: `S_odd(ξ) = L·R_odd(Lξ)`. -/
theorem Sodd_eq_Rodd {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) (ξ : ℂ) :
    Sodd L mode o ξ = (L : ℂ) * Rodd mode o ((L : ℂ) * ξ) := by
  unfold Sodd Rodd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

theorem sqTransform_sinePoly_eq_G {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) {ξ : ℂ}
    (hgen : ∀ k, ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.sqTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L mode o)) ξ
      = ((L : ℂ)) ^ 2 * G mode o ((L : ℂ) * ξ) := by
  rw [sqTransform_sinePoly_eq hL mode o hgen, Sodd_eq_Rodd hL]
  unfold G
  ring

/-- **The odd CvS form is the zero measure paired with the odd universal function**:
`o ⬝ᵥ M_L o = L·∑_ρ m_ρ·Re G_o(L·z_ρ)` for odd `o`, injective modes and generic `L`. -/
theorem quadForm_odd_eq_universal [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0) :
    o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ o)
      = L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (G mode o ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
  have h := Cvs.Finite.OddSectorZeroSide.zeroSide_sineSum hL mode o 0 0
  rw [Cvs.Finite.OddSectorSineSums.weilForm_sineSum_eq_ddMatrix hL _ _ hinj hinv hmode hodd] at h
  unfold Cvs.ZeroCounting.kernelZeroSide at h
  have hsum : ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Detection.sqTransform L (cf (Cvs.Finite.OddSectorZeroSide.sinePoly L mode o))
          (Cvs.ZeroCounting.zPoint rho)).re
      = L ^ 2 * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (G mode o ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
    rw [← tsum_mul_left]
    refine tsum_congr fun rho => ?_
    rw [sqTransform_sinePoly_eq_G hL mode o (hgen rho)]
    have : (((L : ℂ)) ^ 2 * G mode o ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re
        = L ^ 2 * (G mode o ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
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
  have : L * (o ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix
          (fun k => Cvs.Finite.PairFormDividedDifference.aval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (fun k => Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ o))
      = L * (L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (G mode o ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re) := by
    rw [← h]; ring
  exact mul_left_cancel₀ hL' this

end Cvs.Finite.OddUniversalFunction
