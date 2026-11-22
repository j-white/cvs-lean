import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTransformEnvelopes
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LogEnvelopeSquareSummable
import Cvs.Zeta.ZeroSideMoments

/-!
# The CvS bilinear form on even vectors is the zero-side pairing of two universal functions
Polarising `Cvs.Finite.UniversalFunctionPairing`: for even `x, x'`, `x ⬝ᵥ M_L x' = L·∑_ρ m_ρ·Re[Φ_x(L z_ρ)·Φ_{x'}(L z_ρ)]` with
`Φ_x(u) = 2u sin(u/2)·R_x(u)`, `R_x` linear in `x`; the zero side is summable outright, so the
polarisation is legitimate. Under RH the samples are real, so `x ⬝ᵥ M_L x = L·∑_ρ m_ρ·Φ_x(Lγ_ρ)²`
is a weighted sum of squares and `M_L` is positive semidefinite on even vectors: every entry of
the CvS matrix is an explicit sum over the zeros of one function of the dilated ordinates.
-/

noncomputable section

open Real Filter Topology Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.EvenBilinearZeroSide
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- The universal amplitude `Φ(u) = 2u sin(u/2) R(u)`, whose square is `F`. -/
def Phi (mode : ι → ℤ) (xi : ι → ℝ) (u : ℂ) : ℂ :=
  2 * u * Complex.sin (u / 2) * Cvs.Finite.UniversalFunctionPairing.R mode xi u

theorem two_mul_re (z : ℂ) : (2 * z).re = 2 * z.re := by
  rw [Complex.mul_re]; simp

theorem F_eq_Phi_sq (mode : ι → ℤ) (xi : ι → ℝ) (u : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.F mode xi u = Phi mode xi u ^ 2 := by
  unfold Cvs.Finite.UniversalFunctionPairing.F Phi; ring

theorem R_add (mode : ι → ℤ) (xi xi' : ι → ℝ) (u : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.R mode (xi + xi') u
      = Cvs.Finite.UniversalFunctionPairing.R mode xi u + Cvs.Finite.UniversalFunctionPairing.R mode xi' u := by
  unfold Cvs.Finite.UniversalFunctionPairing.R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

theorem Phi_add (mode : ι → ℤ) (xi xi' : ι → ℝ) (u : ℂ) :
    Phi mode (xi + xi') u = Phi mode xi u + Phi mode xi' u := by
  unfold Phi; rw [R_add]; ring

/-- **The zero side of a cosine polynomial is summable outright.** -/
theorem summable_zeroSide_cosPoly {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi))
            (Cvs.ZeroCounting.zPoint rho)).re := by
  obtain ⟨C, hC0, hC⟩ := Cvs.Finite.ModeTransformEnvelopes.exists_cosPoly_bound hL mode xi
  refine Summable.of_norm_bounded
    (Cvs.Zeta.LogEnvelopeSquareSummable.summable_divisorWeight_phi_sq.mul_left (C ^ 2)) fun rho => ?_
  set z := Cvs.ZeroCounting.zPoint rho with hz
  have hz1 := Cvs.Finite.ZeroSideGramMatrix.zPoint_im_le rho
  have hz2 := Cvs.Finite.ZeroSideGramMatrix.neg_zPoint_im_le rho
  have hzre : z.re = ((rho : ℂ)).im := Cvs.Finite.ZeroSideGramMatrix.zPoint_re rho
  have hre0 : 0 ≤ |z.re| := abs_nonneg _
  have hphi1 := Cvs.Zeta.LogEnvelopeSquareSummable.one_div_le_phi hre0
  have hw : (0:ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
  have hb : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → |ξ.re| = |z.re| →
      ‖Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) ξ‖
        ≤ C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re| := by
    intro ξ hξ hre
    refine (hC ξ hξ).trans ?_
    rw [hre, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hphi1 hC0
  have h1 := hb z hz1 rfl
  have h2 := hb (-z) hz2 (by rw [Complex.neg_re, abs_neg])
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast,
    show C ^ 2 * ((Cvs.Criterion.divisorWeight rho : ℝ)
      * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2)
      = (Cvs.Criterion.divisorWeight rho : ℝ)
        * (C ^ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ hw
  calc |(Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) z).re|
      ≤ ‖Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) z‖ :=
        Complex.abs_re_le_norm _
    _ = ‖Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) z‖
        * ‖Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) (-z)‖ := by
        unfold Cvs.Detection.sqTransform; rw [norm_mul]
    _ ≤ (C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re|) * (C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re|) :=
        mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg hC0 (Cvs.Zeta.LogEnvelopeSquareSummable.phi_nonneg hre0))
    _ = C ^ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2 := by rw [hzre]; ring

/-- The universal zero side is summable, for generic `L`. -/
theorem summable_universal {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Finite.UniversalFunctionPairing.F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
  have h := (summable_zeroSide_cosPoly hL mode xi).mul_left (1 / L ^ 2)
  refine h.congr fun rho => ?_
  rw [Cvs.Finite.UniversalFunctionPairing.sqTransform_cosPoly_eq_F hL mode xi (hgen rho)]
  rw [show ((L : ℂ)) ^ 2 = ((L ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  have : L ^ 2 ≠ 0 := by positivity
  field_simp

/-- **The bilinear form on even vectors is the zero pairing of the universal amplitudes.** -/
theorem bilinear_eq_universal [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi xi' : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hxieven' : ∀ i, xi' (neg i) = xi' i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0) :
    xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ xi')
      = L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (Phi mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)
              * Phi mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
  set M := Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode with hM
  set P := ⌈Real.exp L⌉₊
  set Rr := ⌈L / Real.log 2⌉₊
  have hsym : xi' ⬝ᵥ (M *ᵥ xi) = xi ⬝ᵥ (M *ᵥ xi') := by
    have hMT : Mᵀ = M := by
      ext i j; rw [Matrix.transpose_apply, hM]; exact Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ hinj j i
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hMT, dotProduct_comm]
  have hQ := Cvs.Finite.UniversalFunctionPairing.quadForm_eq_universal hL hinj hinv hmode
    (xi := xi + xi') (fun i => by simp only [Pi.add_apply, hxieven, hxieven']) hgen
  have hQ1 := Cvs.Finite.UniversalFunctionPairing.quadForm_eq_universal hL hinj hinv hmode hxieven hgen
  have hQ2 := Cvs.Finite.UniversalFunctionPairing.quadForm_eq_universal hL hinj hinv hmode hxieven' hgen
  rw [← hM] at hQ hQ1 hQ2
  -- the matrix side
  have hexp : (xi + xi') ⬝ᵥ (M *ᵥ (xi + xi'))
      = xi ⬝ᵥ (M *ᵥ xi) + xi' ⬝ᵥ (M *ᵥ xi') + 2 * (xi ⬝ᵥ (M *ᵥ xi')) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym]; ring
  -- the zero side
  have hs1 := summable_universal hL mode xi hgen
  have hs2 := summable_universal hL mode xi' hgen
  have hcross : Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (2 * (Phi mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)
          * Phi mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho))).re := by
    have := ((summable_universal hL mode (xi + xi') hgen).sub hs1).sub hs2
    refine this.congr fun rho => ?_
    rw [F_eq_Phi_sq, F_eq_Phi_sq, F_eq_Phi_sq, Phi_add]
    simp only [← mul_sub, ← Complex.sub_re]
    congr 2
    ring
  have hzero : ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Finite.UniversalFunctionPairing.F mode (xi + xi') ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re
      = (∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Cvs.Finite.UniversalFunctionPairing.F mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re)
        + (∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Cvs.Finite.UniversalFunctionPairing.F mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re)
        + 2 * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Phi mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)
            * Phi mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)).re := by
    rw [← tsum_mul_left, ← hs1.tsum_add hs2, ← (hs1.add hs2).tsum_add (hcross.congr fun rho => by
      rw [two_mul_re]; ring)]
    · refine tsum_congr fun rho => ?_
      rw [F_eq_Phi_sq, F_eq_Phi_sq, F_eq_Phi_sq, Phi_add]
      have : (Phi mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)
          + Phi mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)) ^ 2
          = Phi mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho) ^ 2
            + Phi mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho) ^ 2
            + 2 * (Phi mode xi ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)
              * Phi mode xi' ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)) := by ring
      rw [this, Complex.add_re, Complex.add_re, two_mul_re]
      ring
  rw [hexp, hQ1, hQ2, hzero] at hQ
  linarith [hQ]

/-! ### Under the hypothesis, a sum of squares -/

/-- The real amplitude at a real argument. -/
def phiR (mode : ι → ℤ) (xi : ι → ℝ) (t : ℝ) : ℝ :=
  2 * t * Real.sin (t / 2) * ∑ k, xi k / ((2 * π * mode k) ^ 2 - t ^ 2)

theorem Phi_ofReal (mode : ι → ℤ) (xi : ι → ℝ) (t : ℝ) :
    Phi mode xi (t : ℂ) = ((phiR mode xi t : ℝ) : ℂ) := by
  unfold Phi phiR Cvs.Finite.UniversalFunctionPairing.R
  push_cast
  rfl

/-- **Under RH the CvS quadratic form is a weighted sum of squares of the universal amplitude
at the dilated ordinates.** -/
theorem quadForm_eq_sumsq_of_RH [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0)
    (hRH : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ((rho : ℂ)).re = 1 / 2) :
    xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ xi)
      = L * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ) * phiR mode xi (L * ((rho : ℂ)).im) ^ 2 := by
  rw [Cvs.Finite.UniversalFunctionPairing.quadForm_eq_universal hL hinj hinv hmode hxieven hgen]
  congr 1
  refine tsum_congr fun rho => ?_
  rw [Cvs.ZeroCounting.zPoint_of_re_eq_half (hRH rho), F_eq_Phi_sq,
    show (L : ℂ) * (((rho : ℂ)).im : ℂ) = ((L * ((rho : ℂ)).im : ℝ) : ℂ) by push_cast; ring,
    Phi_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Under RH the CvS matrix is positive semidefinite on even vectors.** -/
theorem quadForm_nonneg_of_RH [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * mode k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0)
    (hRH : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ((rho : ℂ)).re = 1 / 2) :
    0 ≤ xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ xi) := by
  rw [quadForm_eq_sumsq_of_RH hL hinj hinv hmode hxieven hgen hRH]
  exact mul_nonneg hL.le (tsum_nonneg fun rho => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end Cvs.Finite.EvenBilinearZeroSide
