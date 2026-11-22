import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.ShiftedDiagonalSimplicity
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.TwoGapFiniteCertificate
import Cvs.Limit.OffAxesLimit
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# Discrete step (a): zero-freeness from a finite certificate at one scale and mode count
`Cvs.Finite.DisplacementIdentity` takes two inputs from continuous step (a): the odd gap and the even kernel line of the
CvS matrix `Cvs.Finite.TruncationQuadraticForm.M` on `Idx N`. Here they are hypotheses about that finite matrix
(`zeroFree_of_discrete`), and `Cvs.Finite.TwoGapFiniteCertificate` supplies them from a certificate: a trial vector `w` and a
level `t` with `wᵀMw < t‖w‖²`, the odd sector `≥ t`, the even sector on `w⊥` `≥ t`, and
`t ≤ M none none` (`zeroFree_of_cert`). No continuous operator enters.
-/

noncomputable section

open Real Matrix

namespace Cvs.Finite.DiscreteStepACertificate

open Cvs.Finite.SymmetricModeSet in
/-- **Zero-freeness of the discrete minimiser's transform from the finite two-gap.** -/
theorem zeroFree_of_discrete {L : ℝ} (hL : 0 < L) (P R N : ℕ)
    (hgap : ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) → o ≠ 0 →
      lamD P R L hL N * (o ⬝ᵥ o) < o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o))
    (hevenline : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) →
      Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v = lamD P R L hL N • v →
      ∃ c : ℝ, v = c • xiD P R L hL N)
    (hconst : lamD P R L hL N < Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) none none) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (xiD P R L hL N))) z ≠ 0 := by
  obtain ⟨hxi1, hge, hxi⟩ := xiD_spec P R L hL N
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) with hM
  set xi := xiD P R L hL N with hxidef
  set lamD := lamD P R L hL N with hlamD
  have hinj := mode_injective N
  have hinv := negI_involutive N
  have hmode := mode_negI N
  have hsymm := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hA := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj hmode
  have hxieven : ∀ i, xi (negI N i) = xi i := by
    have ho := Cvs.Upstream.SymmetricMatrixBottom.oddPart_eq_zero_of_gap hsymm hinv hA hge hgap hxi
    intro i
    have := congrFun ho i
    simp only [Cvs.Finite.TruncationQuadraticForm.oddPart, Pi.zero_apply] at this
    linarith
  have hker : ∀ v, M *ᵥ v = lamD • v → ∃ c : ℝ, v = c • xi :=
    Cvs.Upstream.SymmetricMatrixBottom.kerline_of_even hsymm hinv hA hge hgap hevenline
  have hne : ∃ j, xi j * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j ≠ 0 :=
    Cvs.Finite.DisplacementIdentity.xiD_ne hL P R N hconst
  have hsum : ∑ i, xi i ≠ 0 :=
    Cvs.Finite.DisplacementIdentity.sum_ne_zero_of_eigen (Cvs.Finite.DisplacementIdentity.omega_injective hL hinj) hinv
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega_neg hmode) hgap hxieven hxi hne
  set c : ℝ := (∑ i, xi i)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hsum
  set xi' : Idx N → ℝ := c • xi with hxi'
  have hnorm : ∑ i, xi' i = 1 := by
    simp only [hxi', Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hsum
  have hxieven' : ∀ i, xi' (negI N i) = xi' i := by
    intro i; simp only [hxi', Pi.smul_apply, hxieven i]
  have hQpsd : ∀ v : Idx N → ℝ, 0 ≤ v ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix
      (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag
        (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N k)) lamD)
      (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k))
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N)) *ᵥ v) := by
    intro v
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_shiftDiag]
    change 0 ≤ v ⬝ᵥ (M *ᵥ v) - lamD * (v ⬝ᵥ v)
    linarith [hge v]
  have hQxi : Cvs.Finite.DividedDifferenceCommutator.ddMatrix
      (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag
        (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N k)) lamD)
      (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k))
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N)) *ᵥ xi' = 0 := by
    rw [Cvs.Upstream.SymmetricMatrixBottom.shiftDiag_mulVec_eq_zero_iff]
    change M *ᵥ xi' = lamD • xi'
    rw [hxi', Matrix.mulVec_smul, hxi, smul_comm]
  have hkerline' : ∀ v : Idx N → ℝ, Cvs.Finite.DividedDifferenceCommutator.ddMatrix
      (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (mode N k))
      (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k))
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N)) *ᵥ v = lamD • v →
      ∃ d : ℝ, v = d • xi' := by
    intro v hv
    obtain ⟨d, hd⟩ := hker v hv
    refine ⟨d * (∑ i, xi i), ?_⟩
    rw [hd, hxi', smul_smul, hc, mul_assoc, mul_inv_cancel₀ hsum, mul_one]
  have hne' : ∃ j, xi' j * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) j ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    refine ⟨j, ?_⟩
    simp only [hxi', Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact mul_ne_zero hc0 hj
  have hb : ∀ i, (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k)) (negI N i)
      = -(fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (mode N k)) i := by
    intro i
    simp only []
    rw [hmode, Cvs.Finite.PairFormDividedDifference.bval_neg]
  have hz := Cvs.Finite.TruncationZeroFreeOffAxes.zeroFree_offAxes hL
    (Cvs.Finite.DisplacementIdentity.omega_injective hL hinj) hinv hmode hb
    hxieven' (fun _ => rfl) hQpsd hQxi hnorm hkerline' hne'
  intro z hz'
  have h := hz z hz'
  rw [hxi', Cvs.Finite.ModeSumFormDomain.modeSum_smul, Cvs.Finite.DisplacementIdentity.fourierLaplace_cf_const_mul] at h
  exact (mul_ne_zero_iff.mp h).2

open Cvs.Finite.SymmetricModeSet in
/-- **Discrete step (a) from a finite certificate**: a trial vector `w`, a level `t`, the odd
sector `≥ t`, the even sector on `w⊥` `≥ t`, and `t ≤ M none none`. -/
theorem zeroFree_of_cert {L : ℝ} (hL : 0 < L) (P R N : ℕ) {w : Idx N → ℝ} {t : ℝ}
    (hw : w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w) < t * (w ⬝ᵥ w))
    (hodd : ∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) →
      t * (o ⬝ᵥ o) ≤ o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o))
    (hperp : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → v ⬝ᵥ w = 0 →
      t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
    (hconst : t ≤ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) none none) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (xiD P R L hL N))) z ≠ 0 := by
  obtain ⟨hxi1, hge, hxi⟩ := xiD_spec P R L hL N
  have hlt := Cvs.Finite.TwoGapFiniteCertificate.lam_lt_of_trial hge hw
  have hgap := Cvs.Finite.TwoGapFiniteCertificate.odd_gap_of_cert hge hw hodd
  have hinj := mode_injective N
  have hinv := negI_involutive N
  have hsymm := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hA := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj (mode_negI N)
  have hxieven : ∀ i, xiD P R L hL N (negI N i) = xiD P R L hL N i := by
    have ho := Cvs.Upstream.SymmetricMatrixBottom.oddPart_eq_zero_of_gap hsymm hinv hA hge hgap hxi
    intro i
    have := congrFun ho i
    simp only [Cvs.Finite.TruncationQuadraticForm.oddPart, Pi.zero_apply] at this
    linarith
  have hxi0 : xiD P R L hL N ≠ 0 := by
    intro h; rw [h] at hxi1; simp at hxi1
  exact zeroFree_of_discrete hL P R N hgap
    (Cvs.Finite.TwoGapFiniteCertificate.evenline_of_cert hge hw hperp hxi0 hxieven hxi)
    (lt_of_lt_of_le hlt hconst)

end Cvs.Finite.DiscreteStepACertificate
