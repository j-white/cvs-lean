import Mathlib
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.StepAZeroFreeMinimiser
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The constant minimiser, and link 3 from step (a) alone

If the constant is the even minimiser, its transform is `(e^{izL} − 1)/(iz)` up to a factor,
zero-free off the axes by inspection; otherwise `Cvs.Limit.StepAZeroFreeMinimiser` applies. So step (a) at a scale gives,
with no further hypothesis, a zero-free Fourier–Laplace transform for its normalised minimiser.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix Filter Topology

namespace Cvs.Limit.ConstantMinimiserLink

/-- `e^{izL} ≠ 1` off the real axis. -/
theorem exp_I_mul_ne_one {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z.im ≠ 0) :
    Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h1 : z * (L : ℂ) = (((n : ℝ) * (2 * π) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    push_cast
    linear_combination hn
  have h2 := congrArg Complex.im h1
  rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add,
    Complex.ofReal_im] at h2
  exact hz ((mul_eq_zero.mp h2).resolve_right hL.ne')

/-- The transform respects a.e. equality. -/
theorem fourierLaplace_cf_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[(volume : Measure ℝ)] g) (z : ℂ) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
      = FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf g) z := by
  unfold FourierLaplace.fourierLaplace
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, hx]

/-- The constant coefficient vector on the zero-mode set. -/
def constVec (c : ℝ) : Cvs.Finite.SymmetricModeSet.Idx 0 → ℝ := fun _ => c

theorem dotProduct_constVec (c : ℝ) : constVec c ⬝ᵥ constVec c = c * c := by
  simp [dotProduct, constVec]

theorem quad_constVec {L : ℝ} (hL : 0 < L) (P R : ℕ) (c : ℝ) :
    constVec c ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode 0) *ᵥ constVec c)
      = c * c * Cvs.Finite.PairFormDividedDifference.aval P R L 0 := by
  simp [dotProduct, Matrix.mulVec, constVec]
  rw [show (default : Cvs.Finite.SymmetricModeSet.Idx 0) = none from rfl,
    Cvs.Limit.StepAZeroFreeMinimiser.M_none_none hL]
  ring

/-- **The normalised constant lies in the even window set.** -/
theorem const_mem {L : ℝ} (hL : 0 < L) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode 0) (constVec (Real.sqrt L)⁻¹)
      ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L := by
  refine Cvs.Finite.ModeSumFormDomain.modeSum_mem_evenWindowSet hL (Cvs.Finite.SymmetricModeSet.mode_injective 0)
    (Cvs.Finite.SymmetricModeSet.negI_involutive 0) (Cvs.Finite.SymmetricModeSet.mode_negI 0)
    (fun _ => rfl) ?_
  rw [dotProduct_constVec, ← sq, inv_pow, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']

/-- **Its form is the constant mode's diagonal entry.** -/
theorem weilForm_const {L : ℝ} (hL : 0 < L) (P R : ℕ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
      (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode 0) (constVec (Real.sqrt L)⁻¹))
      = Cvs.Finite.PairFormDividedDifference.aval P R L 0 := by
  rw [Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL P R
    (Cvs.Finite.SymmetricModeSet.mode_injective 0) (Cvs.Finite.SymmetricModeSet.negI_involutive 0)
    (Cvs.Finite.SymmetricModeSet.mode_negI 0) (fun _ => rfl)]
  change L * (constVec (Real.sqrt L)⁻¹ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L
    (Cvs.Finite.SymmetricModeSet.mode 0) *ᵥ constVec (Real.sqrt L)⁻¹)) = _
  rw [quad_constVec hL, ← sq, inv_pow, Real.sq_sqrt hL.le]
  field_simp

/-- **The transform of the constant mode sum**, in closed form. -/
theorem fourierLaplace_const {L : ℝ} (hL : 0 < L) (c : ℝ) {z : ℂ} (hz : z ≠ 0) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
      (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode 0) (constVec c))) z
      = ((Complex.exp (Complex.I * z * (L : ℂ)) - 1) / Complex.I) * ((c : ℂ) / z) := by
  have hz' : ∀ i : Cvs.Finite.SymmetricModeSet.Idx 0,
      ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode 0) i : ℝ) : ℂ) + z ≠ 0 := by
    rintro (_ | ⟨k, b⟩)
    · simpa [Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode] using hz
    · exact k.elim0
  rw [Cvs.Finite.TruncationZeroFreeOffAxes.fourierLaplace_modeSum hL (Cvs.Finite.SymmetricModeSet.negI_involutive 0)
    (Cvs.Finite.SymmetricModeSet.mode_negI 0) (fun _ => rfl) z hz']
  congr 1
  rw [Fintype.sum_option]
  simp [constVec, Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode]

end Cvs.Limit.ConstantMinimiserLink
