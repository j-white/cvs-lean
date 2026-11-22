import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Fourier transform is Lipschitz when the first moment is finite

    ‖𝓕 f ξ − 𝓕 f η‖ ≤ 2π·|ξ − η|·∫ |x|·‖f x‖

so a uniform first-moment bound gives equicontinuous transforms; on a fixed compact support
that bound is automatic.  Mathlib only.
-/

noncomputable section

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Cvs.Upstream.FourierFirstMomentLipschitz

/-- **A character moves at unit speed.**  `‖e^{iθ} − 1‖ ≤ |θ|`, with no restriction on `θ` —
Mathlib's `norm_exp_sub_one_le` asks `‖x‖ ≤ 1` and loses a factor of two. -/
theorem norm_cexp_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have hsq : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_ofReal_mul_I]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    linarith
  have hnn : 0 ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := norm_nonneg _
  nlinarith [hsq, hcos, sq_abs θ, abs_nonneg θ]

/-- **The transform is Lipschitz with the first moment as constant.**  Equicontinuity of a
family of transforms therefore needs only a uniform bound on `∫ |x|·‖f x‖`. -/
theorem norm_fourier_sub_le {f : ℝ → ℂ} (hf : Integrable f)
    (hxf : Integrable fun x => |x| * ‖f x‖) (ξ η : ℝ) :
    ‖𝓕 f ξ - 𝓕 f η‖ ≤ 2 * π * |ξ - η| * ∫ x : ℝ, |x| * ‖f x‖ := by
  have hint : ∀ w : ℝ, Integrable fun x : ℝ =>
      Complex.exp ((↑(-2 * π * x * w) : ℂ) * Complex.I) * f x := by
    intro w
    refine Integrable.mono' hf.norm ?_ ?_
    · exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (((continuous_const.mul continuous_id).mul continuous_const))).mul
          continuous_const)).aestronglyMeasurable).mul hf.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_exp]
      simp
  have hxi := Real.fourier_real_eq_integral_exp_smul f ξ
  have heta := Real.fourier_real_eq_integral_exp_smul f η
  simp only [smul_eq_mul] at hxi heta
  rw [hxi, heta, ← integral_sub (hint ξ) (hint η)]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpt : ∀ x : ℝ, ‖Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) * f x
        - Complex.exp ((↑(-2 * π * x * η) : ℂ) * Complex.I) * f x‖
      ≤ 2 * π * |ξ - η| * (|x| * ‖f x‖) := by
    intro x
    have he : Complex.exp ((↑(-2 * π * x * η) : ℂ) * Complex.I)
        * Complex.exp ((↑(-2 * π * x * (ξ - η)) : ℂ) * Complex.I)
        = Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfac : Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) * f x
        - Complex.exp ((↑(-2 * π * x * η) : ℂ) * Complex.I) * f x
        = Complex.exp ((↑(-2 * π * x * η) : ℂ) * Complex.I)
          * ((Complex.exp ((↑(-2 * π * x * (ξ - η)) : ℂ) * Complex.I) - 1) * f x) := by
      rw [← he]
      ring
    rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
    have hchar := norm_cexp_I_sub_one_le (-2 * π * x * (ξ - η))
    have habs : |(-2 : ℝ) * π * x * (ξ - η)| = 2 * π * |x| * |ξ - η| := by
      rw [show (-2 : ℝ) * π * x * (ξ - η) = -(2 * π * x * (ξ - η)) by ring, abs_neg]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [habs] at hchar
    have hnn : (0:ℝ) ≤ ‖f x‖ := norm_nonneg _
    nlinarith [hchar, hnn]
  have hbd : Integrable fun x : ℝ => 2 * π * |ξ - η| * (|x| * ‖f x‖) := hxf.const_mul _
  refine le_trans (integral_mono ((hint ξ).sub (hint η)).norm hbd hpt) ?_
  rw [integral_const_mul]

end Cvs.Upstream.FourierFirstMomentLipschitz
