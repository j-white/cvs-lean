import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Fourier transform of a window function is bounded and Lipschitz

    `‖𝓕 f ξ‖ ≤ ∫ ‖f‖`        `‖𝓕 f ξ − 𝓕 f η‖ ≤ 2π L (∫ ‖f‖) |ξ − η|`

for `f` supported in `[0, L]`: the unit exponential is `1`-Lipschitz in its phase and the
support bounds `|x|`.
-/

noncomputable section

open MeasureTheory FourierTransform Real Complex

namespace Cvs.WeilForm.WindowFourierBoundedLipschitz

/-- **The unit exponential is `1`-Lipschitz in its phase.** -/
theorem norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp (↑a * I) - Complex.exp (↑b * I)‖ ≤ |a - b| := by
  have hsplit : Complex.exp (↑a * I) - Complex.exp (↑b * I)
      = Complex.exp (↑b * I) * (Complex.exp (I * ↑(a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

/-- **The transform is bounded by the `L¹` norm.** -/
theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) : ‖(𝓕 f) ξ‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) f ξ

/-- The phase factor times `f` is integrable, because the factor has modulus one. -/
theorem integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * I) * f v) := by
  refine Integrable.mono' hf.norm ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * I))
      |>.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The transform is Lipschitz**, with constant `2π L ∫‖f‖` when `f` lives in `[0, L]`. -/
theorem norm_fourier_sub_le {L : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Set.Icc 0 L → f x = 0) (ξ η : ℝ) :
    ‖(𝓕 f) ξ - (𝓕 f) η‖ ≤ 2 * π * L * (∫ x, ‖f x‖) * |ξ - η| := by
  have heq : (𝓕 f) ξ - (𝓕 f) η
      = ∫ v : ℝ, (Complex.exp (↑(-2 * π * v * ξ) * I) - Complex.exp (↑(-2 * π * v * η) * I))
          * f v := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    rw [← integral_sub (integrable_phase_mul hf ξ) (integrable_phase_mul hf η)]
    congr 1; funext v; ring
  rw [heq]
  -- the pointwise bound, using the support to control `|v|`
  have hpt : ∀ v : ℝ, ‖(Complex.exp (↑(-2 * π * v * ξ) * I)
      - Complex.exp (↑(-2 * π * v * η) * I)) * f v‖ ≤ (2 * π * L * |ξ - η|) * ‖f v‖ := by
    intro v
    rw [norm_mul]
    by_cases hv : v ∈ Set.Icc 0 L
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have habs : |(-2 * π * v * ξ) - (-2 * π * v * η)| = 2 * π * |v| * |ξ - η| := by
        rw [show (-2 * π * v * ξ) - (-2 * π * v * η) = -(2 * π) * (v * (ξ - η)) by ring,
          abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_mul]
        ring
      calc ‖Complex.exp (↑(-2 * π * v * ξ) * I) - Complex.exp (↑(-2 * π * v * η) * I)‖
          ≤ |(-2 * π * v * ξ) - (-2 * π * v * η)| := norm_exp_sub_exp_le _ _
        _ = 2 * π * |v| * |ξ - η| := habs
        _ ≤ 2 * π * L * |ξ - η| := by
            have hvL : |v| ≤ L := by rw [abs_of_nonneg hv.1]; exact hv.2
            have : 2 * π * |v| ≤ 2 * π * L := mul_le_mul_of_nonneg_left hvL (by positivity)
            exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    · rw [hsupp v hv, norm_zero, mul_zero, mul_zero]
  calc ‖∫ v : ℝ, (Complex.exp (↑(-2 * π * v * ξ) * I) - Complex.exp (↑(-2 * π * v * η) * I))
          * f v‖
      ≤ ∫ v : ℝ, (2 * π * L * |ξ - η|) * ‖f v‖ :=
        norm_integral_le_of_norm_le (hf.norm.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = (2 * π * L * |ξ - η|) * ∫ v : ℝ, ‖f v‖ := integral_const_mul _ _
    _ = 2 * π * L * (∫ x, ‖f x‖) * |ξ - η| := by ring

end Cvs.WeilForm.WindowFourierBoundedLipschitz
