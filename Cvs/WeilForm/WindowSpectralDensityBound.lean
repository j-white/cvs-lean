import Mathlib
import Cvs.WeilForm.PoleTermCauchySchwarz
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.WeilPositivityStatement

/-!
# The spectral density is uniformly bounded on the window

    ‖𝓕 f ξ‖² = (∫ f·cos)² + (∫ f·sin)² ≤ L·g 0

for `f` supported in `[−L/2, L/2]`, by `Cvs.WeilForm.PoleTermCauchySchwarz`'s Cauchy–Schwarz twice against a character of
unit modulus.  So the density is capped by the window length times the norm.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.WindowSpectralDensityBound

open Cvs.WeilForm.SelfConvolutionTransform

/-- Against a bounded weight, an integrable function stays integrable. -/
theorem integrable_mul_bdd {f : ℝ → ℝ} (hf : Integrable f) {φ : ℝ → ℝ}
    (hcont : Continuous φ) (hbd : ∀ x, |φ x| ≤ 1) :
    Integrable fun v : ℝ => f v * φ v := by
  refine Integrable.mono' hf.norm (hf.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun v => ?_
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hbd v)

/-- **The transform's square modulus, in real terms.** -/
theorem norm_fourier_sq_eq {f : ℝ → ℝ} (hf : Integrable f) (ξ : ℝ) :
    ‖𝓕 (cf f) ξ‖ ^ 2
      = (∫ v : ℝ, f v * Real.cos (2 * π * v * ξ)) ^ 2
        + (∫ v : ℝ, f v * Real.sin (2 * π * v * ξ)) ^ 2 := by
  have hint : Integrable fun v : ℝ =>
      Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) * (f v : ℂ) := by
    refine Integrable.mono' hf.norm ?_ ?_
    · exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (((continuous_const.mul continuous_id).mul continuous_const))).mul
          continuous_const)).aestronglyMeasurable).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [norm_mul, Complex.norm_exp]
      simp
  have hexp : 𝓕 (cf f) ξ = ∫ v : ℝ,
      Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) * (f v : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    rfl
  have hre : (𝓕 (cf f) ξ).re = ∫ v : ℝ, f v * Real.cos (2 * π * v * ξ) := by
    rw [hexp, show ((∫ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I)
        * (f v : ℂ)).re)
      = RCLike.re (∫ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I)
        * (f v : ℂ)) from rfl, ← integral_re hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show (Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) * (f v : ℂ)).re
      = f v * Real.cos (2 * π * v * ξ)
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im,
      show (-2 * π * v * ξ) = -(2 * π * v * ξ) by ring, Real.cos_neg]
    ring
  have him : (𝓕 (cf f) ξ).im = -∫ v : ℝ, f v * Real.sin (2 * π * v * ξ) := by
    rw [hexp, show ((∫ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I)
        * (f v : ℂ)).im)
      = RCLike.im (∫ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I)
        * (f v : ℂ)) from rfl, ← integral_im hint, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show (Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) * (f v : ℂ)).im
      = -(f v * Real.sin (2 * π * v * ξ))
    rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im,
      show (-2 * π * v * ξ) = -(2 * π * v * ξ) by ring, Real.sin_neg]
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  ring

/-- **The density is capped by the window length times the norm.**  Cauchy–Schwarz against
the two components of a character, whose squares add to one. -/
theorem norm_fourier_sq_le {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0)
    (hf : Integrable f) (hsq : Integrable fun s => (f s) ^ 2) (ξ : ℝ) :
    ‖𝓕 (cf f) ξ‖ ^ 2 ≤ L * selfConvolution f 0 := by
  have hcos : Continuous fun v : ℝ => Real.cos (2 * π * v * ξ) :=
    Real.continuous_cos.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hsin : Continuous fun v : ℝ => Real.sin (2 * π * v * ξ) :=
    Real.continuous_sin.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hC := Cvs.WeilForm.PoleTermCauchySchwarz.sq_integral_mul_le_window (L := L) hsupp hsq hcos
    (integrable_mul_bdd hf hcos fun v => Real.abs_cos_le_one _)
  have hS := Cvs.WeilForm.PoleTermCauchySchwarz.sq_integral_mul_le_window (L := L) hsupp hsq hsin
    (integrable_mul_bdd hf hsin fun v => Real.abs_sin_le_one _)
  have hadd : (∫ s in Icc (-(L / 2)) (L / 2),
        ((Real.cos (2 * π * s * ξ)) ^ 2 + (Real.sin (2 * π * s * ξ)) ^ 2))
      = (∫ s in Icc (-(L / 2)) (L / 2), (Real.cos (2 * π * s * ξ)) ^ 2)
        + ∫ s in Icc (-(L / 2)) (L / 2), (Real.sin (2 * π * s * ξ)) ^ 2 :=
    integral_add ((hcos.pow 2).integrableOn_Icc) ((hsin.pow 2).integrableOn_Icc)
  have hone : (∫ s in Icc (-(L / 2)) (L / 2), (Real.cos (2 * π * s * ξ)) ^ 2)
      + (∫ s in Icc (-(L / 2)) (L / 2), (Real.sin (2 * π * s * ξ)) ^ 2) = L := by
    rw [← hadd]
    have hpt : ∀ s : ℝ, (Real.cos (2 * π * s * ξ)) ^ 2 + (Real.sin (2 * π * s * ξ)) ^ 2
        = (1 : ℝ) := fun s => Real.cos_sq_add_sin_sq _
    rw [setIntegral_congr_fun measurableSet_Icc (fun s _ => hpt s), setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith : -(L / 2) ≤ L / 2)]
    simp
  have hfac : selfConvolution f 0 * (∫ s in Icc (-(L / 2)) (L / 2),
        (Real.cos (2 * π * s * ξ)) ^ 2)
      + selfConvolution f 0 * (∫ s in Icc (-(L / 2)) (L / 2),
        (Real.sin (2 * π * s * ξ)) ^ 2)
      = L * selfConvolution f 0 := by
    rw [← mul_add, hone]; ring
  rw [norm_fourier_sq_eq hf ξ]
  linarith [hC, hS, hfac]

end Cvs.WeilForm.WindowSpectralDensityBound
