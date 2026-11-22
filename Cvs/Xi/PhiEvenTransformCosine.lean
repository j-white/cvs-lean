import Mathlib
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Xi.PhiEvenExtension
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.XiCosineTransformPhi

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even extension's transform is the cosine transform

The line splits at the origin, and reflection carries the negative half onto the positive one with
the frequency reversed. The two exponentials that meet there combine into a cosine, so the
transform of the even extension is twice the cosine transform of `Φ`. Riemann's `Ξ` is
four times that same cosine transform, so it is twice the transform of the even extension.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform

namespace Cvs.Xi.PhiEvenTransformCosine

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiEvenExtension

/-- Opposite frequencies combine into a cosine. -/
theorem exp_add_exp_neg (w : ℂ) :
    Complex.exp (Complex.I * w) + Complex.exp (-(Complex.I * w)) = 2 * Complex.cos w := by
  have h1 : Complex.exp (Complex.I * w) = Complex.cos w + Complex.sin w * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_mul_I w
  have h2 : Complex.exp (-(Complex.I * w)) = Complex.cos w - Complex.sin w * Complex.I := by
    have hrw : -(Complex.I * w) = (-w) * Complex.I := by ring
    rw [hrw, Complex.exp_mul_I (-w), Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]
  ring

/-- The Fourier integrand of the even extension is integrable. -/
theorem integrable_integrand (w : ℝ) :
    Integrable (fun v : ℝ =>
      Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * Complex.I) * phiEven v) := by
  refine Integrable.mono' integrable_phiEven.norm ?_ ?_
  · exact (by fun_prop : Continuous fun v : ℝ =>
      Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable.mul
      integrable_phiEven.aestronglyMeasurable
  · filter_upwards with v
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The negative half of the line, reflected onto the positive half. -/
theorem integral_Iic_eq (w : ℝ) :
    ∫ v in Iic (0 : ℝ), Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * Complex.I) * phiEven v
      = ∫ v in Ioi (0 : ℝ), Complex.exp (((2 * π * v * w : ℝ) : ℂ) * Complex.I) * phiEven v := by
  have h := integral_comp_neg_Iic (0 : ℝ)
    (fun y : ℝ => Complex.exp (((-2 * π * (-y) * w : ℝ) : ℂ) * Complex.I) * phiEven (-y))
  simp only [neg_neg, neg_zero] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  rw [phiEven_neg]
  congr 2
  push_cast
  ring

/-- **The transform of the even extension is twice the cosine transform of `Φ`.** -/
theorem fourierIntegral_phiEven (w : ℝ) :
    𝓕 phiEven w
      = ((2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cos (2 * π * w * u) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) (integrable_integrand w),
    compl_Iic, integral_Iic_eq w]
  have hI1 : IntegrableOn
      (fun v : ℝ => Complex.exp (((2 * π * v * w : ℝ) : ℂ) * Complex.I) * phiEven v)
      (Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun ((integrable_integrand (-w)).integrableOn)
      (fun v _ => by congr 2; push_cast; ring) measurableSet_Ioi
  have hI2 : IntegrableOn
      (fun v : ℝ => Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * Complex.I) * phiEven v)
      (Ioi (0 : ℝ)) := (integrable_integrand w).integrableOn
  rw [← MeasureTheory.integral_add hI1 hI2]
  have hR : ((2 * ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cos (2 * π * w * u) : ℝ) : ℂ)
      = ∫ v in Ioi (0 : ℝ), (2 : ℂ) * ((riemannPhi v * Real.cos (2 * π * w * v) : ℝ) : ℂ) := by
    rw [integral_const_mul, _root_.integral_complex_ofReal]
    push_cast
    ring
  rw [hR]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv0 : (0 : ℝ) < v := hv
  have hcomb : Complex.exp (((2 * π * v * w : ℝ) : ℂ) * Complex.I)
      + Complex.exp (((-2 * π * v * w : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.cos (((2 * π * w * v : ℝ) : ℂ)) := by
    have h1 : ((2 * π * v * w : ℝ) : ℂ) * Complex.I
        = Complex.I * ((2 * π * w * v : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((-2 * π * v * w : ℝ) : ℂ) * Complex.I
        = -(Complex.I * ((2 * π * w * v : ℝ) : ℂ)) := by push_cast; ring
    rw [h1, h2, exp_add_exp_neg]
  rw [phiEven_of_pos hv0, ← add_mul, hcomb, ← Complex.ofReal_cos]
  push_cast
  ring

/-- **Riemann's `Ξ` at `2πw` is twice the transform of the even extension.** -/
theorem Xi_eq_two_mul_fourierIntegral (w : ℝ) :
    Cvs.Limit.ZeroFreeApproximantsRH.Xi (((2 * π * w : ℝ) : ℂ)) = 2 * 𝓕 phiEven w := by
  rw [fourierIntegral_phiEven,
    Cvs.Xi.XiCosineTransformPhi.Xi_eq_four_mul_integral_riemannPhi (2 * π * w)]
  push_cast
  ring

end Cvs.Xi.PhiEvenTransformCosine
