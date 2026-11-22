import Mathlib
import Cvs.WeilForm.ChannelKernelCosineTransform

/-!
# The channel kernel's sine transform

An odd integrand integrates to zero on the line, so the channel kernel pairs with a sine to
nothing.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Set
open scoped FourierTransform

namespace Cvs.WeilForm.ChannelKernelSineTransform

variable {b : ℝ}

/-- **An odd integrand integrates to zero on the line.** -/
theorem integral_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) : (∫ x : ℝ, g x) = 0 := by
  have h1 : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, g x := integral_neg_eq_self g volume
  have h2 : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, -g x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hodd x)
  rw [integral_neg] at h2
  linarith [h1, h2]

/-- **The sine transform of the channel kernel vanishes.** -/
theorem integral_exp_neg_abs_sin (c : ℝ) :
    (∫ x : ℝ, Real.exp (-b * |x|) * Real.sin (c * x)) = 0 := by
  refine integral_odd fun x => ?_
  rw [abs_neg, show c * -x = -(c * x) from by ring, Real.sin_neg]
  ring

/-- **The channel kernel is integrable on the line.** -/
theorem integrable_exp_neg_abs (hb : 0 < b) :
    Integrable (fun v : ℝ => Real.exp (-b * |v|)) := by
  have hIoi : IntegrableOn (fun v : ℝ => Real.exp (-b * |v|)) (Ioi 0) := by
    rw [integrableOn_congr_fun (g := fun v : ℝ => Real.exp (-b * v))
      (fun v hv => by rw [abs_of_pos hv]) measurableSet_Ioi]
    exact exp_neg_integrableOn_Ioi 0 hb
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hIio : IntegrableOn (fun v : ℝ => Real.exp (-b * |v|)) (Iio 0) := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ)) hemb
      (f := fun v : ℝ => Real.exp (-b * |v|)) (s := Ioi (0:ℝ))).mpr hIoi
    simpa [Function.comp_def, abs_neg] using h
  have hIic : IntegrableOn (fun v : ℝ => Real.exp (-b * |v|)) (Iic 0) :=
    hIio.congr_set_ae Iio_ae_eq_Iic.symm
  exact integrableOn_univ.mp (by simpa [Iic_union_Ioi] using hIic.union hIoi)

/-- Domination of the trigonometric halves by the kernel. -/
theorem integrable_mul_trig (hb : 0 < b) (c : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hbd : ∀ x, |g x| ≤ 1) :
    Integrable fun v : ℝ => Real.exp (-b * |v|) * g (c * v) := by
  refine (integrable_exp_neg_abs hb).mono'
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (-b * |v|) * g (c * v)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  nlinarith [hbd (c * v), (Real.exp_pos (-b * |v|)).le, abs_nonneg (g (c * v))]

/-- **The channel kernel's Fourier transform**, in Mathlib's normalisation. -/
theorem fourierIntegral_exp_neg_abs (hb : 0 < b) (w : ℝ) :
    𝓕 (fun x : ℝ => (Real.exp (-b * |x|) : ℂ)) w
      = ((2 * b / (b ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  have hIc := integrable_mul_trig hb (2 * Real.pi * w) Real.cos Real.continuous_cos
    Real.abs_cos_le_one
  have hIs := integrable_mul_trig hb (2 * Real.pi * w) Real.sin Real.continuous_sin
    Real.abs_sin_le_one
  rw [Real.fourier_real_eq_integral_exp_smul]
  have key : ∀ v : ℝ, Complex.exp ((↑(-2 * Real.pi * v * w) : ℂ) * Complex.I)
        • ((Real.exp (-b * |v|) : ℝ) : ℂ)
      = ((Real.exp (-b * |v|) * Real.cos (2 * Real.pi * w * v) : ℝ) : ℂ)
        - Complex.I * ((Real.exp (-b * |v|) * Real.sin (2 * Real.pi * w * v) : ℝ) : ℂ) := by
    intro v
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (-2 * Real.pi * v * w : ℝ) = -(2 * Real.pi * w * v) from by ring,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  have h1 : Integrable fun v : ℝ =>
      ((Real.exp (-b * |v|) * Real.cos (2 * Real.pi * w * v) : ℝ) : ℂ) := hIc.ofReal
  have h2 : Integrable fun v : ℝ =>
      Complex.I * ((Real.exp (-b * |v|) * Real.sin (2 * Real.pi * w * v) : ℝ) : ℂ) :=
    (hIs.ofReal).const_mul Complex.I
  have hre : ∀ g : ℝ → ℝ, Integrable g → (∫ x : ℝ, ((g x : ℝ) : ℂ)) = ((∫ x : ℝ, g x : ℝ) : ℂ) :=
    fun g hg => by simpa using Complex.ofRealCLM.integral_comp_comm hg
  rw [integral_sub h1 h2, integral_const_mul, hre _ hIc, hre _ hIs,
    integral_exp_neg_abs_sin, Cvs.WeilForm.ChannelKernelCosineTransform.integral_exp_neg_abs_cos hb]
  push_cast
  ring

/-- **The transform is integrable.**  It is a Poisson-type kernel, dominated by `(1+w²)⁻¹`. -/
theorem integrable_poisson (hb : 0 < b) :
    Integrable (fun w : ℝ => 2 * b / (b ^ 2 + (2 * Real.pi * w) ^ 2)) := by
  set c := min (b ^ 2) (4 * Real.pi ^ 2) with hc
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hcont : Continuous (fun w : ℝ => 2 * b / (b ^ 2 + (2 * Real.pi * w) ^ 2)) :=
    continuous_const.div₀ (by fun_prop) (fun w => by positivity)
  refine (integrable_inv_one_add_sq.const_mul (2 * b / c)).mono'
    hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  have hden : 0 < b ^ 2 + (2 * Real.pi * w) ^ 2 := by positivity
  have hkey : c * (1 + w ^ 2) ≤ b ^ 2 + (2 * Real.pi * w) ^ 2 := by
    have h1 : c ≤ b ^ 2 := min_le_left _ _
    have h2 : c ≤ 4 * Real.pi ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg w, h1, h2]
  have hb1 : (0:ℝ) < 1 + w ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 2 * b / (b ^ 2 + (2 * Real.pi * w) ^ 2)
      ≤ 2 * b / (c * (1 + w ^ 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hkey
    _ = 2 * b / c * (1 + w ^ 2)⁻¹ := by field_simp

/-- **The transform of the kernel is integrable.** -/
theorem integrable_fourier_kernel (hb : 0 < b) :
    Integrable (𝓕 (fun x : ℝ => (Real.exp (-b * |x|) : ℂ))) := by
  rw [funext (fourierIntegral_exp_neg_abs hb)]
  exact (integrable_poisson hb).ofReal

/-- **The inverse pair.**  Fourier inversion applied to the channel kernel: the kernel is the
inverse transform of its resolvent symbol. -/
theorem fourierInv_poisson (hb : 0 < b) :
    𝓕⁻ (fun w : ℝ => ((2 * b / (b ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ))
      = fun x : ℝ => ((Real.exp (-b * |x|) : ℝ) : ℂ) := by
  have h := Continuous.fourierInv_fourier_eq
    (f := fun x : ℝ => ((Real.exp (-b * |x|) : ℝ) : ℂ)) (by fun_prop)
    ((integrable_exp_neg_abs hb).ofReal) (integrable_fourier_kernel hb)
  rwa [funext (fourierIntegral_exp_neg_abs hb)] at h

end Cvs.WeilForm.ChannelKernelSineTransform
