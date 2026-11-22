import Mathlib
import Cvs.Zeta.ExplicitFormula.AutocorrelationConvolution
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.FourierConventionBridge
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.TransformContinuityScaling
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine
import Cvs.Zeta.FourierShift

/-!
# The prime channel is a finite sum

This closes the chain `WindowTransformFullLine` opened.
-/

namespace Cvs.Detection

open Complex MeasureTheory FourierTransform
open scoped Real RealInnerProductSpace

theorem inner_real (u v : ℝ) : (⟪u, v⟫ : ℝ) = u * v := by
  rw [RCLike.inner_apply]; simp [mul_comm]

/-- **Dilation.**  Compressing a function by `a` dilates its transform by `a`,
with a factor of `a` in front. -/
theorem fourier_comp_div {a : ℝ} (ha : 0 < a) (F : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x : ℝ => F (x / a)) w = (a : ℂ) * 𝓕 F (a * w) := by
  have hane : a ≠ 0 := ne_of_gt ha
  rw [Real.fourier_eq', Real.fourier_eq']
  simp_rw [smul_eq_mul, inner_real]
  have hcomp : ∀ x : ℝ,
      Complex.exp ((↑(-2 * π * (x * w)) : ℂ) * I) * F (x / a)
        = (fun u : ℝ => Complex.exp ((↑(-2 * π * (u * (a * w))) : ℂ) * I) * F u) (a⁻¹ * x) := by
    intro x
    show _ = Complex.exp ((↑(-2 * π * (a⁻¹ * x * (a * w))) : ℂ) * I) * F (a⁻¹ * x)
    have harg : a⁻¹ * x * (a * w) = x * w := by field_simp
    rw [harg, div_eq_inv_mul]
  have hg := MeasureTheory.Measure.integral_comp_inv_mul_left
    (fun u : ℝ => Complex.exp ((↑(-2 * π * (u * (a * w))) : ℂ) * I) * F u) a
  rw [integral_congr_ae (Filter.Eventually.of_forall hcomp), hg, abs_of_pos ha,
    Complex.real_smul]

/-- `h` on the real axis is the autocorrelation's transform, rescaled. -/
theorem sqTransform_eq_fourier_autocorr {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    Cvs.Detection.sqTransform L f ((x : ℝ) : ℂ)
      = 𝓕 (Cvs.Detection.autocorr L f) (x / (2 * π)) := by
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  rw [Cvs.Detection.fourier_autocorr hf, Cvs.Zeta.ExplicitFormula.TransformContinuityScaling.fourier_truncate_eq hL,
    Cvs.Zeta.ExplicitFormula.TransformContinuityScaling.fourier_truncate_eq hL, Cvs.Detection.sqTransform]
  have h1 : ((2 * π * (x / (2 * π)) : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
    congr 1; field_simp
  have h2 : ((2 * π * -(x / (2 * π)) : ℝ) : ℂ) = -((x : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [h1, h2]

/-- **The prime weight is `2π` times the autocorrelation, reflected.** -/
theorem fourierReal_sqTransform {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2) (t : ℝ) :
    Cvs.Zeta.fourierReal (Cvs.Detection.sqTransform L f) t
      = ((2 * π : ℝ) : ℂ) * Cvs.Detection.autocorr L f (-t) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hfun : (fun x : ℝ => Cvs.Detection.sqTransform L f ((x : ℝ) : ℂ))
      = fun x : ℝ => 𝓕 (Cvs.Detection.autocorr L f) (x / (2 * π)) :=
    funext (sqTransform_eq_fourier_autocorr hL hf)
  rw [Cvs.Detection.fourierReal_eq_fourier, hfun, fourier_comp_div hpi]
  have harg : 2 * π * (t / (2 * π)) = t := by field_simp
  rw [harg]
  have hinv := Cvs.Zeta.ExplicitFormula.TransformContinuityScaling.fourier_fourier_autocorr hL hf h0 hLz hC hbd (-t)
  rw [neg_neg] at hinv
  rw [hinv]

/-- **The prime weight vanishes outside `[−L, L]`.** -/
theorem fourierReal_eq_zero {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2)
    {t : ℝ} (ht : L ≤ |t|) :
    Cvs.Zeta.fourierReal (Cvs.Detection.sqTransform L f) t = 0 := by
  rw [fourierReal_sqTransform hL hf h0 hLz hC hbd t,
    Cvs.Detection.autocorr_eq_zero_of_abs_ge f (by rwa [abs_neg]), mul_zero]

/-- **The prime sum stops at `n = e^L`.**  Every term with `n ≥ e^L` is zero. -/
theorem fourierReal_log_eq_zero {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2)
    {n : ℕ} (hn : Real.exp L ≤ n) :
    Cvs.Zeta.fourierReal (Cvs.Detection.sqTransform L f) (Real.log n) = 0 := by
  have hlog : L ≤ Real.log n := by
    have hh := Real.log_le_log (Real.exp_pos L) hn
    rwa [Real.log_exp] at hh
  refine fourierReal_eq_zero hL hf h0 hLz hC hbd ?_
  rw [abs_of_nonneg (by linarith)]
  exact hlog

end Cvs.Detection
