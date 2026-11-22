import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Zeta.ExplicitFormula.AutocorrelationConvolution
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.TaperedAutocorrelationContinuous
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# Fourier inversion for the autocorrelation

`TaperedAutocorrelationContinuous` gave `Continuous R`, the first of inversion's three hypotheses.
-/

namespace Cvs.Zeta.ExplicitFormula.AutocorrelationFourierInversion
open Cvs.Detection

open Complex MeasureTheory FourierTransform
open scoped Real

theorem hasCompactSupport_autocorr (L : ℝ) (f : ℝ → ℂ) :
    HasCompactSupport (Cvs.Detection.autocorr L f) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := (-L : ℝ)) (b := L)) ?_
  exact (Cvs.Detection.support_autocorr L f).trans Set.Ioo_subset_Icc_self

/-- `R` is integrable — continuous with compact support. -/
theorem integrable_autocorr {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) : Integrable (Cvs.Detection.autocorr L f) :=
  (Cvs.Detection.continuous_autocorr hL hf h0 hLz).integrable_of_hasCompactSupport
    (hasCompactSupport_autocorr L f)

/-- **`𝓕 R` is integrable**, from a merely quadratic bound on `𝓕 g`. -/
theorem integrable_fourier_autocorr {L : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hFg : Continuous (𝓕 (Cvs.Detection.truncate L f))) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2) :
    Integrable (𝓕 (Cvs.Detection.autocorr L f)) := by
  have hprod : Continuous (𝓕 (Cvs.Detection.autocorr L f)) := by
    have hfun : 𝓕 (Cvs.Detection.autocorr L f)
        = fun w : ℝ => 𝓕 (Cvs.Detection.truncate L f) w * 𝓕 (Cvs.Detection.truncate L f) (-w) :=
      funext (Cvs.Detection.fourier_autocorr hf)
    rw [hfun]
    exact hFg.mul (hFg.comp continuous_neg)
  refine (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono'
    hprod.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  rw [Cvs.Detection.fourier_autocorr hf, norm_mul]
  have habs : (0 : ℝ) ≤ |w| := abs_nonneg _
  have hden : (0 : ℝ) < (1 + |w|) ^ 2 := by positivity
  have hstep : ‖𝓕 (Cvs.Detection.truncate L f) w‖ * ‖𝓕 (Cvs.Detection.truncate L f) (-w)‖
      ≤ (C / (1 + |w|) ^ 2) * (C / (1 + |w|) ^ 2) := by
    have h2 := hbd (-w)
    rw [abs_neg] at h2
    exact mul_le_mul (hbd w) h2 (norm_nonneg _) (by positivity)
  refine hstep.trans ?_
  rw [div_mul_div_comm, ← pow_add]
  have hone : (1 : ℝ) + w ^ 2 ≤ (1 + |w|) ^ (2 + 2) := by
    have h1 : (1 : ℝ) + w ^ 2 ≤ (1 + |w|) ^ 2 := by nlinarith [sq_abs w, habs]
    have h2 : (1 : ℝ) ≤ (1 + |w|) ^ 2 := by nlinarith [habs]
    calc (1 : ℝ) + w ^ 2 ≤ (1 + |w|) ^ 2 := h1
      _ = (1 + |w|) ^ 2 * 1 := by ring
      _ ≤ (1 + |w|) ^ 2 * (1 + |w|) ^ 2 := by nlinarith [h2, hden]
      _ = (1 + |w|) ^ (2 + 2) := by ring
  rw [← div_eq_mul_inv, ← pow_two]
  gcongr

/-- **Fourier inversion for the autocorrelation.** -/
theorem fourier_fourier_autocorr {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) (hFg : Continuous (𝓕 (Cvs.Detection.truncate L f)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2) (w : ℝ) :
    𝓕 (𝓕 (Cvs.Detection.autocorr L f)) (-w) = Cvs.Detection.autocorr L f w := by
  have hinv := (Cvs.Detection.continuous_autocorr hL hf h0 hLz).fourierInv_fourier_eq
    (integrable_autocorr hL hf h0 hLz)
    (integrable_fourier_autocorr hf hFg hC hbd)
  rw [← Real.fourierInv_eq_fourier_neg, hinv]

end Cvs.Zeta.ExplicitFormula.AutocorrelationFourierInversion
