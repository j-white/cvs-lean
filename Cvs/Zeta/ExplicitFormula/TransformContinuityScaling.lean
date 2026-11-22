import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Zeta.ExplicitFormula.AutocorrelationFourierInversion
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# The transform's continuity, and the `2π` scaling
-/

namespace Cvs.Zeta.ExplicitFormula.TransformContinuityScaling
open Cvs.Detection

open Complex MeasureTheory FourierTransform
open scoped Real RealInnerProductSpace

/-- **The truncated test's transform is continuous** — `Cvs.Zeta.ExplicitFormula.AutocorrelationFourierInversion`'s open hypothesis. -/
theorem continuous_fourier_truncate (L : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (𝓕 (Cvs.Detection.truncate L f)) := by
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
    (Cvs.Detection.integrable_truncate L hf)
  exact continuous_inner

/-- **Fourier inversion for the autocorrelation**, with no open hypotheses. -/
theorem fourier_fourier_autocorr {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ C / (1 + |w|) ^ 2) (w : ℝ) :
    𝓕 (𝓕 (Cvs.Detection.autocorr L f)) (-w) = Cvs.Detection.autocorr L f w :=
  Cvs.Zeta.ExplicitFormula.AutocorrelationFourierInversion.fourier_fourier_autocorr hL hf h0 hLz (continuous_fourier_truncate L hf) hC hbd w

/-- **The `2π` scaling.**  `𝓕` of the truncation is the window transform at `2πw`. -/
theorem fourier_truncate_eq {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℂ) (w : ℝ) :
    𝓕 (Cvs.Detection.truncate L f) w = Cvs.Detection.windowTransform L f ((2 * π * w : ℝ) : ℂ) := by
  rw [Cvs.Detection.windowTransform_eq_integral hL, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [smul_eq_mul]
  congr 2
  have hinner : (⟪s, w⟫ : ℝ) = s * w := by
    rw [RCLike.inner_apply]
    simp [mul_comm]
  rw [hinner]
  push_cast
  ring

end Cvs.Zeta.ExplicitFormula.TransformContinuityScaling
