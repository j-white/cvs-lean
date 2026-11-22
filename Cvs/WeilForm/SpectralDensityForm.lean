import Mathlib
import Cvs.WeilForm.Archimedean.ArchSpectralDensity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WindowTruncatesPrimes
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form against its spectral density

    weilForm = 2·A(f)·M(f) + ∫ specDensity f t · archSymbol t dt − windowed prime sum

`Cvs.WeilForm.SelfConvolutionCosine` writes the self-convolution as a cosine integral against a nonnegative density, `Cvs.WeilForm.Archimedean.ArchSpectralDensity`
charges each frequency the symbol there, and `Cvs.WeilForm.WindowTruncatesPrimes` truncates the prime side.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.SpectralDensityForm

/-- **The window's form, frequency by frequency.**  Each frequency the test function carries
is charged `archSymbol` there, against a density that is a square modulus. -/
theorem weilForm_spectral (P R : ℕ) {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0)
    (hfint : Integrable f)
    (hgint : Integrable fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
    (hcont : Continuous fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
    (hFsq : Integrable fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2)
    (hWi : Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f))
    (hWA : Integrable fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
    (hprod : Integrable (Function.uncurry fun u t : ℝ =>
        Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * ((1 - Real.cos (t / 2 * u)) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t))
      ((volume.restrict (Ioi (0:ℝ))).prod volume)) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
      = 2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))
        + (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
            * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t)
        - ∑ k ∈ Cvs.WeilForm.WindowTruncatesPrimes.windowIndex P R L,
            (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1/2) : ℝ))
              * (selfConvolution f (Real.log k) + selfConvolution f (-(Real.log k))) := by
  have hg : ∀ v : ℝ, selfConvolution f v
      = ∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * Real.cos (t * v) := fun v =>
    Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hFsq hcont.continuousAt
  have harch := Cvs.WeilForm.Archimedean.ArchSpectralDensity.arch_of_spectral hWi hg hWA hprod
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, harch,
    Cvs.WeilForm.WindowTruncatesPrimes.primePowerSideTruncated_eq_window hL hsupp P R]

end Cvs.WeilForm.SpectralDensityForm
