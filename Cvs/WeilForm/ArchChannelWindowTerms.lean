import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolTwiceScore
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityModulus
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# The archimedean channel, in the window form's terms

    ∫ archScore y · ‖windowTransform L f y‖² dy = π · ∫ specDensity f t · archSymbol t dt

`Cvs.WeilForm.Archimedean.SymbolTwiceScore` halves the symbol into the detection score and `Cvs.WeilForm.SpectralDensityModulus` turns the transform's square
modulus into `2π` times the density, so the two factors of two combine into one `π`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ArchChannelWindowTerms

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded Cvs.WeilForm.SelfConvolutionTransform

/-- **The archimedean channel's integrand, rewritten.** -/
theorem archScore_mul_norm_sq {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) (y : ℝ) :
    Cvs.Detection.archScore y
        * ‖Cvs.Detection.windowTransform L (cf f) ((y : ℝ) : ℂ)‖ ^ 2
      = π * (Cvs.WeilForm.SelfConvolutionCosine.specDensity (Set.indicator (Set.Ioc 0 L) f) y
          * archSymbol y) := by
  rw [show (cf f) = (fun s : ℝ => ((f s : ℝ) : ℂ)) from rfl,
    Cvs.WeilForm.SpectralDensityModulus.norm_windowTransform_sq_eq hL f y]
  have hscore : archSymbol y = 2 * Cvs.Detection.archScore y :=
    Cvs.WeilForm.Archimedean.SymbolTwiceScore.archSymbol_eq_two_mul_archScore y
  rw [hscore]
  ring

/-- **The archimedean channel.**  The detection side's integral is `π` times the window
form's archimedean term. -/
theorem arch_channel_eq {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) :
    (∫ y : ℝ, Cvs.Detection.archScore y
        * ‖Cvs.Detection.windowTransform L (cf f) ((y : ℝ) : ℂ)‖ ^ 2)
      = π * ∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity
          (Set.indicator (Set.Ioc 0 L) f) t * archSymbol t := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    fun y => archScore_mul_norm_sq hL f y)

end Cvs.WeilForm.ArchChannelWindowTerms
