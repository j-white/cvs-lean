import Mathlib
import Cvs.WeilForm.Archimedean.ArchSpectralDensity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.PoleTermCauchySchwarz
import Cvs.WeilForm.PrimeSideBoundedBelow
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The form's value bounds the test function's high-frequency mass

    (c − archSymbol 0)·∫_{|t|≥T} W ≤ weilForm − (archSymbol 0 − 2·Wtot − 4·sinh(L/2))·g 0

with `archSymbol ≥ c` past `T`.  Pole term, prime side and symbol floor are all charged to
the norm; what is left over is paid by the mass at high frequency.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.HighFrequencyMassBound

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded Cvs.WeilForm.SelfConvolutionCosine Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin

/-- **The form's value bounds the high-frequency mass.**  Everything except the symbol's
growth is bounded by a multiple of the norm, so a bound on the form is a bound on the tail. -/
theorem tailMass_le (P R : ℕ) {f : ℝ → ℝ} {L T c : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0)
    (hfint : Integrable f)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    (hA : Integrable fun s => f s * Real.exp (s / 2))
    (hM : Integrable fun s => f s * Real.exp (-(s / 2)))
    (hgint : Integrable fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
    (hcont : Continuous fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
    (hFsq : Integrable fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2)
    (hWi : Integrable (specDensity f))
    (hWA : Integrable fun t : ℝ => specDensity f t * archSymbol t)
    (hprod : Integrable (Function.uncurry fun u t : ℝ =>
        Cvs.WeilForm.Archimedean.LevyDensity.densityU u * ((1 - Real.cos (t / 2 * u)) * specDensity f t))
      ((volume.restrict (Ioi (0:ℝ))).prod volume))
    (hc : ∀ t : ℝ, t ∈ tailSet T → c ≤ archSymbol t) :
    (c - archSymbol 0) * (∫ t in tailSet T, specDensity f t)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
        - (archSymbol 0 - 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R
            - 4 * Real.sinh (L / 2)) * selfConvolution f 0 := by
  -- the spectral representation
  have hg : ∀ v : ℝ, selfConvolution f v
      = ∫ t : ℝ, specDensity f t * Real.cos (t * v) := fun v =>
    Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hFsq hcont.continuousAt
  have hWA' : Integrable fun t : ℝ => specDensity f t * (archSymbol t - archSymbol 0) := by
    have : (fun t : ℝ => specDensity f t * (archSymbol t - archSymbol 0))
        = (fun t : ℝ => specDensity f t * archSymbol t)
          - fun t : ℝ => archSymbol 0 * specDensity f t := by
      funext t; simp only [Pi.sub_apply]; ring
    rw [this]
    exact hWA.sub (hWi.const_mul _)
  have harch := Cvs.WeilForm.Archimedean.ArchSpectralDensity.arch_of_spectral hWi hg hWA' hprod
  -- the symbol's floor and its tail
  have hmass : (∫ t : ℝ, specDensity f t) = selfConvolution f 0 :=
    integral_specDensity hfint hgint hcont.continuousAt hFsq
  have htail := arch_ge_tail (W := specDensity f) (specDensity_nonneg f) hWi hWA hc
  rw [hmass] at htail
  -- the pole term and the prime side
  have hpole := Cvs.WeilForm.PoleTermCauchySchwarz.neg_le_poleTerm hL hsupp hsq hA hM
  have hprime : primePowerSideTruncated P R (selfConvolution f)
      ≤ 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R * selfConvolution f 0 :=
    le_trans (le_abs_self _)
      (Cvs.WeilForm.PrimeSideBoundedBelow.abs_primePowerSideTruncated_le P R hsq hcross)
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, harch]
  linarith [htail, hpole, hprime]

end Cvs.WeilForm.HighFrequencyMassBound
