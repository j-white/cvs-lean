import Mathlib
import Cvs.Upstream.CompactSupportWeightIntegrable
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.HighFrequencyMassBound
import Cvs.WeilForm.PrimeSideBoundedBelow
import Cvs.WeilForm.ProductIntegrability
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.UnitWindowTransformBounded
import Cvs.WeilForm.WindowFormTranslationInvariant
import Cvs.Zeta.WeilPositivityStatement

/-!
# The tail bound, on the window `(0, L]`

`Cvs.WeilForm.HighFrequencyMassBound` is stated on the centred window; every quantity in it is translation invariant, so it
holds verbatim for a test function supported in `(0, L]`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.TailBoundOnWindow

/-- The spectral density does not see a translation. -/
theorem specDensity_translate (f : ℝ → ℝ) (c : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f (x + c))
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity f := by
  funext t
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  have hcf : (Cvs.WeilForm.SelfConvolutionTransform.cf fun x => f (x + c))
      = fun x : ℝ => (Cvs.WeilForm.SelfConvolutionTransform.cf f) (x + c) := rfl
  rw [hcf, Cvs.WeilForm.UnitWindowTransformBounded.norm_fourier_translate]

/-- The Lévy integrand does not see a translation. -/
theorem levy_translate (f : ℝ → ℝ) (c : ℝ) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (fun x => f (x + c)) = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f := by
  funext u
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  rw [Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate f c 0,
    Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate f c (u / 2)]

/-- **The tail bound on `(0, L]`.** -/
theorem tailMass_le_window {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {f : ℝ → ℝ} {T c : ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ))
    (hc : ∀ t : ℝ, t ∈ Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T →
      c ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t) :
    (c - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        * (∫ t in Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
        - (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
            - 2 * Cvs.WeilForm.PrimeSideBoundedBelow.primeWeightTotal P R
            - 4 * Real.sinh (L / 2)) * selfConvolution f 0 := by
  set g : ℝ → ℝ := fun x => f (x + L / 2) with hg
  have hgsupp : ∀ x, x ∉ Set.Icc (-(L / 2)) (L / 2) → g x = 0 :=
    Cvs.WeilForm.CentredWindowTranslate.support_translate hsupp
  have hgmem : MemLp g 2 (volume : Measure ℝ) := Cvs.WeilForm.CentredWindowTranslate.memLp_translate _ hf
  have hfint : Integrable f (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf hsupp
  have hgint : Integrable g (volume : Measure ℝ) := hfint.comp_add_right (L / 2)
  have hgsq : Integrable (fun s : ℝ => g s ^ 2) (volume : Measure ℝ) := hgmem.integrable_sq
  have hgcross : ∀ u : ℝ, Integrable (fun s : ℝ => g s * g (s + u)) (volume : Measure ℝ) := by
    intro u
    exact hgmem.integrable_mul
      (hgmem.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) u))
  have hgA : Integrable (fun s : ℝ => g s * Real.exp (s / 2)) (volume : Measure ℝ) :=
    Cvs.Upstream.CompactSupportWeightIntegrable.integrable_mul_weight hgint hgsupp
      (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hgM : Integrable (fun s : ℝ => g s * Real.exp (-(s / 2))) (volume : Measure ℝ) :=
    Cvs.Upstream.CompactSupportWeightIntegrable.integrable_mul_weight hgint hgsupp
      (Real.continuous_exp.comp (continuous_id.div_const 2).neg)
  have hgself := Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hgint
  have hgcont : Continuous (fun u : ℝ => ((selfConvolution g u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hgmem)
  have hgFsq := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hgmem hgint
  have hgWi := Cvs.WeilForm.ProductIntegrability.integrable_specDensity hgFsq
  have hgdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Set.Ioi 0) (volume : Measure ℝ) := by
    rw [hg, levy_translate]; exact hdom
  have hgWA := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hgmem hgint hgdom
  have hgWA' : Integrable (fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity g t
      * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t) (volume : Measure ℝ) := by
    have h := hgWA.add (hgWi.const_mul (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  have hgprod := Cvs.WeilForm.ProductIntegrability.integrable_prod_of_arch
    (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg g)
    (Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hgint).measurable hgWA
  have hmain := Cvs.WeilForm.HighFrequencyMassBound.tailMass_le P R hL hgsupp hgint hgsq hgcross hgA hgM
    hgself hgcont hgFsq hgWi hgWA' hgprod hc
  rw [specDensity_translate f (L / 2), Cvs.WeilForm.WindowFormTranslationInvariant.weilForm_translate,
    Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate f (L / 2) 0] at hmain
  exact hmain

end Cvs.WeilForm.TailBoundOnWindow
