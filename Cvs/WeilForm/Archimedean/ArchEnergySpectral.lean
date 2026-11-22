import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionMaximum
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The archimedean energy, on the spectral side, real-valued

    ∫_{u>0} levy f u du  =  ∫ specDensity f t · (archSymbol t − archSymbol 0) dt

`Cvs.WeilForm.Archimedean.LevyTonelli` proves this in `[0,∞]`; both sides are nonnegative and integrable, so it descends.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.ArchEnergySpectral

/-- **The Lévy integrand is nonnegative.**  The density is positive and `Cvs.WeilForm.SelfConvolutionMaximum` caps the
self-convolution by its value at the origin. -/
theorem levy_nonneg {f : ℝ → ℝ}
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    {u : ℝ} (hu : 0 < u) : 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := by
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  have hd : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu
  have hg := Cvs.WeilForm.SelfConvolutionMaximum.selfConvolution_le (f := f) (u / 2) hsq (hcross (u / 2))
  have : 0 ≤ selfConvolution f 0 - selfConvolution f (u / 2) := by linarith
  exact mul_nonneg hd.le this

/-- **The spectral integrand is nonnegative.**  The density is a square and the symbol is
least at the origin. -/
theorem spec_nonneg (f : ℝ → ℝ) (t : ℝ) :
    0 ≤ Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) :=
  mul_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)
    (Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg t)

/-- **The exchange, real-valued.**  This is what puts the window's form on the spectral side,
where the symbol is a multiplier and the eigenvalue question becomes one about it. -/
theorem integral_levy_eq {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ))
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ))
    (hspec : Integrable fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) :
    (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u)
      = ∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) := by
  have hL : (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u)
      = (∫⁻ u in Set.Ioi (0:ℝ),
          ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u)).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_ hdom.aestronglyMeasurable
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun u hu => levy_nonneg hsq hcross hu)
  have hR : (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
        * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
      = (∫⁻ t : ℝ, ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
            - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))).toReal := by
    refine integral_eq_lintegral_of_nonneg_ae ?_ hspec.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => spec_nonneg f t
  rw [hL, hR, Cvs.WeilForm.Archimedean.LevyTonelli.lintegral_levy_eq hf hfint]

/-! ### The form, on the spectral side -/

/-- **The window's form is the symbol against the spectral density, plus the pole, minus the
primes.**  On this side the archimedean part is a multiplier, which is what a second-eigenvalue
bound has to talk about. -/
theorem weilForm_spectral (P R : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ))
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u))
    (hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ))
    (hsd : Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) (volume : Measure ℝ))
    (hspec : Integrable fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
      * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
    (hmass : (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) = selfConvolution f 0) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
      = 2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))
        + (∫ t : ℝ, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
        - primePowerSideTruncated P R (selfConvolution f) := by
  have hsplit : (∫ t : ℝ, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
      = (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t
          * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
        + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
    rw [← integral_const_mul, ← integral_add hspec (hsd.const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, hsplit, hmass,
    ← integral_levy_eq hf hfint hsq hcross hdom hspec]
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  ring

end Cvs.WeilForm.Archimedean.ArchEnergySpectral
