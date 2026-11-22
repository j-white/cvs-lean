import Mathlib
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Lévy domain is the spectral domain

    `IntegrableOn (levy f) (Ioi 0)  ↔  ∫⁻ ofReal (specDensity f · (archSymbol − archSymbol 0)) < ∞`

for window functions, together with the sum, scalar and almost-everywhere rules for the
spectral density and for the window representative that make this domain a subspace.
-/

noncomputable section

open MeasureTheory Real FourierTransform Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.LevyDomainSpectral

/-- **The spectral density is insensitive to null sets.** -/
theorem specDensity_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity f = Cvs.WeilForm.SelfConvolutionCosine.specDensity g := by
  funext t
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  have hc : Cvs.WeilForm.SelfConvolutionTransform.cf f =ᵐ[volume] Cvs.WeilForm.SelfConvolutionTransform.cf g := by
    filter_upwards [h] with x hx
    simp [Cvs.WeilForm.SelfConvolutionTransform.cf, hx]
  rw [Real.fourier_congr_ae hc]

/-- **The spectral density of a sum**, by `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem specDensity_add_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (f + g) t
      ≤ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t + 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity g t := by
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  have hcf : Cvs.WeilForm.SelfConvolutionTransform.cf (f + g)
      = Cvs.WeilForm.SelfConvolutionTransform.cf f + Cvs.WeilForm.SelfConvolutionTransform.cf g := by
    funext x; simp [Cvs.WeilForm.SelfConvolutionTransform.cf]
  have hadd : 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f + Cvs.WeilForm.SelfConvolutionTransform.cf g)
      = 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) + 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf g) :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar (by fun_prop)
      (hf.ofReal : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f)) (hg.ofReal)
  rw [hcf, hadd, Pi.add_apply]
  set A := 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) (t / (2 * π))
  set B := 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf g) (t / (2 * π))
  have hsq : ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    have h1 := norm_add_le A B
    have h2 := norm_nonneg A
    have h3 := norm_nonneg B
    nlinarith [sq_nonneg (‖A‖ - ‖B‖), norm_nonneg (A + B)]
  have hpi : (0:ℝ) < 2 * π := by positivity
  calc ‖A + B‖ ^ 2 / (2 * π) ≤ (2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2) / (2 * π) :=
        div_le_div_of_nonneg_right hsq hpi.le
    _ = 2 * (‖A‖ ^ 2 / (2 * π)) + 2 * (‖B‖ ^ 2 / (2 * π)) := by ring

/-- **The spectral density of a scalar multiple.** -/
theorem specDensity_smul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => c * f x) t
      = c ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  have hcf : Cvs.WeilForm.SelfConvolutionTransform.cf (fun x => c * f x)
      = (c : ℂ) • Cvs.WeilForm.SelfConvolutionTransform.cf f := by
    funext x; simp [Cvs.WeilForm.SelfConvolutionTransform.cf]
  have hsm : 𝓕 ((c : ℂ) • Cvs.WeilForm.SelfConvolutionTransform.cf f) = (c : ℂ) • 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) :=
    VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) (Cvs.WeilForm.SelfConvolutionTransform.cf f) c
  rw [hcf, hsm, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **The representative of a window class is integrable.** -/
theorem integrable_rep {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Integrable (Cvs.WeilForm.WindowRepresentative.rep φ) :=
  Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)
    (Cvs.WeilForm.WindowRepresentative.rep_supp φ)

/-- **Representatives add**, almost everywhere. -/
theorem rep_add_ae {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (φ + ψ)
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ := by
  have h : Cvs.WeilForm.WindowRepresentative.fn (φ + ψ)
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.fn φ + Cvs.WeilForm.WindowRepresentative.fn ψ := by
    unfold Cvs.WeilForm.WindowRepresentative.fn
    rw [Submodule.coe_add]
    exact Lp.coeFn_add _ _
  filter_upwards [h] with x hx
  simp only [Cvs.WeilForm.WindowRepresentative.rep, Set.indicator_apply, Pi.add_apply]
  split_ifs <;> simp [hx]

/-- **Representatives scale**, almost everywhere. -/
theorem rep_smul_ae {L : ℝ} (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (c • φ)
      =ᵐ[volume] fun x => c * Cvs.WeilForm.WindowRepresentative.rep φ x := by
  have h : Cvs.WeilForm.WindowRepresentative.fn (c • φ)
      =ᵐ[volume] c • Cvs.WeilForm.WindowRepresentative.fn φ := by
    unfold Cvs.WeilForm.WindowRepresentative.fn
    rw [Submodule.coe_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [h] with x hx
  simp only [Cvs.WeilForm.WindowRepresentative.rep, Set.indicator_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  split_ifs <;> simp [hx]

/-- **The Lévy domain is the spectral domain.**  The Lévy integrand is nonnegative, so its
integrability is the finiteness of its `lintegral`, which the Lévy identity equates with the
spectral one. -/
theorem levyDom_iff {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ)) (hint : Integrable f)
    (hsq : Integrable fun s => f s ^ 2)
    (hcross : ∀ u : ℝ, Integrable fun s => f s * f (s + u)) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)
      ↔ ∫⁻ t, ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t *
          (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) < ⊤ := by
  have hmeas : AEStronglyMeasurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f)
      (volume.restrict (Set.Ioi 0)) :=
    Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun u hu =>
      Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg hsq hcross hu
  have hid := Cvs.WeilForm.Archimedean.LevyTonelli.lintegral_levy_eq hf hint
  constructor
  · intro h
    rw [← hid]
    exact (hasFiniteIntegral_iff_ofReal hnn).mp h.2
  · intro h
    exact ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).mpr (hid ▸ h)⟩

end Cvs.WeilForm.LevyDomainSpectral
