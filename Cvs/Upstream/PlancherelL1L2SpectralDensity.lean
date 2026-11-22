import Mathlib
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# Plancherel on `L¹ ∩ L²`, and the spectral density integrates to the norm

    `∫ ‖𝓕 f‖² = ∫ ‖f‖²`        `∫ specDensity f = ∫ f² = selfConvolution f 0`

so the spectral representation of the Weil form no longer needs to assume it.
-/

noncomputable section

open MeasureTheory FourierTransform Real

namespace Cvs.Upstream.PlancherelL1L2SpectralDensity

/-- **The `L²` norm is the integral of the squared modulus.** -/
theorem norm_sq_eq_integral (φ : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖φ‖ ^ 2 = ∫ x, ‖(φ : ℝ → ℂ) x‖ ^ 2 := by
  have h1 : (inner ℂ φ φ : ℂ) = (‖φ‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K φ
  have h2 : (inner ℂ φ φ : ℂ) = ∫ x, (inner ℂ ((φ : ℝ → ℂ) x) ((φ : ℝ → ℂ) x) : ℂ) :=
    L2.inner_def φ φ
  have h3 : ∀ x, (inner ℂ ((φ : ℝ → ℂ) x) ((φ : ℝ → ℂ) x) : ℂ)
      = (‖(φ : ℝ → ℂ) x‖ : ℂ) ^ 2 := fun x => inner_self_eq_norm_sq_to_K _
  have : (‖φ‖ : ℂ) ^ 2 = ((∫ x, ‖(φ : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h1, h2]; simp only [h3]; norm_cast
  exact_mod_cast this

/-- **Plancherel on `L¹ ∩ L²`.**  The Fourier integral preserves the squared `L²` norm. -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫ x, ‖(𝓕 f) x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hae := Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hf hf2
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf2.toLp f) with hF
  set G : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hG
  have e1 : ∫ x, ‖(𝓕 f) x‖ ^ 2 = ∫ x, ‖(F : ℝ → ℂ) x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have e2 : ‖F‖ = ‖G‖ := Lp.norm_fourier_eq G
  have e3 : ∫ x, ‖(G : ℝ → ℂ) x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  rw [e1, ← norm_sq_eq_integral, e2, norm_sq_eq_integral, e3]

/-- **The spectral density integrates to the squared norm.**  The frequency is scaled by `2π`,
and the density carries the compensating `1/(2π)`. -/
theorem integral_specDensity {f : ℝ → ℝ} (hf : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t = ∫ x, (f x) ^ 2 := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set g : ℝ → ℝ := fun ξ => ‖(𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f)) ξ‖ ^ 2 with hg
  have hsd : ∀ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t = g (t / (2 * π)) / (2 * π) :=
    fun t => rfl
  simp only [hsd]
  rw [integral_div, Measure.integral_comp_div g (2 * π), abs_of_pos hpi, smul_eq_mul,
    mul_div_cancel_left₀ _ hpi.ne']
  have hc : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f) := hf.ofReal
  have hc2 : MemLp (Cvs.WeilForm.SelfConvolutionTransform.cf f) 2 (volume : Measure ℝ) := hf2.ofReal
  simp only [hg]
  rw [integral_norm_sq_fourier hc hc2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.norm_real, sq_abs]

/-- **In the form the spectral representation asks for.** -/
theorem integral_specDensity_eq_selfConvolution {f : ℝ → ℝ} (hf : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t = Cvs.Zeta.Explicit.Weil.selfConvolution f 0 := by
  rw [integral_specDensity hf hf2]
  unfold Cvs.Zeta.Explicit.Weil.selfConvolution
  simp [pow_two]

/-- **The spectral representation of the Weil form**, with Plancherel supplied rather than
assumed. -/
theorem weilForm_spectral (P R : ℕ) {f : ℝ → ℝ}
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hf : Integrable f)
    (hsq : Integrable (fun s => f s ^ 2))
    (hcross : ∀ u : ℝ, Integrable (fun s => f s * f (s + u)))
    (hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0))
    (hsd : Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f))
    (hsda : Integrable (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t *
      (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f =
      ((2 * ∫ x, f x * Real.exp (x / 2)) * ∫ x, f x * Real.exp (-(x / 2)))
        + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
        - Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution f) :=
  Cvs.WeilForm.Archimedean.ArchEnergySpectral.weilForm_spectral P R hf2 hf hsq hcross hlevy hsd hsda
    (integral_specDensity_eq_selfConvolution hf hf2)

end Cvs.Upstream.PlancherelL1L2SpectralDensity
