import Mathlib
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-!
# The complexification of a real `L²` class is an isometry, and its transform

    `‖emb φ‖ = ‖φ‖`        `𝓕 (emb φ) =ᵐ 𝓕 (cf f)`   for any integrable representative `f`

so the `L²` Fourier machinery applies to the real window through `emb`.
-/

noncomputable section

open MeasureTheory FourierTransform

namespace Cvs.Upstream.ComplexificationIsometryL2

/-- **The complexification** of a real `L²` class. -/
def emb : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure ℝ) :=
  Complex.ofRealCLM.compLpL 2 volume

/-- It is the pointwise complexification, almost everywhere. -/
theorem emb_ae (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    ((emb φ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun x => (((φ : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLp' (p := 2) (μ := volume) φ] with x hx
  exact hx

/-- **The complexification preserves the norm.** -/
theorem norm_emb (φ : Lp ℝ 2 (volume : Measure ℝ)) : ‖emb φ‖ = ‖φ‖ := by
  have h1 : ‖emb φ‖ ^ 2 = ∫ x, ‖((emb φ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ ^ 2 :=
    Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral _
  have h2 : ∫ x, ‖((emb φ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ ^ 2
      = ∫ x, ((φ : ℝ → ℝ) x) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [emb_ae φ] with x hx
    rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h3 : ‖φ‖ ^ 2 = ∫ x, ((φ : ℝ → ℝ) x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [pow_two])
  have : ‖emb φ‖ ^ 2 = ‖φ‖ ^ 2 := by rw [h1, h2, h3]
  calc ‖emb φ‖ = Real.sqrt (‖emb φ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖φ‖ ^ 2) := by rw [this]
    _ = ‖φ‖ := Real.sqrt_sq (norm_nonneg _)

/-- **It is an isometry.** -/
theorem isometry_emb : Isometry emb := by
  refine Isometry.of_dist_eq fun φ ψ => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_emb]

/-- **The transform of the complexification is the Fourier integral of any integrable
representative.** -/
theorem fourier_emb_ae {φ : Lp ℝ 2 (volume : Measure ℝ)} {f : ℝ → ℝ}
    (hae : (φ : ℝ → ℝ) =ᵐ[volume] f) (hf : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((𝓕 (emb φ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) := by
  have hcf2 : MemLp (Cvs.WeilForm.SelfConvolutionTransform.cf f) 2 (volume : Measure ℝ) := hf2.ofReal
  have heq : emb φ = hcf2.toLp _ := by
    apply Lp.ext
    filter_upwards [emb_ae φ, hae, hcf2.coeFn_toLp] with x h1 h2 h3
    rw [h1, h3, h2]
    rfl
  rw [heq]
  exact Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq
    (hf.ofReal : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f)) hcf2

/-- **On the window**, against the representative. -/
theorem fourier_emb_window {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ((𝓕 (emb (φ : Lp ℝ 2 (volume : Measure ℝ))) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.WeilForm.WindowRepresentative.rep φ)) :=
  fourier_emb_ae (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ) (Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ)
    (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)

end Cvs.Upstream.ComplexificationIsometryL2
