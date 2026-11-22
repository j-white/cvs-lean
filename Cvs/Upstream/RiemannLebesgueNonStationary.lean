import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Riemann–Lebesgue lemma with a non-stationary phase

`∫ g(v) cos(cv) dv → 0` and `∫ g(v) sin(cv) dv → 0` as `c → ∞` for integrable `g`; and if `ψ` is injective with
non-vanishing derivative on a measurable `s`, `∫_s g cos(cψ) → 0` and `∫_s g sin(cψ) → 0`, by `y = ψ(x)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology FourierTransform

namespace Cvs.Upstream.RiemannLebesgueNonStationary

theorem tendsto_fourier_atTop (g : ℝ → ℝ) :
    Tendsto (fun c : ℝ => ∫ v : ℝ, 𝐞 (-(v * (c / (2 * π)))) • ((g v : ℝ) : ℂ)) atTop (𝓝 0) := by
  have h := Real.tendsto_integral_exp_smul_cocompact (fun v => ((g v : ℝ) : ℂ))
  have hc : Tendsto (fun c : ℝ => c / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  exact h.comp hc

theorem fourierChar_smul (v c : ℝ) (y : ℝ) :
    𝐞 (-(v * (c / (2 * π)))) • ((y : ℝ) : ℂ) =
      ((y * Real.cos (c * v) : ℝ) : ℂ) - ((y * Real.sin (c * v) : ℝ) : ℂ) * Complex.I := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  have e : (((2 * π * -(v * (c / (2 * π))) : ℝ) : ℂ) * Complex.I) = ((-(c * v) : ℝ) : ℂ) * Complex.I := by
    congr 2; field_simp
  rw [e, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **Riemann–Lebesgue**: `∫ g(v) cos(cv) dv → 0` for integrable `g`. -/
theorem tendsto_integral_mul_cos {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun c : ℝ => ∫ v, g v * Real.cos (c * v)) atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto 0).comp (tendsto_fourier_atTop g)
  simp only [Complex.zero_re] at h
  refine h.congr fun c => ?_
  simp only [Function.comp]
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Complex.reCLM_apply, fourierChar_smul]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring
  · simp_rw [fourierChar_smul]
    refine Integrable.sub ?_ ?_
    · exact (hg.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)).ofReal
    · exact ((hg.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_sin_le_one _)).ofReal).mul_const _

/-- **Riemann–Lebesgue**: `∫ g(v) sin(cv) dv → 0` for integrable `g`. -/
theorem tendsto_integral_mul_sin {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun c : ℝ => ∫ v, g v * Real.sin (c * v)) atTop (𝓝 0) := by
  have h := ((Complex.continuous_im.tendsto 0).comp (tendsto_fourier_atTop g)).neg
  simp only [Complex.zero_im, neg_zero] at h
  refine h.congr fun c => ?_
  simp only [Function.comp]
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm, ← integral_neg]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Complex.imCLM_apply, fourierChar_smul]
    simp only [Complex.sub_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring
  · simp_rw [fourierChar_smul]
    refine Integrable.sub ?_ ?_
    · exact (hg.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)).ofReal
    · exact ((hg.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact abs_sin_le_one _)).ofReal).mul_const _

/-- The change of variables `y = ψ(x)` for an oscillatory set integral. -/
theorem setIntegral_comp_eq {s : Set ℝ} (hs : MeasurableSet s) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ x ∈ s, HasDerivWithinAt ψ (ψ' x) s x) (hinj : InjOn ψ s) (hne : ∀ x ∈ s, ψ' x ≠ 0)
    {g : ℝ → ℝ} (hg : IntegrableOn g s) (k : ℝ → ℝ) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ c : ℝ, ∫ x in s, g x * k (c * ψ x) = ∫ y, G y * k (c * y) := by
  set G₀ : ℝ → ℝ := fun y => g (Function.invFunOn ψ s y) / |ψ' (Function.invFunOn ψ s y)| with hG₀
  have hG₀ψ : ∀ x ∈ s, G₀ (ψ x) = g x / |ψ' x| := fun x hx => by
    simp only [hG₀, hinj.leftInvOn_invFunOn hx]
  have hcont : ContinuousOn ψ s := fun x hx => (hψ x hx).continuousWithinAt
  have ht : MeasurableSet (ψ '' s) := hs.image_of_continuousOn_injOn hcont hinj
  have hiG : IntegrableOn G₀ (ψ '' s) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hs hψ hinj]
    refine hg.congr_fun (fun x hx => ?_) hs
    rw [hG₀ψ x hx, smul_eq_mul]
    have : |ψ' x| ≠ 0 := abs_ne_zero.2 (hne x hx)
    field_simp
  refine ⟨(ψ '' s).indicator G₀, (integrable_indicator_iff ht).2 hiG, fun c => ?_⟩
  have e1 : ∫ y, (ψ '' s).indicator G₀ y * k (c * y) = ∫ y in ψ '' s, G₀ y * k (c * y) := by
    rw [← integral_indicator ht]
    congr 1; ext y
    by_cases hy : y ∈ ψ '' s
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
  rw [e1, integral_image_eq_integral_abs_deriv_smul hs hψ hinj]
  refine setIntegral_congr_fun hs fun x hx => ?_
  simp only [smul_eq_mul]
  rw [hG₀ψ x hx]
  have : |ψ' x| ≠ 0 := abs_ne_zero.2 (hne x hx)
  field_simp

/-- **Non-stationary Riemann–Lebesgue**: `∫_s g cos(cψ) → 0`. -/
theorem tendsto_setIntegral_mul_cos_comp {s : Set ℝ} (hs : MeasurableSet s) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ x ∈ s, HasDerivWithinAt ψ (ψ' x) s x) (hinj : InjOn ψ s) (hne : ∀ x ∈ s, ψ' x ≠ 0)
    {g : ℝ → ℝ} (hg : IntegrableOn g s) :
    Tendsto (fun c : ℝ => ∫ x in s, g x * Real.cos (c * ψ x)) atTop (𝓝 0) := by
  obtain ⟨G, hG, he⟩ := setIntegral_comp_eq hs hψ hinj hne hg Real.cos
  simp_rw [he]
  exact tendsto_integral_mul_cos hG

/-- **Non-stationary Riemann–Lebesgue**: `∫_s g sin(cψ) → 0`. -/
theorem tendsto_setIntegral_mul_sin_comp {s : Set ℝ} (hs : MeasurableSet s) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ x ∈ s, HasDerivWithinAt ψ (ψ' x) s x) (hinj : InjOn ψ s) (hne : ∀ x ∈ s, ψ' x ≠ 0)
    {g : ℝ → ℝ} (hg : IntegrableOn g s) :
    Tendsto (fun c : ℝ => ∫ x in s, g x * Real.sin (c * ψ x)) atTop (𝓝 0) := by
  obtain ⟨G, hG, he⟩ := setIntegral_comp_eq hs hψ hinj hne hg Real.sin
  simp_rw [he]
  exact tendsto_integral_mul_sin hG

end Cvs.Upstream.RiemannLebesgueNonStationary

end
