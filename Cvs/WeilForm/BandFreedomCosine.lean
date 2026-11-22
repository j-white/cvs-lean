import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.TruncatedEffectiveSymbol
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Band freedom: cosine transforms of measures carried by `|v| ≥ L` are invisible to windows of length `L`

For `f, g ∈ L¹ ∩ L²` vanishing off `[a, b]`, `polar f g v = 2∫ ρ_{f,g}(t) cos(tv) dt` vanishes at every
`|v| ≥ b − a`, boundary included, so `h = Re(μ̂ − ν̂)`, `μ̂(t) = ∫ e^{itv} dμ`, with `μ, ν` finite and null on
`(−L, L)` has `∫ h ρ_{f,g} = 0` once `b − a ≤ L`. These `h` form the submodule `bandFree L`, antitone in
`L`, holding `cos(tw)` for `|w| ≥ L` and cosine transforms of integrable densities vanishing on `(−L, L)`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.Zeta.Explicit.Weil
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

namespace Cvs.WeilForm.BandFreedomCosine

variable {f g : ℝ → ℝ}

/-! ### The cross density as a cosine transform -/

/-- `ρ_{f,g} = (ρ_{f+g} − ρ_f − ρ_g)/2` for integrable `f, g`. -/
theorem crossSpec_eq (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    crossSpec f g t = (specDensity (fun x => f x + g x) t - specDensity f t - specDensity g t) / 2 := by
  have h := Cvs.L2a.FullTailPolarisation.specDensity_add_smul hf hg 1 t
  simp only [one_mul, one_pow, mul_one] at h
  rw [h]; ring

/-- `ρ_{f,g}` is continuous for integrable `f, g`. -/
theorem continuous_crossSpec (hf : Integrable f) (hg : Integrable g) : Continuous (crossSpec f g) := by
  rw [show crossSpec f g = fun t => (specDensity (fun x => f x + g x) t - specDensity f t
      - specDensity g t) / 2 from funext (crossSpec_eq hf hg)]
  exact (((Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity (hf.add hg)).sub
    (Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hf)).sub
    (Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hg)).div_const 2

/-- `ρ_{f,g}` is integrable for `f, g ∈ L¹ ∩ L²`. -/
theorem integrable_crossSpec (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) : Integrable (crossSpec f g) := by
  rw [show crossSpec f g = fun t => (specDensity (fun x => f x + g x) t - specDensity f t
      - specDensity g t) / 2 from funext (crossSpec_eq hf1 hg1)]
  exact (((Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity (hf2.add hg2) (hf1.add hg1)).sub
    (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1)).sub
    (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hg2 hg1)).div_const 2

/-- `S_f(v) = ∫ ρ_f(t) cos(tv) dt` for `f ∈ L¹ ∩ L²`. -/
theorem selfConvolution_eq_integral (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (v : ℝ) :
    selfConvolution f v = ∫ t, specDensity f t * Real.cos (t * v) :=
  Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hf1
    (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hf1)
    (Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf2 hf1)
    (Complex.continuous_ofReal.comp (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf2)).continuousAt

/-- **The cross-convolution is the cosine transform of the cross density**:
`polar f g v = 2∫ ρ_{f,g}(t) cos(tv) dt` for `f, g ∈ L¹ ∩ L²`. -/
theorem polar_eq_integral (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) (v : ℝ) :
    Cvs.WeilForm.TruncatedFormPolarised.polar f g v = 2 * ∫ t, crossSpec f g t * Real.cos (t * v) := by
  have hs1 : Integrable (fun x => f x + g x) := hf1.add hg1
  have hs2 : MemLp (fun x => f x + g x) 2 volume := hf2.add hg2
  have hA := Cvs.WeilForm.TruncatedEffectiveSymbol.specDensity_cos_integrable hs2 hs1 v
  have hB := Cvs.WeilForm.TruncatedEffectiveSymbol.specDensity_cos_integrable hf2 hf1 v
  have hC := Cvs.WeilForm.TruncatedEffectiveSymbol.specDensity_cos_integrable hg2 hg1 v
  have e : (∫ t, crossSpec f g t * Real.cos (t * v))
      = (∫ t, specDensity (fun x => f x + g x) t * Real.cos (t * v)
          - specDensity f t * Real.cos (t * v) - specDensity g t * Real.cos (t * v)) / 2 := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only [crossSpec_eq hf1 hg1 t]; ring)
  rw [Cvs.WeilForm.TruncatedFormPolarised.polar_eq_selfConvolution hf2 hg2, selfConvolution_eq_integral hs1 hs2,
    selfConvolution_eq_integral hf1 hf2, selfConvolution_eq_integral hg1 hg2, e, integral_sub _ hC,
    integral_sub hA hB]
  · ring
  · exact hA.sub hB

/-! ### Vanishing at displacements beyond the support -/

/-- The cross-convolution of two functions vanishing off `[a, b]` vanishes at every `|v| ≥ b − a`. -/
theorem crossConv_eq_zero_of_support {a b v : ℝ} (hfs : ∀ x ∉ Icc a b, f x = 0)
    (hgs : ∀ x ∉ Icc a b, g x = 0) (hv : b - a ≤ |v|) : Cvs.WeilForm.TruncatedFormPolarised.crossConv f g v = 0 := by
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({a, b} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (((Set.finite_singleton b).insert a).measure_zero _)
  unfold Cvs.WeilForm.TruncatedFormPolarised.crossConv
  refine integral_eq_zero_of_ae (hnull.mono fun x hx => ?_)
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
  show f x * g (x + v) = 0
  by_cases hxs : x ∈ Icc a b
  · have hax : a < x := lt_of_le_of_ne hxs.1 (Ne.symm hx.1)
    have hxb : x < b := lt_of_le_of_ne hxs.2 hx.2
    refine mul_eq_zero_of_right _ (hgs _ fun h => ?_)
    rcases le_total 0 v with h0 | h0
    · rw [abs_of_nonneg h0] at hv; linarith [h.2]
    · rw [abs_of_nonpos h0] at hv; linarith [h.1]
  · rw [hfs x hxs, zero_mul]

/-- **The boundary-inclusive vanishing**: `polar f g v = 0` at every `|v| ≥ b − a` for `f, g` vanishing
off `[a, b]`. -/
theorem polar_eq_zero_of_support {a b v : ℝ} (hfs : ∀ x ∉ Icc a b, f x = 0)
    (hgs : ∀ x ∉ Icc a b, g x = 0) (hv : b - a ≤ |v|) : Cvs.WeilForm.TruncatedFormPolarised.polar f g v = 0 := by
  rw [Cvs.WeilForm.TruncatedFormPolarised.polar, crossConv_eq_zero_of_support hfs hgs hv,
    crossConv_eq_zero_of_support hgs hfs hv, add_zero]

/-! ### Cosine transforms of finite measures against the cross density -/

/-- `v ↦ cos(tv)` is integrable against a finite measure. -/
theorem integrable_cos_mul (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun v => Real.cos (t * v)) μ :=
  Integrable.of_bound (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable 1
    (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)

/-- `(t, v) ↦ cos(tv) ρ_{f,g}(t)` is integrable on `ℝ × ℝ` against Lebesgue times a finite measure. -/
theorem integrable_cos_mul_crossSpec (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun p : ℝ × ℝ => Real.cos (p.1 * p.2) * crossSpec f g p.1) ((volume : Measure ℝ).prod μ) := by
  have h := (integrable_crossSpec hf1 hf2 hg1 hg2).norm.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  refine h.mono' ((Real.continuous_cos.comp (continuous_fst.mul continuous_snd)).mul
    ((continuous_crossSpec hf1 hg1).comp continuous_fst)).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  simp only [norm_mul, mul_one, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)

/-- `t ↦ (∫ cos(tv) dμ(v)) ρ_{f,g}(t)` is integrable for a finite measure `μ`. -/
theorem integrable_cosTransform_mul_crossSpec (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable fun t => (∫ v, Real.cos (t * v) ∂μ) * crossSpec f g t :=
  (integrable_cos_mul_crossSpec hf1 hf2 hg1 hg2 μ).integral_prod_left.congr
    (Eventually.of_forall fun t => by dsimp only; exact integral_mul_const _ _)

/-- **Fubini against a finite measure**: `∫ (∫ cos(tv) dμ(v)) ρ_{f,g}(t) dt = ½∫ polar f g dμ`. -/
theorem integral_cosTransform_mul_crossSpec (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∫ t, (∫ v, Real.cos (t * v) ∂μ) * crossSpec f g t
      = (∫ v, Cvs.WeilForm.TruncatedFormPolarised.polar f g v ∂μ) / 2 := by
  calc ∫ t, (∫ v, Real.cos (t * v) ∂μ) * crossSpec f g t
      = ∫ t, ∫ v, Real.cos (t * v) * crossSpec f g t ∂μ :=
        integral_congr_ae (Eventually.of_forall fun t => (integral_mul_const _ _).symm)
    _ = ∫ v, ∫ t, Real.cos (t * v) * crossSpec f g t ∂volume ∂μ :=
        integral_integral_swap (f := fun t v => Real.cos (t * v) * crossSpec f g t)
          (integrable_cos_mul_crossSpec hf1 hf2 hg1 hg2 μ)
    _ = ∫ v, Cvs.WeilForm.TruncatedFormPolarised.polar f g v / 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [polar_eq_integral hf1 hf2 hg1 hg2 v]
        simp_rw [mul_comm (Real.cos _) (crossSpec f g _)]
        ring
    _ = _ := integral_div _ _

/-! ### The band-free multipliers -/

/-- **The band-free multipliers at length `L`**: `h(t) = ∫ cos(tv) dμ(v) − ∫ cos(tv) dν(v)` with `μ, ν`
finite and `μ(−L, L) = ν(−L, L) = 0`. -/
def bandFree (L : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {h | ∃ μ ν : Measure ℝ, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ (Ioo (-L) L) = 0 ∧
    ν (Ioo (-L) L) = 0 ∧ ∀ t, h t = (∫ v, Real.cos (t * v) ∂μ) - ∫ v, Real.cos (t * v) ∂ν}
  zero_mem' := ⟨0, 0, inferInstance, inferInstance, rfl, rfl, fun t => by simp⟩
  add_mem' := by
    rintro h₁ h₂ ⟨μ₁, ν₁, hμ₁, hν₁, hμ₁0, hν₁0, e₁⟩ ⟨μ₂, ν₂, hμ₂, hν₂, hμ₂0, hν₂0, e₂⟩
    refine ⟨μ₁ + μ₂, ν₁ + ν₂, inferInstance, inferInstance, by simp [hμ₁0, hμ₂0],
      by simp [hν₁0, hν₂0], fun t => ?_⟩
    rw [integral_add_measure (integrable_cos_mul μ₁ t) (integrable_cos_mul μ₂ t),
      integral_add_measure (integrable_cos_mul ν₁ t) (integrable_cos_mul ν₂ t), Pi.add_apply, e₁, e₂]
    ring
  smul_mem' := by
    rintro c h ⟨μ, ν, hμ, hν, hμ0, hν0, e⟩
    rcases le_total 0 c with hc | hc
    · refine ⟨c.toNNReal • μ, c.toNNReal • ν, inferInstance, inferInstance, by simp [hμ0],
        by simp [hν0], fun t => ?_⟩
      rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, Pi.smul_apply, e t,
        NNReal.smul_def, NNReal.smul_def, Real.coe_toNNReal _ hc, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    · refine ⟨(-c).toNNReal • ν, (-c).toNNReal • μ, inferInstance, inferInstance, by simp [hν0],
        by simp [hμ0], fun t => ?_⟩
      rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, Pi.smul_apply, e t,
        NNReal.smul_def, NNReal.smul_def, Real.coe_toNNReal _ (neg_nonneg.2 hc), smul_eq_mul,
        smul_eq_mul, smul_eq_mul]
      ring

/-- `bandFree` is antitone in `L`. -/
theorem bandFree_anti {L L' : ℝ} (hL : L' ≤ L) : bandFree L ≤ bandFree L' := by
  rintro h ⟨μ, ν, hμ, hν, hμ0, hν0, e⟩
  have hs : Ioo (-L') L' ⊆ Ioo (-L) L := Ioo_subset_Ioo (by linarith) hL
  exact ⟨μ, ν, hμ, hν, measure_mono_null hs hμ0, measure_mono_null hs hν0, e⟩

/-- `cos(tw)` is band-free at every `L ≤ |w|`. -/
theorem cos_mem_bandFree {L w : ℝ} (hw : L ≤ |w|) : (fun t => Real.cos (t * w)) ∈ bandFree L := by
  refine ⟨Measure.dirac w, 0, inferInstance, inferInstance, ?_, rfl, fun t => by simp [integral_dirac]⟩
  rw [Measure.dirac_apply' _ measurableSet_Ioo, indicator_of_notMem]
  intro hmem
  exact absurd (abs_lt.2 hmem) (not_lt.2 hw)

/-! ### Band freedom -/

/-- A band-free multiplier times `ρ_{f,g}` is integrable for `f, g ∈ L¹ ∩ L²`. -/
theorem integrable_mul_crossSpec {L : ℝ} {h : ℝ → ℝ} (hh : h ∈ bandFree L) (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    Integrable fun t => h t * crossSpec f g t := by
  obtain ⟨μ, ν, hμ, hν, -, -, e⟩ := hh
  refine ((integrable_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 μ).sub
    (integrable_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 ν)).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, e t]; ring

/-- **Band freedom**: for `h ∈ bandFree L` and `f, g ∈ L¹ ∩ L²` vanishing off `[a, b]` with `b − a ≤ L`,
`∫ h(t) ρ_{f,g}(t) dt = 0`. -/
theorem integral_mul_crossSpec_eq_zero {L a b : ℝ} {h : ℝ → ℝ} (hh : h ∈ bandFree L)
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hg1 : Integrable g) (hg2 : MemLp g 2 volume)
    (hfs : ∀ x ∉ Icc a b, f x = 0) (hgs : ∀ x ∉ Icc a b, g x = 0) (hab : b - a ≤ L) :
    ∫ t, h t * crossSpec f g t = 0 := by
  obtain ⟨μ, ν, hμ, hν, hμ0, hν0, e⟩ := hh
  have hz : ∀ m : Measure ℝ, m (Ioo (-L) L) = 0 → ∫ v, Cvs.WeilForm.TruncatedFormPolarised.polar f g v ∂m = 0 :=
    fun m hm => integral_eq_zero_of_ae ((measure_eq_zero_iff_ae_notMem.1 hm).mono fun v hv =>
      polar_eq_zero_of_support hfs hgs (hab.trans (not_lt.1 fun hlt => hv (abs_lt.1 hlt))))
  rw [show (fun t => h t * crossSpec f g t) = fun t => (∫ v, Real.cos (t * v) ∂μ) * crossSpec f g t
      - (∫ v, Real.cos (t * v) ∂ν) * crossSpec f g t from funext fun t => by rw [e t]; ring,
    integral_sub (integrable_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 μ)
      (integrable_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 ν),
    integral_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 μ,
    integral_cosTransform_mul_crossSpec hf1 hf2 hg1 hg2 ν, hz μ hμ0, hz ν hν0]
  simp

/-- **Band freedom on the diagonal**: `∫ h(t) ρ_f(t) dt = 0` for `h ∈ bandFree L` and `f ∈ L¹ ∩ L²`
vanishing off `[a, b]` with `b − a ≤ L`. -/
theorem integral_mul_specDensity_eq_zero {L a b : ℝ} {h : ℝ → ℝ} (hh : h ∈ bandFree L)
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hfs : ∀ x ∉ Icc a b, f x = 0) (hab : b - a ≤ L) :
    ∫ t, h t * specDensity f t = 0 := by
  simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using
    integral_mul_crossSpec_eq_zero hh hf1 hf2 hf1 hf2 hfs hfs hab

end Cvs.WeilForm.BandFreedomCosine
