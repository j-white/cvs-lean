import Mathlib
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.LogPositionLevelForm
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.GradedArchFloor
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.EffectiveSymbolThreeFacts
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Spectral mass and the per-level leak

`specMass G K = ∫_{|t|<K} specDensity (logScale G)`; `√specMass` is subadditive (Minkowski), `∫ρ log⁺(|t|/T)` is the
level integral `∫_{k>1} (N − specMass F (kT))/k` (Tonelli), and with `LogPositionLevelForm`'s level form of `logPos`, a far-part bound
`specMass (posTail Φ X − posTail Φ k) (kT) ≤ ε(k)N` on `[k₁, X]` gives
`logPos Φ X ≤ ∫ρ log⁺(|t|/T) + (log k₁ + ∫_{k₁}^X min 1 (2√ε(k))/k) N`.
-/

namespace Cvs.L2a.SpectralMassLevelLeak

open Real Set MeasureTheory Cvs.L2a.TailLogScaleTest Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity
open Cvs.WeilForm.SelfConvolutionCosine (specDensity specDensity_nonneg)
open scoped FourierTransform

/-- The low-pass spectral mass `∫_{|t|<K} specDensity (logScale G)`. -/
noncomputable def specMass (G : ℝ → ℝ) (K : ℝ) : ℝ :=
  ∫ t in {t : ℝ | |t| < K}, specDensity (logScale G) t

/-- The set `{t | |t| < K}` is measurable. -/
theorem measurableSet_abs_lt (K : ℝ) : MeasurableSet {t : ℝ | |t| < K} :=
  measurableSet_lt measurable_abs measurable_const

/-- The spectral mass is nonnegative. -/
theorem specMass_nonneg (G : ℝ → ℝ) (K : ℝ) : 0 ≤ specMass G K :=
  setIntegral_nonneg (measurableSet_abs_lt K) fun t _ => specDensity_nonneg _ t

/-- The spectral mass is at most the total mass `∫_{θ>1} G²` (Plancherel). -/
theorem specMass_le {G : ℝ → ℝ} (hG : ∀ θ ≤ 1, G θ = 0) (h2 : MemLp (logScale G) 2 volume)
    (h1 : Integrable (logScale G) volume) (K : ℝ) : specMass G K ≤ ∫ θ in Ioi 1, G θ ^ 2 := by
  rw [← integral_sq G hG, ← Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2]
  exact setIntegral_le_integral (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1)
    (Filter.Eventually.of_forall fun t => specDensity_nonneg _ t)

/-- The integrand of the Fourier transform of an integrable real function is integrable. -/
theorem integrable_fourier_integrand {f : ℝ → ℝ} (hf : Integrable f) (w : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • Cvs.WeilForm.SelfConvolutionTransform.cf f v) := by
  have hc : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  refine Integrable.mono' hf.norm (hc.aestronglyMeasurable.smul hf.ofReal.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simp [Cvs.WeilForm.SelfConvolutionTransform.cf]

/-- The Fourier transform of the complexified sum of two integrable real functions is the sum of the transforms. -/
theorem fourier_cf_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (f + g)) w
      = 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w + 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf g) w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_add (integrable_fourier_integrand hf w)
      (integrable_fourier_integrand hg w)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Pi.add_apply, Complex.ofReal_add, smul_add]

/-- **Pointwise Minkowski**: `√specDensity` is subadditive on integrable functions. -/
theorem sqrt_specDensity_add_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    √(specDensity (f + g) t) ≤ √(specDensity f t) + √(specDensity g t) := by
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  have e : ∀ h : ℝ → ℝ, √(specDensity h t) = ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf h) (t / (2 * π))‖ / √(2 * π) := by
    intro h
    rw [specDensity, Real.sqrt_div' _ hpi, Real.sqrt_sq (norm_nonneg _)]
  rw [e, e, e, ← add_div, fourier_cf_add hf hg]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)

/-- **Minkowski in `L²`** for nonnegative square-integrable functions. -/
theorem sqrt_integral_add_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpm : AEStronglyMeasurable p μ) (hqm : AEStronglyMeasurable q μ)
    (hp : Integrable (fun x => p x ^ 2) μ) (hq : Integrable (fun x => q x ^ 2) μ) :
    √(∫ x, (p x + q x) ^ 2 ∂μ) ≤ √(∫ x, p x ^ 2 ∂μ) + √(∫ x, q x ^ 2 ∂μ) := by
  have hpq : Integrable (fun x => p x * q x) μ := by
    refine Integrable.mono' ((hp.add hq).div_const 2) (hpm.mul hqm) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 x) (hq0 x))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (p x - q x)]
  have hCS : ∫ x, p x * q x ∂μ ≤ √(∫ x, p x ^ 2 ∂μ) * √(∫ x, q x ^ 2 ∂μ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall hp0) (Filter.Eventually.of_forall hq0)
      (by rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq hpm).mpr hp)
      (by rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq hqm).mpr hq)
    simp only [Real.rpow_two] at h
    rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hexp : ∫ x, (p x + q x) ^ 2 ∂μ
      = (∫ x, p x ^ 2 ∂μ) + 2 * (∫ x, p x * q x ∂μ) + ∫ x, q x ^ 2 ∂μ := by
    have e1 : ∫ x, (p x + q x) ^ 2 ∂μ = ∫ x, ((p x ^ 2 + 2 * (p x * q x)) + q x ^ 2) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have h12 : Integrable (fun x => p x ^ 2 + 2 * (p x * q x)) μ := hp.add (hpq.const_mul 2)
    rw [e1, integral_add h12 hq, integral_add hp (hpq.const_mul 2), integral_const_mul]
  have hA := integral_nonneg (μ := μ) (f := fun x => p x ^ 2) fun x => sq_nonneg (p x)
  have hB := integral_nonneg (μ := μ) (f := fun x => q x ^ 2) fun x => sq_nonneg (q x)
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  refine Real.sqrt_le_sqrt ?_
  rw [hexp]
  nlinarith

/-- The log-scale map is additive. -/
theorem logScale_add (G H : ℝ → ℝ) : logScale (G + H) = logScale G + logScale H := by
  funext s; simp only [logScale, Pi.add_apply]; ring

/-- The log-scale map commutes with subtraction. -/
theorem logScale_sub (G H : ℝ → ℝ) : logScale (G - H) = logScale G - logScale H := by
  funext s; simp only [logScale, Pi.sub_apply]; ring

/-- **Minkowski for the spectral mass**: `√specMass` is subadditive on `L¹ ∩ L²` log-scale profiles. -/
theorem sqrt_specMass_add_le {G H : ℝ → ℝ} (h2G : MemLp (logScale G) 2 volume) (h1G : Integrable (logScale G) volume)
    (h2H : MemLp (logScale H) 2 volume) (h1H : Integrable (logScale H) volume) (K : ℝ) :
    √(specMass (G + H) K) ≤ √(specMass G K) + √(specMass H K) := by
  set S := {t : ℝ | |t| < K}
  set f := logScale G
  set g := logScale H
  have hfi := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2G h1G
  have hgi := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2H h1H
  set p : ℝ → ℝ := fun t => √(specDensity f t)
  set q : ℝ → ℝ := fun t => √(specDensity g t)
  have hp2 : (fun t => p t ^ 2) = specDensity f := funext fun t => Real.sq_sqrt (specDensity_nonneg f t)
  have hq2 : (fun t => q t ^ 2) = specDensity g := funext fun t => Real.sq_sqrt (specDensity_nonneg g t)
  have hpm : AEStronglyMeasurable p (volume.restrict S) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hfi.aestronglyMeasurable).restrict
  have hqm : AEStronglyMeasurable q (volume.restrict S) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hgi.aestronglyMeasurable).restrict
  have hpS : Integrable (fun t => p t ^ 2) (volume.restrict S) := by rw [hp2]; exact hfi.restrict
  have hqS : Integrable (fun t => q t ^ 2) (volume.restrict S) := by rw [hq2]; exact hgi.restrict
  have hpqS : Integrable (fun t => (p t + q t) ^ 2) (volume.restrict S) := by
    refine Integrable.mono' ((hpS.add hqS).const_mul 2) ((hpm.add hqm).pow 2)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (p t - q t)]
  have hle : specMass (G + H) K ≤ ∫ t in S, (p t + q t) ^ 2 := by
    rw [specMass, logScale_add]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => specDensity_nonneg _ t) hpqS
      (Filter.Eventually.of_forall fun t => ?_)
    have h := sqrt_specDensity_add_le h1G h1H t
    have h0 := Real.sqrt_nonneg (specDensity (f + g) t)
    calc specDensity (f + g) t = √(specDensity (f + g) t) ^ 2 := (Real.sq_sqrt (specDensity_nonneg _ t)).symm
      _ ≤ (p t + q t) ^ 2 := pow_le_pow_left₀ h0 h 2
  have hM := sqrt_integral_add_sq_le (μ := volume.restrict S) (fun t => Real.sqrt_nonneg _)
    (fun t => Real.sqrt_nonneg _) hpm hqm hpS hqS
  rw [hp2, hq2] at hM
  exact (Real.sqrt_le_sqrt hle).trans hM

/-- The level kernel `1_{kT ≤ |t|} k⁻¹`. -/
theorem levelKer_eq_indicator (T t : ℝ) :
    (fun k : ℝ => if k * T ≤ |t| then k⁻¹ else 0) = {k : ℝ | k * T ≤ |t|}.indicator (fun k => k⁻¹) := by
  funext k; simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- **The layer form of `log⁺`**: `k ↦ 1_{kT ≤ |t|} k⁻¹` is integrable on `(1, ∞)` with integral `max 0 (log(|t|/T))`. -/
theorem logPlus_eq_integral {T : ℝ} (hT : 0 < T) (t : ℝ) :
    IntegrableOn (fun k : ℝ => if k * T ≤ |t| then k⁻¹ else 0) (Ioi 1)
      ∧ ∫ k in Ioi 1, (if k * T ≤ |t| then k⁻¹ else 0) = max 0 (Real.log (|t| / T)) := by
  set b := |t| / T
  have hms : MeasurableSet {k : ℝ | k * T ≤ |t|} := measurableSet_le (measurable_id.mul_const T) measurable_const
  have hset : Ioi 1 ∩ {k : ℝ | k * T ≤ |t|} = Ioc 1 b := by
    ext k; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_ofPred_eq, Set.mem_Ioc, b, le_div_iff₀ hT]
  have hinv : IntegrableOn (fun k : ℝ => k⁻¹) (Ioc 1 b) :=
    ((continuousOn_inv₀.mono fun x (hx : x ∈ Icc 1 b) => ne_of_gt (lt_of_lt_of_le one_pos hx.1)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  rw [levelKer_eq_indicator]
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, integrable_indicator_iff hms, IntegrableOn, Measure.restrict_restrict hms, Set.inter_comm, hset]
    exact hinv
  · rw [setIntegral_indicator hms, hset]
    have hb0 : 0 ≤ b := div_nonneg (abs_nonneg t) hT.le
    rcases le_or_gt 1 b with hb | hb
    · rw [← intervalIntegral.integral_of_le hb, integral_inv_of_pos one_pos (by linarith), div_one,
        max_eq_right (Real.log_nonneg hb)]
    · rw [Set.Ioc_eq_empty (not_lt.mpr hb.le), Measure.restrict_empty, integral_zero_measure,
        max_eq_left (Real.log_nonpos hb0 hb.le)]

/-- The tail-mass layer: `∫ ρ(t) 1_{kT ≤ |t|} k⁻¹ dt = (∫ρ − ∫_{|t|<kT} ρ)/k`, with integrability. -/
theorem integral_mul_levelKer {ρ : ℝ → ℝ} (hρ : Integrable ρ) (T k : ℝ) :
    Integrable (fun t => ρ t * (if k * T ≤ |t| then k⁻¹ else 0))
      ∧ ∫ t, ρ t * (if k * T ≤ |t| then k⁻¹ else 0) = ((∫ t, ρ t) - ∫ t in {t : ℝ | |t| < k * T}, ρ t) / k := by
  have hms : MeasurableSet {t : ℝ | k * T ≤ |t|} := measurableSet_le measurable_const measurable_abs
  have e : (fun t => ρ t * (if k * T ≤ |t| then k⁻¹ else 0))
      = {t : ℝ | k * T ≤ |t|}.indicator (fun t => ρ t * k⁻¹) := by
    funext t; simp only [Set.indicator_apply, Set.mem_ofPred_eq]; split_ifs <;> simp
  have hc : {t : ℝ | |t| < k * T}ᶜ = {t : ℝ | k * T ≤ |t|} := by ext t; simp [not_lt]
  rw [e]
  refine ⟨(hρ.mul_const k⁻¹).indicator hms, ?_⟩
  rw [integral_indicator hms, integral_mul_const, ← hc, ← integral_add_compl (measurableSet_abs_lt (k * T)) hρ]
  ring

/-- **Tonelli for the `log⁺` weight**: `∫⁻ ρ log⁺(|t|/T) = ∫⁻_{k>1} (∫ρ − ∫_{|t|<kT} ρ)/k` for `ρ ≥ 0` integrable. -/
theorem lintegral_mul_logPlus {ρ : ℝ → ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ) {T : ℝ} (hT : 0 < T) :
    ∫⁻ t, ENNReal.ofReal (ρ t * max 0 (Real.log (|t| / T)))
      = ∫⁻ k in Ioi 1, ENNReal.ofReal (((∫ t, ρ t) - ∫ t in {t : ℝ | |t| < k * T}, ρ t) / k) := by
  set h : ℝ → ℝ → ℝ := fun t k => if k * T ≤ |t| then k⁻¹ else 0 with hh
  have hh0 : ∀ t k, 0 < k → 0 ≤ h t k := fun t k hk => by
    simp only [hh]; split_ifs
    · exact inv_nonneg.mpr hk.le
    · exact le_rfl
  have step1 : ∀ t, ENNReal.ofReal (ρ t * max 0 (Real.log (|t| / T)))
      = ∫⁻ k in Ioi 1, ENNReal.ofReal (ρ t * h t k) := by
    intro t
    obtain ⟨hint, heq⟩ := logPlus_eq_integral hT t
    rw [← heq, ← integral_const_mul]
    refine ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun k hk => mul_nonneg (hρ0 t) (hh0 t k (lt_trans one_pos hk)))
  have hmeas : Measurable (fun p : ℝ × ℝ => h p.1 p.2) :=
    Measurable.ite (measurableSet_le (measurable_snd.mul_const T) (measurable_abs.comp measurable_fst))
      measurable_snd.inv measurable_const
  have hAE : AEMeasurable (Function.uncurry fun t k => ENNReal.ofReal (ρ t * h t k))
      (volume.prod (volume.restrict (Ioi 1))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hρ.aemeasurable.comp_fst).mul hmeas.aemeasurable)
  rw [lintegral_congr step1, lintegral_lintegral_swap hAE]
  refine setLIntegral_congr_fun measurableSet_Ioi fun k hk => ?_
  obtain ⟨hint, heq⟩ := integral_mul_levelKer hρ T k
  rw [← heq]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun t => mul_nonneg (hρ0 t) (hh0 t k (lt_trans one_pos hk)))).symm

/-- The low-pass mass `k ↦ ∫_{|t|<kT} ρ` is monotone for `ρ ≥ 0` integrable and `T > 0`. -/
theorem monotone_lowMass {ρ : ℝ → ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ) {T : ℝ} (hT : 0 < T) :
    Monotone fun k : ℝ => ∫ t in {t : ℝ | |t| < k * T}, ρ t := by
  intro k k' hkk'
  refine setIntegral_mono_set hρ.integrableOn (Filter.Eventually.of_forall fun t => hρ0 t) ?_
  exact LE.le.eventuallySubset fun t ht => lt_of_lt_of_le ht (mul_le_mul_of_nonneg_right hkk' hT.le)

/-- **The `log⁺` arch mass in level form**: for `ρ ≥ 0` integrable and `T > 0`,
`∫ ρ(t) max 0 (log(|t|/T)) = ∫_{k>1} (∫ρ − ∫_{|t|<kT} ρ)/k`, and the right integrand is integrable on `(1, ∞)`
whenever the left one is. -/
theorem integral_mul_logPlus_levels {ρ : ℝ → ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ) {T : ℝ} (hT : 0 < T) :
    (Integrable (fun t => ρ t * max 0 (Real.log (|t| / T))) →
        IntegrableOn (fun k => ((∫ t, ρ t) - ∫ t in {t : ℝ | |t| < k * T}, ρ t) / k) (Ioi 1))
      ∧ ∫ t, ρ t * max 0 (Real.log (|t| / T))
        = ∫ k in Ioi 1, ((∫ t, ρ t) - ∫ t in {t : ℝ | |t| < k * T}, ρ t) / k := by
  set H : ℝ → ℝ := fun k => ((∫ t, ρ t) - ∫ t in {t : ℝ | |t| < k * T}, ρ t) / k with hH
  have hHm : Measurable H :=
    (measurable_const.sub (monotone_lowMass hρ0 hρ hT).measurable).div measurable_id
  have hH0 : 0 ≤ᵐ[volume.restrict (Ioi 1)] H := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun k hk => ?_)
    have hle : ∫ t in {t : ℝ | |t| < k * T}, ρ t ≤ ∫ t, ρ t :=
      setIntegral_le_integral hρ (Filter.Eventually.of_forall hρ0)
    exact div_nonneg (by linarith) (le_of_lt (lt_trans one_pos hk))
  have hLm : Measurable fun t : ℝ => max 0 (Real.log (|t| / T)) :=
    measurable_const.max ((measurable_abs.div_const T).log)
  have hL0 : 0 ≤ᵐ[volume] fun t => ρ t * max 0 (Real.log (|t| / T)) :=
    Filter.Eventually.of_forall fun t => mul_nonneg (hρ0 t) (le_max_left _ _)
  have hLs : AEStronglyMeasurable (fun t => ρ t * max 0 (Real.log (|t| / T))) volume :=
    hρ.aestronglyMeasurable.mul hLm.aestronglyMeasurable
  have hlin := lintegral_mul_logPlus hρ0 hρ hT
  refine ⟨fun hint => ⟨hHm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hH0, ← hlin, ← hasFiniteIntegral_iff_ofReal hL0]
    exact hint.2
  · rw [integral_eq_lintegral_of_nonneg_ae hL0 hLs, integral_eq_lintegral_of_nonneg_ae hH0 hHm.aestronglyMeasurable,
      hlin]

/-- **`integral_mul_logPlus_eq`**: for `G` vanishing on `(−∞, 1]` with `logScale G ∈ L¹ ∩ L²` and `T > 0`,
`∫ ρ(t) max 0 (log(|t|/T)) = ∫_{k>1} (N − specMass G (kT))/k` with `ρ = specDensity (logScale G)`, `N = ∫_{θ>1} G²`. -/
theorem integral_mul_logPlus_eq {G : ℝ → ℝ} (hG : ∀ θ ≤ 1, G θ = 0) (h2 : MemLp (logScale G) 2 volume)
    (h1 : Integrable (logScale G) volume) {T : ℝ} (hT : 0 < T) :
    ∫ t, specDensity (logScale G) t * max 0 (Real.log (|t| / T))
      = ∫ k in Ioi 1, ((∫ θ in Ioi 1, G θ ^ 2) - specMass G (k * T)) / k := by
  have hN : ∫ t, specDensity (logScale G) t = ∫ θ in Ioi 1, G θ ^ 2 := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2, integral_sq G hG]
  rw [(integral_mul_logPlus_levels (specDensity_nonneg _) (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1)
    hT).2, hN]
  rfl

/-- The level integrand `(N − specMass G (kT))/k` is integrable on `(1, ∞)` when `ρ log⁺(|t|/T)` is. -/
theorem integrableOn_levels {G : ℝ → ℝ} (hG : ∀ θ ≤ 1, G θ = 0) (h2 : MemLp (logScale G) 2 volume)
    (h1 : Integrable (logScale G) volume) {T : ℝ} (hT : 0 < T)
    (hA : Integrable (fun t => specDensity (logScale G) t * max 0 (Real.log (|t| / T)))) :
    IntegrableOn (fun k => ((∫ θ in Ioi 1, G θ ^ 2) - specMass G (k * T)) / k) (Ioi 1) := by
  have hN : ∫ t, specDensity (logScale G) t = ∫ θ in Ioi 1, G θ ^ 2 := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2, integral_sq G hG]
  have h := (integral_mul_logPlus_levels (specDensity_nonneg _) (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1)
    hT).1 hA
  rw [hN] at h
  exact h

/-- **The per-level leak**: if the far part has `specMass (posTail Φ X − posTail Φ k) K ≤ e N`, then
`specMass (posTail Φ X) K − ∫_{θ>1} (posTail Φ k)² ≤ min 1 (2√e) N`, with `N = ∫_{θ>1} (posTail Φ X)²`. -/
theorem level_leak_le (Φ : ℝ → ℝ) {X k K e : ℝ} (hX : 1 ≤ X) (hΦ : ContDiffOn ℝ 1 Φ (Icc 1 X)) (hk : 1 ≤ k)
    (hkX : k ≤ X)
    (hfar : specMass (posTail Φ X - posTail Φ k) K ≤ e * ∫ θ in Ioi 1, posTail Φ X θ ^ 2) :
    specMass (posTail Φ X) K - ∫ θ in Ioi 1, posTail Φ k θ ^ 2
      ≤ min 1 (2 * √e) * ∫ θ in Ioi 1, posTail Φ X θ ^ 2 := by
  set F := posTail Φ X
  set Fe := posTail Φ k
  set N := ∫ θ in Ioi 1, F θ ^ 2
  set Ne := ∫ θ in Ioi 1, Fe θ ^ 2
  obtain ⟨h2, h1, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX hΦ
  obtain ⟨h2e, h1e, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hk (hΦ.mono (Icc_subset_Icc le_rfl hkX))
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hNe0 : 0 ≤ Ne := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hAN : specMass F K ≤ N := specMass_le (fun θ hθ => posTail_zero Φ X hθ) h2 h1 K
  have hBNe : specMass Fe K ≤ Ne := specMass_le (fun θ hθ => posTail_zero Φ k hθ) h2e h1e K
  have hM : √(specMass F K) ≤ √(specMass Fe K) + √(specMass (F - Fe) K) := by
    have e1 : F = Fe + (F - Fe) := (add_sub_cancel Fe F).symm
    conv_lhs => rw [e1]
    refine sqrt_specMass_add_le h2e h1e ?_ ?_ K
    · rw [logScale_sub]; exact h2.sub h2e
    · rw [logScale_sub]; exact h1.sub h1e
  set A := specMass F K
  set B := specMass Fe K
  set C := specMass (F - Fe) K
  have hA0 := specMass_nonneg F K
  have hB0 := specMass_nonneg Fe K
  have hC0 := specMass_nonneg (F - Fe) K
  have hsA := Real.sq_sqrt hA0
  have hsB := Real.sq_sqrt hB0
  have hsN := Real.sq_sqrt hN0
  have hc : √C ≤ √e * √N := by
    rw [← Real.sqrt_mul' e hN0]; exact Real.sqrt_le_sqrt hfar
  have hr0 := Real.sqrt_nonneg e
  have hn0 := Real.sqrt_nonneg N
  have hc0 := Real.sqrt_nonneg C
  have h2bound : A - Ne ≤ 2 * √e * N := by
    rcases le_or_gt A B with hAB | hAB
    · have : 0 ≤ 2 * √e * N := by positivity
      linarith
    · have hba : √B ≤ √A := Real.sqrt_le_sqrt hAB.le
      have han : √A ≤ √N := Real.sqrt_le_sqrt hAN
      have hb0 := Real.sqrt_nonneg B
      have e2 : A - B = (√A - √B) * (√A + √B) := by nlinarith
      have s1 : (√A - √B) * (√A + √B) ≤ √C * (√A + √B) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have s2 : √C * (√A + √B) ≤ √C * (2 * √N) := mul_le_mul_of_nonneg_left (by linarith) hc0
      have s3 : √C * (2 * √N) ≤ (√e * √N) * (2 * √N) := mul_le_mul_of_nonneg_right hc (by positivity)
      have e3 : (√e * √N) * (2 * √N) = 2 * √e * N := by
        calc (√e * √N) * (2 * √N) = 2 * √e * √N ^ 2 := by ring
          _ = 2 * √e * N := by rw [hsN]
      linarith
  rw [min_mul_of_nonneg _ _ hN0]
  refine le_min (by linarith) (by linarith)

/-- **`hloc` from per-level far-part bounds**: for `Φ` `C¹` on `[1, X]`, `2 ≤ T`, `1 ≤ k₁ ≤ X` and measurable `ε` with
`specMass (posTail Φ X − posTail Φ k) (kT) ≤ ε(k) N` on `[k₁, X]`,
`logPos Φ X ≤ ∫ ρ log⁺(|t|/T) + (log k₁ + ∫_{k₁}^X min 1 (2√ε(k))/k) N`. -/
theorem hloc_of_levels (Φ ε : ℝ → ℝ) {X T k₁ : ℝ} (hX : 1 ≤ X) (hΦ : ContDiffOn ℝ 1 Φ (Icc 1 X)) (hT : 2 ≤ T)
    (hk₁ : 1 ≤ k₁) (hk₁X : k₁ ≤ X) (hεm : Measurable ε)
    (hε : ∀ k ∈ Icc k₁ X, specMass (posTail Φ X - posTail Φ k) (k * T) ≤ ε k * ∫ θ in Ioi 1, posTail Φ X θ ^ 2) :
    logPos Φ X ≤ (∫ t, specDensity (logScale (posTail Φ X)) t * max 0 (Real.log (|t| / T)))
      + (Real.log k₁ + ∫ k in k₁..X, min 1 (2 * √(ε k)) / k) * ∫ θ in Ioi 1, posTail Φ X θ ^ 2 := by
  set F := posTail Φ X with hFdef
  set N := ∫ θ in Ioi 1, F θ ^ 2 with hNdef
  have hT0 : 0 < T := by linarith
  have hF0 : ∀ θ ≤ 1, F θ = 0 := fun θ hθ => posTail_zero Φ X hθ
  obtain ⟨h2, h1, -, -, hlevy⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX hΦ
  have hρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have hA := Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_arch_mul h2 h1 hlevy
  have hlog := Cvs.WeilForm.Archimedean.GradedArchFloor.integrable_mul_logPlus (specDensity (logScale F)) (specDensity_nonneg _) hρ hA hT
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  set H : ℝ → ℝ := fun k => (N - specMass F (k * T)) / k with hHdef
  have hHi : IntegrableOn H (Ioi 1) := integrableOn_levels hF0 h2 h1 hT0 hlog
  have hHeq := integral_mul_logPlus_eq hF0 h2 h1 hT0
  have hAN : ∀ K, specMass F K ≤ N := fun K => specMass_le hF0 h2 h1 K
  have hH0 : ∀ k, 0 < k → 0 ≤ H k := fun k hk => div_nonneg (by linarith [hAN (k * T)]) hk.le
  have hlev := Cvs.L2a.LogPositionLevelForm.logPos_eq_levels Φ hX hΦ.continuousOn
  rw [← hFdef, ← hNdef] at hlev
  rw [hlev]
  set f : ℝ → ℝ := fun k => (N - ∫ θ in Ioi 1, posTail Φ k θ ^ 2) / k with hfdef
  set w : ℝ → ℝ := fun k => min 1 (2 * √(ε k)) / k with hwdef
  have hk₁0 : 0 < k₁ := by linarith
  -- integrability of the weight `w` on `[k₁, X]`
  have hwi : IntervalIntegrable w volume k₁ X := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hk₁X]
    have hinv : IntegrableOn (fun k : ℝ => k⁻¹) (Ioc k₁ X) :=
      ((continuousOn_inv₀.mono fun x (hx : x ∈ Icc k₁ X) => ne_of_gt (lt_of_lt_of_le hk₁0 hx.1)).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    refine Integrable.mono' hinv
      (((measurable_const.min (measurable_const.mul hεm.sqrt)).div measurable_id).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun k hk => ?_)
    have hk0 : 0 < k := lt_trans hk₁0 hk.1
    have hm0 : 0 ≤ min 1 (2 * √(ε k)) := le_min zero_le_one (by positivity)
    simp only [hwdef]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm0 hk0.le), ← one_div]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hk0.le
  have hw0 : 0 ≤ ∫ k in k₁..X, w k := by
    refine intervalIntegral.integral_nonneg hk₁X fun k hk => ?_
    exact div_nonneg (le_min zero_le_one (by positivity)) (by linarith [hk.1])
  have hlogk : 0 ≤ Real.log k₁ := Real.log_nonneg hk₁
  have hρlog0 : 0 ≤ ∫ t, specDensity (logScale F) t * max 0 (Real.log (|t| / T)) :=
    integral_nonneg fun t => mul_nonneg (specDensity_nonneg _ t) (le_max_left _ _)
  by_cases hfi : IntervalIntegrable f volume 1 X
  swap
  · rw [intervalIntegral.integral_undef hfi]
    have := mul_nonneg (add_nonneg hlogk hw0) hN0
    linarith
  have hHI : ∀ a b, 1 ≤ a → a ≤ b → IntervalIntegrable H volume a b := fun a b ha hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hHi.mono_set fun k hk => lt_of_le_of_lt ha hk.1)
  have hf1 : IntervalIntegrable f volume 1 k₁ :=
    hfi.mono_set (by rw [uIcc_of_le hk₁, uIcc_of_le hX]; exact Icc_subset_Icc le_rfl hk₁X)
  have hf2 : IntervalIntegrable f volume k₁ X :=
    hfi.mono_set (by rw [uIcc_of_le hk₁X, uIcc_of_le hX]; exact Icc_subset_Icc hk₁ le_rfl)
  have hNinv : IntervalIntegrable (fun k : ℝ => N / k) volume 1 k₁ := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id fun x hx => ?_)
    rw [uIcc_of_le hk₁] at hx
    exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)
  have hNlog : ∫ k in (1 : ℝ)..k₁, N / k = N * Real.log k₁ := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hk₁0, div_one]
  -- the levels below `k₁`
  have stepA : ∫ k in (1 : ℝ)..k₁, f k ≤ (∫ k in (1 : ℝ)..k₁, H k) + N * Real.log k₁ := by
    rw [← hNlog, ← intervalIntegral.integral_add (hHI 1 k₁ le_rfl hk₁) hNinv]
    refine intervalIntegral.integral_mono_on hk₁ hf1 ((hHI 1 k₁ le_rfl hk₁).add hNinv) fun k hk => ?_
    have hk0 : 0 < k := lt_of_lt_of_le one_pos hk.1
    have hNe0 : 0 ≤ ∫ θ in Ioi 1, posTail Φ k θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
    simp only [hfdef, hHdef]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith [hAN (k * T)]) hk0.le
  -- the levels from `k₁` to `X`
  have hNw : IntervalIntegrable (fun k => N * w k) volume k₁ X := hwi.const_mul N
  have stepB : ∫ k in k₁..X, f k ≤ (∫ k in k₁..X, H k) + N * ∫ k in k₁..X, w k := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hHI k₁ X hk₁ hk₁X) hNw]
    refine intervalIntegral.integral_mono_on hk₁X hf2 ((hHI k₁ X hk₁ hk₁X).add hNw) fun k hk => ?_
    have hk0 : 0 < k := lt_of_lt_of_le hk₁0 hk.1
    have hleak := level_leak_le Φ hX hΦ (le_trans hk₁ hk.1) hk.2 (hε k hk)
    have e : H k + N * w k = ((N - specMass F (k * T)) + min 1 (2 * √(ε k)) * N) / k := by
      simp only [hHdef, hwdef]; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hk0.le
  -- reassemble
  have hsplit : ∫ k in (1 : ℝ)..X, f k = (∫ k in (1 : ℝ)..k₁, f k) + ∫ k in k₁..X, f k :=
    (intervalIntegral.integral_add_adjacent_intervals hf1 hf2).symm
  have hHsplit : (∫ k in (1 : ℝ)..k₁, H k) + (∫ k in k₁..X, H k) = ∫ k in (1 : ℝ)..X, H k :=
    intervalIntegral.integral_add_adjacent_intervals (hHI 1 k₁ le_rfl hk₁) (hHI k₁ X hk₁ hk₁X)
  have hHle : ∫ k in (1 : ℝ)..X, H k ≤ ∫ k in Ioi 1, H k := by
    rw [intervalIntegral.integral_of_le hX]
    refine setIntegral_mono_set hHi ?_ (LE.le.eventuallySubset Ioc_subset_Ioi_self)
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun k hk => hH0 k (lt_trans one_pos hk))
  rw [hHeq]
  have : (Real.log k₁ + ∫ k in k₁..X, w k) * N = N * Real.log k₁ + N * ∫ k in k₁..X, w k := by ring
  simp only [hwdef] at this ⊢
  linarith

end Cvs.L2a.SpectralMassLevelLeak
