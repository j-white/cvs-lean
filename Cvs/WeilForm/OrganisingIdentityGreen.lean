import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.FullTailPolarisation
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.FourierMultiplication
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.ChannelKernelSineTransform
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.PolePrimeCosineMultipliers
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Organising Identity `Q = E + A - F` and Shifted-Arch Multiplier Representation

Splits the pole term into the positive-definite Green kernel `E` (`e^{-|v|/2}`) and continuous
prime mean `M` (`e^{|v|/2}`), yielding `Q = E + A - F` and the `shiftedArchSymbol` representation.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.Zeta.Explicit.Weil
open scoped FourierTransform InnerProductSpace

namespace Cvs.WeilForm.OrganisingIdentityGreen
open Cvs.ZeroCounting

/-! ### 1. Lag-Kernel Split of the Pole Term (`poleTerm = windowGreenEnergy + windowMeanTerm`) -/

/-- Positive-definite lag-weighted Green energy `E(f) = ∫ (f ⋆ f̃)(v) e^{-|v|/2} dv`. -/
def windowGreenEnergy (f : ℝ → ℝ) : ℝ :=
  ∫ v, selfConvolution f v * Real.exp (-|v| / 2)

/-- Continuous prime mean `M(f) = ∫ (f ⋆ f̃)(v) e^{|v|/2} dv` in lag coordinates. -/
def windowMeanTerm (f : ℝ → ℝ) : ℝ :=
  ∫ v, selfConvolution f v * Real.exp (|v| / 2)

/-- Mean-free prime block `F(f) = primeTerm P R f − windowMeanTerm f`. -/
def meanFreePrimeTerm (P R : ℕ) (f : ℝ → ℝ) : ℝ :=
  Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R f - windowMeanTerm f

/-- Pointwise hyperbolic split `2 cosh(v / 2) = e^{-|v|/2} + e^{|v|/2}`. -/
theorem two_mul_cosh_half_eq_exp_abs (v : ℝ) :
    2 * Real.cosh (v / 2) = Real.exp (-|v| / 2) + Real.exp (|v| / 2) := by
  have h1 : Real.cosh (v / 2) = Real.cosh (|v| / 2) := by
    rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_div, Real.cosh_neg]
  rw [h1, Real.cosh_eq, neg_div]
  ring

/-- The rank-two pole term is `∫ 2 cosh(v / 2) (f ⋆ f̃)(v) dv` for integrable `f` supported in `[a, b]`. -/
theorem poleTerm_eq_integral_cosh_selfConvolution {a b : ℝ} {f : ℝ → ℝ}
    (hf : Integrable f) (hfs : ∀ x ∉ Set.Icc a b, f x = 0) :
    Cvs.WeilForm.PoleArchPrimeProblem.poleTerm f = ∫ v, 2 * Real.cosh (v / 2) * selfConvolution f v := by
  have hp : Cvs.WeilForm.PoleArchPrimeProblem.poleTerm f = Cvs.WeilForm.TruncatedFormPolarised.poleF f * Cvs.WeilForm.TruncatedFormPolarised.poleG f + Cvs.WeilForm.TruncatedFormPolarised.poleF f * Cvs.WeilForm.TruncatedFormPolarised.poleG f := by
    unfold Cvs.WeilForm.PoleArchPrimeProblem.poleTerm Cvs.WeilForm.PoleArchPrimeProblem.Mplus Cvs.WeilForm.PoleArchPrimeProblem.Mminus Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG
    ring
  rw [hp, Cvs.WeilForm.PolePrimeCosineMultipliers.pole_eq_integral_cosh_mul_crossConv hf hf hfs hfs]
  rfl

/-- `v ↦ selfConvolution f v * exp (-|v| / 2)` is integrable for any integrable `f`. -/
theorem integrable_selfConvolution_mul_exp_neg_abs {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable fun v => selfConvolution f v * Real.exp (-|v| / 2) := by
  have hsc : Integrable (selfConvolution f) := (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hf).re
  have hc : Continuous fun v : ℝ => Real.exp (-|v| / 2) := by fun_prop
  refine hsc.norm.mono' (hsc.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-|v| / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg v])
  exact mul_le_of_le_one_right (abs_nonneg (selfConvolution f v)) he

/-- `v ↦ selfConvolution f v * exp (|v| / 2)` is integrable for integrable `f` supported in `[a, b]`. -/
theorem integrable_selfConvolution_mul_exp_abs {a b : ℝ} {f : ℝ → ℝ}
    (hf : Integrable f) (hfs : ∀ x ∉ Set.Icc a b, f x = 0) :
    Integrable fun v => selfConvolution f v * Real.exp (|v| / 2) := by
  have hcosh := (Cvs.WeilForm.PolePrimeCosineMultipliers.integrable_cosh_mul_crossConv hf hf hfs hfs).const_mul 2
  have hneg := integrable_selfConvolution_mul_exp_neg_abs hf
  refine (hcosh.sub hneg).congr (Eventually.of_forall fun v => ?_)
  dsimp only
  change 2 * (Real.cosh (v / 2) * selfConvolution f v)
      - selfConvolution f v * Real.exp (-|v| / 2)
    = selfConvolution f v * Real.exp (|v| / 2)
  have h2 := two_mul_cosh_half_eq_exp_abs v
  linear_combination selfConvolution f v * h2

/-- **Pole Term Split**: `poleTerm f = windowGreenEnergy f + windowMeanTerm f` for any integrable
`f` supported in `[a, b]`. -/
theorem poleTerm_eq_windowGreenEnergy_add_windowMeanTerm {a b : ℝ} {f : ℝ → ℝ}
    (hf : Integrable f) (hfs : ∀ x ∉ Set.Icc a b, f x = 0) :
    Cvs.WeilForm.PoleArchPrimeProblem.poleTerm f = windowGreenEnergy f + windowMeanTerm f := by
  rw [poleTerm_eq_integral_cosh_selfConvolution hf hfs, windowGreenEnergy, windowMeanTerm,
    ← integral_add (integrable_selfConvolution_mul_exp_neg_abs hf)
      (integrable_selfConvolution_mul_exp_abs hf hfs)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [two_mul_cosh_half_eq_exp_abs]
  ring

/-! ### 2. Spectral Identity and Positivity of `windowGreenEnergy` -/

/-- **Spectral Representation of `windowGreenEnergy`**:
`windowGreenEnergy f = ∫ t, greenMultiplier t * specDensity f t` for any `f ∈ L¹(ℝ)`. -/
theorem windowGreenEnergy_eq_spectral {f : ℝ → ℝ} (hf : Integrable f) :
    windowGreenEnergy f = ∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  unfold windowGreenEnergy
  let p : ℝ → ℝ := fun w => 1 / (1 / 4 + (2 * π * w) ^ 2)
  have hp_eq : p = fun w => 2 * (1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + (2 * π * w) ^ 2) := by
    funext w
    norm_num [p]
  have hp : Integrable p := by
    rw [hp_eq]
    exact Cvs.WeilForm.ChannelKernelSineTransform.integrable_poisson (show (0 : ℝ) < 1 / 2 by norm_num)
  have hfp : ∀ v, 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf p) v = (Real.exp (-|v| / 2) : ℂ) := by
    intro v
    have h := congrFun (Cvs.WeilForm.ChannelKernelSineTransform.fourierInv_poisson (show (0 : ℝ) < 1 / 2 by norm_num)) (-v)
    rw [fourierInv_eq_fourier_neg] at h
    simp only [neg_neg] at h
    change 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (fun w => 2 * (1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + (2 * π * w) ^ 2))) v = _ at h
    rw [← hp_eq] at h
    simpa only [abs_neg, show -(1 / 2 : ℝ) * |v| = -|v| / 2 by ring] using h
  have h := Cvs.Upstream.FourierMultiplication.integral_fourier_mul
    (Cvs.WeilForm.SelfConvolutionTransform.cf (selfConvolution f)) (Cvs.WeilForm.SelfConvolutionTransform.cf p)
    (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hf) hp.ofReal
  change (∫ w, 𝓕 (fun v => (selfConvolution f v : ℂ)) w * Cvs.WeilForm.SelfConvolutionTransform.cf p w) = _ at h
  simp_rw [Cvs.WeilForm.SelfConvolutionTransform.fourier_selfConvolution f hf, hfp] at h
  have hreal : (∫ w, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖ ^ 2 * p w) =
      ∫ v, selfConvolution f v * Real.exp (-|v| / 2) := by
    have hl : (fun w => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖ ^ 2 : ℝ) : ℂ) * Cvs.WeilForm.SelfConvolutionTransform.cf p w) =
        fun w => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖ ^ 2 * p w : ℝ) : ℂ) := by
      funext w
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.ofReal_mul]
    have hr : (fun v => Cvs.WeilForm.SelfConvolutionTransform.cf (selfConvolution f) v * (Real.exp (-|v| / 2) : ℂ)) =
        fun v => ((selfConvolution f v * Real.exp (-|v| / 2) : ℝ) : ℂ) := by
      funext v
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.ofReal_mul]
    rw [hl, hr, integral_complex_ofReal, integral_complex_ofReal] at h
    exact Complex.ofReal_inj.mp h
  rw [← hreal]
  have hc := Measure.integral_comp_mul_left
    (fun t => Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (2 * π)
  have he : (fun w => Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier (2 * π * w) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f (2 * π * w)) =
      fun w => (‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖ ^ 2 * p w) / (2 * π) := by
    funext w
    unfold Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier Cvs.WeilForm.SelfConvolutionCosine.specDensity p
    rw [show (2 * π * w) / (2 * π) = w by field_simp]
    ring
  rw [he, integral_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), smul_eq_mul] at hc
  exact (mul_left_cancel₀ (inv_ne_zero (by positivity : (2 * π : ℝ) ≠ 0))
    (by simpa only [div_eq_inv_mul] using hc))

/-- `windowGreenEnergy f` is nonnegative for any `f ∈ L¹(ℝ)`. -/
theorem windowGreenEnergy_nonneg {f : ℝ → ℝ} (hf : Integrable f) :
    0 ≤ windowGreenEnergy f := by
  rw [windowGreenEnergy_eq_spectral hf]
  exact integral_nonneg fun t =>
    mul_nonneg (Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier_nonneg t) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)

/-- `windowGreenEnergy f ≤ 4 ∫ specDensity f` for `f ∈ L¹(ℝ) ∩ L²(ℝ)`. -/
theorem windowGreenEnergy_le_four_mul_integral_specDensity {f : ℝ → ℝ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    windowGreenEnergy f ≤ 4 * ∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  rw [windowGreenEnergy_eq_spectral hf1, ← integral_const_mul]
  have hi1 : Integrable fun t => Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
    simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using Cvs.WeilForm.GreenRemovesFirstArchChannel.integrable_green_spectral hf1 hf2
  have hi2 : Integrable fun t => 4 * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t :=
    (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1).const_mul 4
  exact integral_mono hi1 hi2 fun t =>
    mul_le_mul_of_nonneg_right (Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier_le_four t) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)

/-! ### 3. Organising Identity `Q = E + A - F` and Shifted-Arch Representation on `formDomain hL` -/

/-- General window decomposition `Q = poleTerm + archTerm - primeTerm` on `formDomain hL`. -/
theorem Q_eq_pole_add_arch_sub_prime {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        - Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) = _
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).1, Cvs.WeilForm.PoleArchPrimeProblem.weilForm_split]

/-- Pole split on a form-domain representative: `poleTerm (rep φ) = E(rep φ) + M(rep φ)`. -/
theorem poleTerm_rep_eq_windowGreenEnergy_add_windowMeanTerm {L : ℝ} {hL : 0 ≤ L}
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      = windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        + windowMeanTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) :=
  poleTerm_eq_windowGreenEnergy_add_windowMeanTerm
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL φ)

/-- Spectral representation of `windowGreenEnergy` on `formDomain hL`. -/
theorem windowGreenEnergy_rep_eq_spectral {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      = ∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.EvenBulkVisibility.rho φ t :=
  windowGreenEnergy_eq_spectral (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))

/-- `windowGreenEnergy` is nonnegative on `formDomain hL`. -/
theorem windowGreenEnergy_rep_nonneg {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    0 ≤ windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) :=
  windowGreenEnergy_nonneg (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))

/-- `windowGreenEnergy (rep φ) ≤ 4 ‖φ‖²` on `formDomain hL`. -/
theorem windowGreenEnergy_rep_le_four_mul_norm_sq {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) ≤ 4 * ‖φ‖ ^ 2 := by
  have h := windowGreenEnergy_le_four_mul_integral_specDensity
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
  rwa [Cvs.WeilForm.AdmissibleMultiplierMinorants.integral_specDensity_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)] at h

/-- Integrability of `greenMultiplier * rho φ` on `formDomain hL`. -/
theorem integrable_greenMultiplier_mul_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using Cvs.WeilForm.GreenRemovesFirstArchChannel.integrable_green_spectral
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))

/-- Integrability of `archSymbol * rho φ` on `formDomain hL`. -/
theorem integrable_archSymbol_mul_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hf : MemLp f 2 volume := Cvs.WeilForm.WindowRepresentative.memLp_rep _
  have hf1 : Integrable f := Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _
  have hsd : Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hf1
  have hspec : Integrable fun t =>
      Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) :=
    Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hf hf1 (Cvs.WeilForm.FormDomain.hdom_of_mem φ)
  exact (hspec.add (hsd.const_mul (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))).congr
    (Eventually.of_forall fun t => by simp only [Pi.add_apply, Cvs.WeilForm.EvenBulkVisibility.rho, f]; ring)

/-- Spectral representation of `archTerm` on `formDomain hL`:
`archTerm (rep φ) = ∫ t, archSymbol t * rho φ t`. -/
theorem archTerm_rep_eq_spectral {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) = ∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hf : MemLp f 2 volume := Cvs.WeilForm.WindowRepresentative.memLp_rep _
  have hf1 : Integrable f := Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _
  have hsq : Integrable fun s => f s ^ 2 := Cvs.WeilForm.WindowRepresentative.integrable_sq_rep _
  have hcross : ∀ u, Integrable fun s => f s * f (s + u) := Cvs.WeilForm.WindowRepresentative.integrable_cross_rep _
  have hdom : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  have hsd : Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hf1
  have hspec : Integrable fun t =>
      Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) :=
    Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hf hf1 hdom
  have hmass : (∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) = selfConvolution f 0 :=
    Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity_eq_selfConvolution hf1 hf
  have hlevy := Cvs.WeilForm.Archimedean.ArchEnergySpectral.integral_levy_eq hf hf1 hsq hcross hdom hspec
  have hsplit : (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = (∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
        + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
    rw [← integral_const_mul, ← integral_add hspec (hsd.const_mul _)]
    exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only [Cvs.WeilForm.EvenBulkVisibility.rho]; ring)
  rw [hsplit, hmass, ← hlevy]
  unfold Cvs.WeilForm.PoleArchPrimeProblem.archTerm Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  ring

/-- **Organising Identity `Q = E + A - F`** on `formDomain hL`:
`Q hL P R φ = windowGreenEnergy (rep φ) + archTerm (rep φ) - meanFreePrimeTerm P R (rep φ)`. -/
theorem Q_eq_green_add_arch_sub_meanFreePrime {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ
      = windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        - meanFreePrimeTerm P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  rw [Q_eq_pole_add_arch_sub_prime hL P R φ,
    poleTerm_rep_eq_windowGreenEnergy_add_windowMeanTerm φ, meanFreePrimeTerm]
  ring

/-- Dropping the nonnegative Green energy `E ≥ 0` gives `archTerm − meanFreePrimeTerm ≤ Q`. -/
theorem Q_ge_arch_sub_meanFreePrime {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        - meanFreePrimeTerm P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ := by
  rw [Q_eq_green_add_arch_sub_meanFreePrime hL P R φ]
  linarith [windowGreenEnergy_rep_nonneg φ]

/-- **Shifted-Arch Multiplier Representation of `Q`** on `formDomain hL`:
`Q hL P R φ = (∫ t, shiftedArchSymbol t * rho φ t) - meanFreePrimeTerm P R (rep φ)`. -/
theorem Q_eq_shiftedArch_sub_meanFreePrime {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ
      = (∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
        - meanFreePrimeTerm P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  rw [Q_eq_green_add_arch_sub_meanFreePrime hL P R φ,
    windowGreenEnergy_rep_eq_spectral φ, archTerm_rep_eq_spectral φ,
    ← integral_add (integrable_greenMultiplier_mul_rho φ) (integrable_archSymbol_mul_rho φ)]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by
    dsimp only [Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol]; ring)

/-! ### 4. Scale-`x` and Even-Bulk Specializations -/

/-- Organising identity `Q_x = E_x + A_x - F_x` on `Dom x`. -/
theorem Qx_eq_green_add_arch_sub_meanFreePrime (x : ℕ) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x w
      = windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) :=
  Q_eq_green_add_arch_sub_meanFreePrime (Real.log_natCast_nonneg x) x (Nat.clog 2 x) w

/-- **Even Bulk Floor from Mean-Free Prime Control Against `archTerm`**: if on `Ev x ∩ R₁ᗮ`
the mean-free prime term `F_x(w)` is at most `archTerm (rep w) − b ‖w‖²`, then `EvenBulkFloor x b`
holds (with `windowGreenEnergy (rep w) ≥ 0` retained as slack). -/
theorem evenBulkFloor_of_meanFreePrime_le_arch {x : ℕ} {b : ℝ}
    (hF : ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) - b * ‖w‖ ^ 2) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b := by
  intro w hwE hwR
  have h1 := Q_ge_arch_sub_meanFreePrime (Real.log_natCast_nonneg x) x (Nat.clog 2 x) w
  change Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      - meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
    ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w at h1
  linarith [hF w hwE hwR]

end Cvs.WeilForm.OrganisingIdentityGreen
