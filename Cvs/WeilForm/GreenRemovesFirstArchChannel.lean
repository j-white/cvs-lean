import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.EvenConnesEnergyFormDomain
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.Upstream.FourierMultiplication
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.SymbolPartialFraction
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.WeilForm.ChannelKernelSineTransform
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PhysicalCubicCorrectionColumn
import Cvs.WeilForm.PoleCancelsPrimeMean
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.PhysicalReciprocalReflection
import Cvs.Zeta.Digamma
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Green term removes the first archimedean channel

The actual Green energy has the first digamma pole as its spectral multiplier.
Its exact cancellation raises the archimedean floor by four and retains the
signed arithmetic discrepancy on the constructed closed Connes form domain.
-/

noncomputable section

open Real Set MeasureTheory Filter Cvs.Zeta.Explicit.Weil
open scoped FourierTransform ComplexConjugate

namespace Cvs.WeilForm.GreenRemovesFirstArchChannel
open Cvs.ZeroCounting

open Cvs.L2a.TailLogScaleTest (logScale)

private theorem integral_exp_of_zero_nonpos (g : ℝ → ℝ)
    (hg : ∀ θ ≤ 0, g θ = 0) :
    (∫ s, exp s * g (exp s)) = ∫ θ, g θ := by
  calc
    _ = ∫ θ in Ioi (0:ℝ), g θ := by
      simpa only [smul_eq_mul] using Cvs.WeilForm.ThetaSpaceParseval.integral_exp_smul_Ioi g
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro θ hθ
      exact hg θ (by simpa only [mem_Ioi, not_lt] using hθ)

private theorem exp_kernel_identity (F : ℝ → ℝ) (s t : ℝ) :
    exp s * (exp t * (F (exp s) * F (exp t) / max (exp s) (exp t))) =
      logScale F s * logScale F t * exp (-|s-t|/2) := by
  rcases le_total s t with h | h
  · rw [max_eq_right (exp_le_exp.mpr h)]
    have he : exp (s/2) * exp (t/2) * exp (-|s-t|/2) = exp s := by
      rw [abs_of_nonpos (sub_nonpos.mpr h), ← exp_add, ← exp_add]
      congr 1
      ring
    calc
      _ = F (exp s) * F (exp t) * exp s := by field_simp
      _ = F (exp s) * F (exp t) *
          (exp (s/2) * exp (t/2) * exp (-|s-t|/2)) := by rw [he]
      _ = _ := by unfold logScale; ring
  · rw [max_eq_left (exp_le_exp.mpr h)]
    have he : exp (s/2) * exp (t/2) * exp (-|s-t|/2) = exp t := by
      rw [abs_of_nonneg (sub_nonneg.mpr h), ← exp_add, ← exp_add]
      congr 1
      ring
    calc
      _ = F (exp s) * F (exp t) * exp t := by field_simp
      _ = F (exp s) * F (exp t) *
          (exp (s/2) * exp (t/2) * exp (-|s-t|/2)) := by rw [he]
      _ = _ := by unfold logScale; ring

/-- The physical Green energy becomes the exact exponential kernel after log scaling. -/
theorem greenEnergy_eq_log_kernel {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume)
    (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy F = ∫ s, ∫ t,
      logScale F s * logScale F t * exp (-|s-t|/2) := by
  have hz : ∀ θ ≤ 0, F θ = 0 := by
    intro θ hθ
    apply hs θ
    intro h
    exact ha.not_ge (h.1.trans hθ)
  unfold Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy
  rw [integral_prod _ (Cvs.WeilForm.PoleCancelsPrimeMean.integrable_greenPair ha hm hF hs)]
  have houter : (∫ θ, ∫ η, Cvs.WeilForm.PoleCancelsPrimeMean.greenPair F (θ,η)) =
      ∫ s, exp s * ∫ η, Cvs.WeilForm.PoleCancelsPrimeMean.greenPair F (exp s,η) := by
    symm
    apply integral_exp_of_zero_nonpos (fun θ => ∫ η, Cvs.WeilForm.PoleCancelsPrimeMean.greenPair F (θ,η))
    intro θ hθ
    simp [Cvs.WeilForm.PoleCancelsPrimeMean.greenPair, hz θ hθ]
  rw [houter]
  apply integral_congr_ae
  filter_upwards [] with s
  have hinner : (∫ η, Cvs.WeilForm.PoleCancelsPrimeMean.greenPair F (exp s,η)) =
      ∫ t, exp t * Cvs.WeilForm.PoleCancelsPrimeMean.greenPair F (exp s,exp t) := by
    symm
    apply integral_exp_of_zero_nonpos (fun η => Cvs.WeilForm.PoleCancelsPrimeMean.greenPair F (exp s,η))
    intro θ hθ
    simp [Cvs.WeilForm.PoleCancelsPrimeMean.greenPair, hz θ hθ]
  rw [hinner, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  exact exp_kernel_identity F s t

private theorem integrable_joint {f : ℝ → ℝ} (hm : Measurable f)
    (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f (p.1+p.2) * exp (-|p.2|/2)) := by
  have hi : Integrable (fun p : ℝ × ℝ => |f p.1| * |f (p.1+p.2)|) := by
    exact (measurePreserving_prod_add volume volume).integrable_comp_of_integrable
      (hf.abs.mul_prod hf.abs)
  refine hi.mono' (((hm.comp measurable_fst).mul
    (hm.comp (measurable_fst.add measurable_snd))).mul
      (by fun_prop : Measurable fun p : ℝ × ℝ => exp (-|p.2|/2))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _)]
  have he : exp (-|p.2|/2) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg p.2])
  exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) he

private theorem log_kernel_eq_weighted_selfConvolution {f : ℝ → ℝ}
    (hm : Measurable f) (hf : Integrable f) :
    (∫ s, ∫ t, f s*f t*exp (-|s-t|/2)) =
      ∫ v, selfConvolution f v * exp (-|v|/2) := by
  have hj := integrable_joint hm hf
  have hs : (∫ s, ∫ t, f s*f t*exp (-|s-t|/2)) =
      ∫ s, ∫ v, f s*f (s+v)*exp (-|v|/2) := by
    apply integral_congr_ae
    filter_upwards [] with s
    rw [← integral_add_left_eq_self (fun t => f s*f t*exp (-|s-t|/2)) s]
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [show s-(s+v) = -v by ring, abs_neg]
  rw [hs, integral_integral_swap hj]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [integral_mul_const]
  rfl

/-- The first-pole multiplier, in angular-frequency normalization. -/
def greenMultiplier (t : ℝ) : ℝ := 1/(t^2+1/4)

private theorem weighted_selfConvolution_eq_spectral {f : ℝ → ℝ} (hf : Integrable f) :
    (∫ v, selfConvolution f v * exp (-|v|/2)) =
      ∫ t, greenMultiplier t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  let p : ℝ → ℝ := fun w => 1/(1/4+(2*π*w)^2)
  have hp_eq : p = fun w => 2*(1/2:ℝ)/((1/2:ℝ)^2+(2*π*w)^2) := by
    funext w
    norm_num [p]
  have hp : Integrable p := by
    rw [hp_eq]
    exact Cvs.WeilForm.ChannelKernelSineTransform.integrable_poisson (show (0:ℝ)<1/2 by norm_num)
  have hfp : ∀ v, 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf p) v = (exp (-|v|/2) : ℂ) := by
    intro v
    have h := congrFun (Cvs.WeilForm.ChannelKernelSineTransform.fourierInv_poisson (show (0:ℝ)<1/2 by norm_num)) (-v)
    rw [fourierInv_eq_fourier_neg] at h
    simp only [neg_neg] at h
    change 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (fun w => 2*(1/2:ℝ)/((1/2:ℝ)^2+(2*π*w)^2))) v = _ at h
    rw [← hp_eq] at h
    simpa only [abs_neg, show -(1/2:ℝ)*|v| = -|v|/2 by ring] using h
  have h := Cvs.Upstream.FourierMultiplication.integral_fourier_mul
    (Cvs.WeilForm.SelfConvolutionTransform.cf (selfConvolution f)) (Cvs.WeilForm.SelfConvolutionTransform.cf p)
    (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hf) hp.ofReal
  change (∫ w, 𝓕 (fun v => (selfConvolution f v : ℂ)) w * Cvs.WeilForm.SelfConvolutionTransform.cf p w) = _ at h
  simp_rw [Cvs.WeilForm.SelfConvolutionTransform.fourier_selfConvolution f hf, hfp] at h
  have hreal : (∫ w, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖^2 * p w) =
      ∫ v, selfConvolution f v * exp (-|v|/2) := by
    have hl : (fun w => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖^2 : ℝ) : ℂ) * Cvs.WeilForm.SelfConvolutionTransform.cf p w) =
        fun w => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖^2 * p w : ℝ) : ℂ) := by
      funext w
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.ofReal_mul]
    have hr : (fun v => Cvs.WeilForm.SelfConvolutionTransform.cf (selfConvolution f) v * (exp (-|v|/2) : ℂ)) =
        fun v => ((selfConvolution f v * exp (-|v|/2) : ℝ) : ℂ) := by
      funext v
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.ofReal_mul]
    rw [hl, hr, integral_complex_ofReal, integral_complex_ofReal] at h
    exact Complex.ofReal_inj.mp h
  rw [← hreal]
  have hc := Measure.integral_comp_mul_left
    (fun t => greenMultiplier t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) (2*π)
  have he : (fun w => greenMultiplier (2*π*w) * Cvs.WeilForm.SelfConvolutionCosine.specDensity f (2*π*w)) =
      fun w => (‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w‖^2 * p w)/(2*π) := by
    funext w
    unfold greenMultiplier Cvs.WeilForm.SelfConvolutionCosine.specDensity p
    rw [show (2*π*w)/(2*π) = w by field_simp]
    ring
  rw [he, integral_div, abs_of_pos (by positivity : (0:ℝ)<(2*π)⁻¹), smul_eq_mul] at hc
  exact (mul_left_cancel₀ (inv_ne_zero (by positivity : (2*π:ℝ)≠0))
    (by simpa only [div_eq_inv_mul] using hc))

/-- The actual Green kernel has the first-pole spectral multiplier without a continuity premise. -/
theorem greenEnergy_eq_spectral {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume)
    (hs : ∀ θ ∉ Icc a 1, F θ=0) (hf : Integrable (logScale F)) :
    Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy F = ∫ t, greenMultiplier t * Cvs.L2a.FullTailPolarisation.crossSpec
      (logScale F) (logScale F) t := by
  have hmf : Measurable (logScale F) :=
    (hm.comp Real.measurable_exp).mul (by fun_prop)
  rw [greenEnergy_eq_log_kernel ha hm hF hs,
    log_kernel_eq_weighted_selfConvolution hmf hf,
    weighted_selfConvolution_eq_spectral hf]
  simp only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self]

theorem greenMultiplier_nonneg (t : ℝ) : 0 ≤ greenMultiplier t := by
  unfold greenMultiplier
  positivity

theorem greenMultiplier_le_four (t : ℝ) : greenMultiplier t ≤ 4 := by
  unfold greenMultiplier
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg t]

/-- The first-pole spectral energy is genuinely integrable on `L¹ ∩ L²`. -/
theorem integrable_green_spectral {f : ℝ → ℝ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) :
    Integrable (fun t => greenMultiplier t * Cvs.L2a.FullTailPolarisation.crossSpec f f t) := by
  have hi := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1
  have hc : Continuous greenMultiplier := by
    have hd : Continuous (fun t : ℝ => t^2+1/4) := by fun_prop
    have hne : ∀ t : ℝ, t^2+1/4 ≠ 0 := fun t => by positivity
    exact continuous_const.div₀ hd hne
  simp only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self]
  refine (hi.const_mul 4).mono' (hc.mul (Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hf1)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (greenMultiplier_nonneg t) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t))]
  exact mul_le_mul_of_nonneg_right (greenMultiplier_le_four t) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)

/-- The arch symbol with the cancelled first-pole channel. -/
def shiftedArchSymbol (t : ℝ) : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t + greenMultiplier t

/-- The shift is exactly the digamma recurrence from `1/4` to `5/4`. -/
theorem shiftedArchSymbol_eq_digamma (t : ℝ) :
    shiftedArchSymbol t =
      (Complex.digamma (((5/4:ℝ):ℂ) + Complex.I * ((t/2:ℝ):ℂ))).re - log π := by
  have h := Cvs.WeilForm.Archimedean.SymbolPartialFraction.re_digamma_shift t 1
  norm_num [Finset.sum_range_one, Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx] at h
  have ha : Cvs.Zeta.digammaArg t 1 =
      ((5/4:ℝ):ℂ) + Complex.I * ((t/2:ℝ):ℂ) := by
    norm_num [Cvs.Zeta.digammaArg]
  rw [ha] at h
  unfold shiftedArchSymbol Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol greenMultiplier
  simp only [one_div]
  linarith

/-- Removing the first pole raises the exact global spectral minimum by four. -/
theorem shiftedArchSymbol_ge (t : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4 ≤ shiftedArchSymbol t := by
  have ht := Cvs.WeilForm.Archimedean.TruncationBelowSymbol.remainder_nonneg t 1
  have he (u : ℝ) : shiftedArchSymbol u =
      (Complex.digamma (Cvs.Zeta.digammaArg u 1)).re - log π := by
    rw [shiftedArchSymbol_eq_digamma]
    norm_num [Cvs.Zeta.digammaArg]
  have hzero : shiftedArchSymbol 0 = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4 := by
    norm_num [shiftedArchSymbol, greenMultiplier]
  rw [← hzero, he 0, he t]
  linarith

/-- The constructed even Connes Green energy has the exact spectral representation. -/
theorem greenEnergy_connesAngularEven_eq_spectral {x : ℕ} (hx : 80 ≤ 2*π*x) :
    Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) =
      ∫ t, greenMultiplier t * Cvs.L2a.FullTailPolarisation.crossSpec
        (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t :=
  greenEnergy_eq_spectral (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
    (Cvs.WeilForm.PoleCancelsPrimeMean.measurable_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
    (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
    (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x) (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx).1

/-- The actual shifted arch channel is genuinely integrable on the constructed form domain. -/
theorem integrable_shifted_arch_connesAngularEven {x : ℕ} (hx : 80 ≤ 2*π*x) :
    Integrable (fun t => shiftedArchSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
      (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) := by
  obtain ⟨hf1,hf2,_⟩ := Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx
  have h := (Cvs.Approximant.EvenConnesEnergyFormDomain.integrable_arch_connesAngularEven hx).add
    (integrable_green_spectral hf1 hf2)
  apply h.congr
  exact ae_of_all _ fun t => by simp only [shiftedArchSymbol, add_mul, Pi.add_apply]

/-- The actual closed Connes form has the shifted arch decomposition with the signed discrepancy retained. -/
theorem Q_even_connesClass_eq_shifted_arch_sub_discrepancy {x : ℕ}
    (hx : 80 ≤ 2*π*x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)) =
      (∫ t, shiftedArchSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
        (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) -
      Cvs.WeilForm.PoleCancelsPrimeMean.primeDiscrepancy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  obtain ⟨hf1,hf2,_⟩ := Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx
  rw [Cvs.WeilForm.PoleCancelsPrimeMean.Q_even_connesClass_eq_arch_green_sub_discrepancy hx,
    greenEnergy_connesAngularEven_eq_spectral hx,
    ← integral_add (Cvs.Approximant.EvenConnesEnergyFormDomain.integrable_arch_connesAngularEven hx)
      (integrable_green_spectral hf1 hf2)]
  simp only [shiftedArchSymbol, add_mul]

private theorem integral_crossSpec_connes_eq_physical {x : ℕ} (hx : 80 ≤ 2*π*x) :
    (∫ t, Cvs.L2a.FullTailPolarisation.crossSpec (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x))
      (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) =
      ∫ θ, Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ ^ 2 := by
  obtain ⟨hf1,hf2,_⟩ := Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx
  rw [Cvs.WeilForm.ThetaSpaceParseval.integral_crossSpec hf1 hf2 hf1 hf2]
  simp only [← sq]
  apply Cvs.WeilForm.PhysicalCubicCorrectionColumn.integral_logScale_sq
  intro θ hθ
  apply Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x θ
  intro h
  exact (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)).not_ge (h.1.trans hθ)

/-- The exact actual spectral floor improves by four, while retaining all arithmetic discrepancy. -/
theorem Q_even_connesClass_ge_shifted_floor {x : ℕ} (hx : 80 ≤ 2*π*x) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4) * (∫ θ, Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ ^ 2) -
      Cvs.WeilForm.PoleCancelsPrimeMean.primeDiscrepancy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) ≤
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)) := by
  obtain ⟨hf1,hf2,_⟩ := Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx
  have hi : Integrable (fun t => (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4) * Cvs.L2a.FullTailPolarisation.crossSpec
      (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) := by
    simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using
      (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1).const_mul (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4)
  have h := integral_mono hi (integrable_shifted_arch_connesAngularEven hx) fun t =>
    mul_le_mul_of_nonneg_right (shiftedArchSymbol_ge t)
      (by simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using
        Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t)
  rw [integral_const_mul, integral_crossSpec_connes_eq_physical hx] at h
  rw [Q_even_connesClass_eq_shifted_arch_sub_discrepancy hx]
  linarith

/-- The actual positive Green correction is bounded by four times the physical energy. -/
theorem greenEnergy_connesAngularEven_bounds {x : ℕ} (hx : 80 ≤ 2*π*x) :
    0 ≤ Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) ∧
      Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) ≤
        4 * ∫ θ, Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ ^ 2 := by
  constructor
  · exact Cvs.WeilForm.PoleCancelsPrimeMean.greenEnergy_nonneg (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
      (Cvs.WeilForm.PoleCancelsPrimeMean.measurable_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
      (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
      (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x)
  · obtain ⟨hf1,hf2,_⟩ := Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx
    rw [greenEnergy_connesAngularEven_eq_spectral hx,
      ← integral_crossSpec_connes_eq_physical hx, ← integral_const_mul]
    apply integral_mono (integrable_green_spectral hf1 hf2)
      (by simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using
        (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1).const_mul 4)
    intro t
    exact mul_le_mul_of_nonneg_right (greenMultiplier_le_four t)
      (by simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using
        Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t)

end Cvs.WeilForm.GreenRemovesFirstArchChannel
