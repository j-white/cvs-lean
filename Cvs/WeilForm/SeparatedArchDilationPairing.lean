import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.SymmetricModeSet
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.RungWindowCouplingTail
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PoleTermDilationMean
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaPairingBilinear
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImagePoleFunctionals
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The separated arch channel is a continuous dilation pairing

When a tail is supported above `1` and a window test below `1`, only one
orientation of the polarised arch convolution survives. Its exact continuous
dilation weight is `r / (r² - 1)`. The coupling formula retains both pole
channels and the actual infinite Mangoldt sum.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.WeilForm.SeparatedArchDilationPairing
open Cvs.ZeroCounting

open Cvs.WeilForm.TruncatedFormPolarised (crossConv polar)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.L2a.FullTailPolarisation (archFullBil crossSpec)
open Cvs.WeilForm.ThetaSpaceParseval (poleP poleM dil weilθ)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.PoleTermDilationMean (dilR)

/-- A positive shift cannot pair a right-supported first function with a
left-supported second function. -/
theorem crossConv_eq_zero_of_separated {f g : ℝ → ℝ}
    (hf : ∀ s ≤ 0, f s = 0) (hg : ∀ s, 0 < s → g s = 0)
    {v : ℝ} (hv : 0 ≤ v) : crossConv f g v = 0 := by
  unfold crossConv
  apply integral_eq_zero_of_ae
  filter_upwards [] with s
  by_cases hs : s ≤ 0
  · simp only [hf s hs, zero_mul, Pi.zero_apply]
  · simp only [hg (s + v) (by linarith), mul_zero, Pi.zero_apply]

/-- The separated polarisation has only the left-to-right orientation. -/
theorem archFullBil_eq_one_sided {f g : ℝ → ℝ}
    (hf : ∀ s ≤ 0, f s = 0) (hg : ∀ s, 0 < s → g s = 0) :
    archFullBil f g =
      -(∫ u in Ioi (0 : ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u * crossConv g f (u / 2) / 2) := by
  unfold archFullBil
  have hp0 : polar f g 0 = 0 := by
    rw [polar, crossConv_eq_zero_of_separated hf hg (le_refl 0)]
    have he : crossConv g f 0 = crossConv f g 0 := by
      unfold crossConv
      apply integral_congr_ae
      filter_upwards [] with s
      simp only [add_zero, mul_comm]
    rw [he, crossConv_eq_zero_of_separated hf hg (le_refl 0)]
    ring
  rw [hp0, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0 < u at hu
  change Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (0 - polar f g (u / 2)) / 2 = _
  simp only [polar, crossConv_eq_zero_of_separated hf hg (by linarith : 0 ≤ u / 2)]
  ring

/-- After doubling the shift, the Jacobian cancels the `1/2` in the
polarised arch convention. -/
theorem archFullBil_eq_shift {f g : ℝ → ℝ}
    (hf : ∀ s ≤ 0, f s = 0) (hg : ∀ s, 0 < s → g s = 0) :
    archFullBil f g =
      -(∫ v in Ioi (0 : ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) * crossConv g f v) := by
  rw [archFullBil_eq_one_sided hf hg]
  congr 1
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * crossConv g f (u / 2) / 2) 0
    (show (0 : ℝ) < 2 by norm_num)
  simp only [mul_zero, smul_eq_mul] at h
  have he : (∫ v in Ioi (0 : ℝ),
      Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) * crossConv g f v) =
      2 * (∫ v in Ioi (0 : ℝ),
        Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) * crossConv g f ((2 * v) / 2) / 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    dsimp only
    rw [show (2 * v) / 2 = v by ring]
    ring
  rw [he, h]
  ring

/-- The two support hypotheses in theta coordinates imply separated log
supports. -/
theorem logScale_separated {F G : ℝ → ℝ}
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : ∀ θ, 1 < θ → G θ = 0) :
    (∀ s ≤ 0, logScale F s = 0) ∧ (∀ s, 0 < s → logScale G s = 0) := by
  constructor
  · intro s hs
    simp only [logScale, hF _ (Real.exp_le_one_iff.mpr hs), zero_mul]
  · intro s hs
    simp only [logScale, hG _ (Real.one_lt_exp_iff.mpr hs), zero_mul]

/-- The weight in the positive log-shift integral after `r = exp v`. -/
theorem densityU_mul_sqrt_exp (v : ℝ) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) * √(Real.exp v) =
      Real.exp v * (Real.exp v / ((Real.exp v) ^ 2 - 1)) := by
  rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU, show -(2 * v / 4) = -v / 2 by ring,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp]
  rw [show v * (1 / 2) = v / 2 by ring]
  have hden : 1 - Real.exp (-(2 * v)) =
      ((Real.exp v) ^ 2 - 1) / (Real.exp v) ^ 2 := by
    rw [Real.exp_neg, show 2 * v = v + v by ring, Real.exp_add]
    field_simp
  rw [hden, div_mul_eq_mul_div, ← Real.exp_add,
    show -v / 2 + v / 2 = 0 by ring, Real.exp_zero]
  field_simp

/-- The one-sided shift integral is genuinely integrable on the arch
domains of its two slots. -/
theorem integrable_arch_shift {f g : ℝ → ℝ}
    (hf : ∀ s ≤ 0, f s = 0) (hg : ∀ s, 0 < s → g s = 0)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    IntegrableOn (fun v => Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) * crossConv g f v)
      (Ioi (0 : ℝ)) := by
  have hS := Cvs.L2a.FullTailPolarisation.integrableOn_levy_add_smul hf2 hg2 hfl hgl 1
  have hP : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u *
      (polar f g 0 - polar f g (u / 2)) / 2) (Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun (((hS.sub hfl).sub hgl).div_const 2) (fun u _ => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply, Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_add_smul hf2 hg2 1]
    ring
  have h0 : crossConv g f 0 = 0 := by
    have he := Cvs.WeilForm.TruncatedFormPolarised.crossConv_neg f g 0
    simpa only [neg_zero, crossConv_eq_zero_of_separated hf hg (le_refl 0)] using he
  have hU : IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u *
      crossConv g f (u / 2) / 2) (Ioi (0 : ℝ)) := by
    refine hP.neg.congr_fun (fun u hu => ?_) measurableSet_Ioi
    change 0 < u at hu
    simp only [Pi.neg_apply, polar, h0,
      crossConv_eq_zero_of_separated hf hg (le_refl 0),
      crossConv_eq_zero_of_separated hf hg (by linarith : 0 ≤ u / 2)]
    ring
  have hV := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * crossConv g f (u / 2) / 2)
    0 (show (0 : ℝ) < 2 by norm_num)).mpr (by simpa only [mul_zero] using hU)
  refine IntegrableOn.congr_fun (hV.const_mul 2) (fun v _ => ?_) measurableSet_Ioi
  simp only [show (2 * v) / 2 = v by ring]
  ring

/-- Integrability also passes through the exact real-dilation bridge. -/
theorem integrable_arch_dilation {F G : ℝ → ℝ}
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : ∀ θ, 1 < θ → G θ = 0)
    (hf2 : MemLp (logScale F) 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume)
    (hg2 : MemLp (logScale G) 2 volume)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale G)) (Ioi 0) volume) :
    IntegrableOn (fun r => r / (r ^ 2 - 1) * dilR G F r) (Ioi (1 : ℝ)) := by
  obtain ⟨hsF, hsG⟩ := logScale_separated hF hG
  have hV := integrable_arch_shift hsF hsG hf2 hg2 hfl hgl
  have hE : IntegrableOn (fun v : ℝ => Real.exp v *
      (Real.exp v / ((Real.exp v) ^ 2 - 1) * dilR G F (Real.exp v))) (Ioi 0) := by
    refine hV.congr_fun (fun v _ => ?_) measurableSet_Ioi
    have hc := Cvs.WeilForm.ThetaPairingBilinear.crossConv_logScale_log G F (Real.exp_pos v)
    rw [Real.log_exp] at hc
    change Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) *
      crossConv (logScale G) (logScale F) v = _
    rw [hc, ← mul_assoc, densityU_mul_sqrt_exp]
    simp only [dilR]
    ring
  have h := (integrableOn_comp_exp_Ioi
    (fun r : ℝ => r / (r ^ 2 - 1) * dilR G F r) 0)
  change IntegrableOn (fun v : ℝ => Real.exp v *
      (Real.exp v / ((Real.exp v) ^ 2 - 1) * dilR G F (Real.exp v))) (Ioi 0) ↔
    IntegrableOn (fun r : ℝ => r / (r ^ 2 - 1) * dilR G F r) (Ioi (Real.exp 0)) at h
  simpa only [Real.exp_zero] using h.mp hE

/-- The exact arch term for separated functions, assuming their actual
spectral arch domains. No Fubini interchange is used. -/
theorem integral_arch_eq_dilation {F G : ℝ → ℝ}
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : ∀ θ, 1 < θ → G θ = 0)
    (hf2 : MemLp (logScale F) 2 volume) (hf1 : Integrable (logScale F))
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume)
    (hg2 : MemLp (logScale G) 2 volume) (hg1 : Integrable (logScale G))
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale G)) (Ioi 0) volume) :
    (∫ t, archSymbol t * crossSpec (logScale F) (logScale G) t) =
      -(∫ r in Ioi (1 : ℝ), r / (r ^ 2 - 1) * dilR G F r) := by
  obtain ⟨hsF, hsG⟩ := logScale_separated hF hG
  rw [Cvs.L2a.WindowFormTailLimit.integral_arch_crossSpec_eq hf2 hf1 hfl hg2 hg1 hgl]
  have hi0 : (∫ s, logScale F s * logScale G s) = 0 := by
    simpa only [crossConv, add_zero] using
      crossConv_eq_zero_of_separated hsF hsG (le_refl 0)
  rw [hi0, mul_zero, zero_add, archFullBil_eq_shift hsF hsG]
  congr 1
  have he : (∫ v in Ioi (0 : ℝ),
      Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) * crossConv (logScale G) (logScale F) v) =
      ∫ v in Ioi (0 : ℝ), Real.exp v *
        (Real.exp v / ((Real.exp v) ^ 2 - 1) * dilR G F (Real.exp v)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    have hc := Cvs.WeilForm.ThetaPairingBilinear.crossConv_logScale_log G F (Real.exp_pos v)
    rw [Real.log_exp] at hc
    change Cvs.WeilForm.Archimedean.LevyDensity.densityU (2 * v) *
      crossConv (logScale G) (logScale F) v = _
    rw [hc, ← mul_assoc, densityU_mul_sqrt_exp]
    simp only [dilR]
    ring
  rw [he]
  have h := integral_comp_exp_Ioi (fun r : ℝ => r / (r ^ 2 - 1) * dilR G F r) 0
  change (∫ v in Ioi (0 : ℝ), Real.exp v *
      (Real.exp v / ((Real.exp v) ^ 2 - 1) * dilR G F (Real.exp v))) =
    (∫ r in Ioi (Real.exp 0), r / (r ^ 2 - 1) * dilR G F r) at h
  simpa only [Real.exp_zero] using h

/-- The actual Fourier tail has the required spectral arch domain, while
a tame window test provides the other slot. -/
theorem arch_fullTail_eq_dilation {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c)
    {w : ℝ → ℝ} {α β : ℝ} (hw : Tame w α β) (hβ : β ≤ 1) :
    (∫ t, archSymbol t * crossSpec (logScale (fullTail (psi c g))) (logScale w) t) =
      -(∫ r in Ioi (1 : ℝ), r / (r ^ 2 - 1) * dilR w (fullTail (psi c g)) r) := by
  obtain ⟨hf2, hf1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  obtain ⟨hw1, hw2⟩ := hw.log
  exact integral_arch_eq_dilation (fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ)
    (fun θ hθ => hw.supp θ (fun h => by linarith [h.2])) hf2 hf1
    (Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc) hw2 hw1 hw.levy

/-- The pole-weighted dilation correlation is jointly integrable from a
concrete tail bound and the compact support of the actual window test. -/
theorem integrable_dilR_div_prod {F G : ℝ → ℝ} {K α β : ℝ}
    (hFm : Measurable F) (hFK : ∀ θ, 0 < θ → |F θ| ≤ K / θ)
    (hG : Tame G α β) :
    Integrable (fun p : ℝ × ℝ => G p.2 * F (p.1 * p.2) / p.1)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨M, hM⟩ := hG.bdd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := by simpa only [div_one] using (abs_nonneg (F 1)).trans (hFK 1 one_pos)
  have hα0 : 0 < α := hG.pos
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => G p.2 * F (p.1 * p.2) / p.1)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (((hG.meas.comp measurable_snd).mul
      (hFm.comp (measurable_fst.mul measurable_snd))).div measurable_fst).aestronglyMeasurable
  have h1 : Integrable (fun r : ℝ => (M * K / α) * (1 / r ^ 2))
      (volume.restrict (Ioi (1 : ℝ))) :=
    (Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq one_pos).const_mul _
  have h2 : Integrable ((Icc α β).indicator fun _ => (1 : ℝ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.restrict ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const measure_Icc_lt_top.ne))
  refine Integrable.mono' (h1.mul_prod h2) hm ?_
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  have hr0 : 0 < r := lt_trans one_pos hr
  change 0 < θ at hθ
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hr0]
  by_cases hs : θ ∈ Icc α β
  · rw [indicator_of_mem hs, mul_one]
    calc |G θ| * |F (r * θ)| / r ≤ M * (K / (r * θ)) / r := by
          gcongr
          exact hM θ
          exact hFK _ (by positivity)
      _ = M * K / (r ^ 2 * θ) := by field_simp
      _ ≤ M * K / (r ^ 2 * α) := by gcongr; exact hs.1
      _ = M * K / α * (1 / r ^ 2) := by field_simp
  · rw [hG.supp θ hs, abs_zero, zero_mul, zero_div, indicator_of_notMem hs, mul_zero]

/-- One of the tail pole channels is exactly the `1/r` continuous
dilation correlation. All interchanges use the concrete joint bound above. -/
theorem integral_dilR_div_eq_poles {F G : ℝ → ℝ} {K α β : ℝ}
    (hFm : Measurable F) (hFK : ∀ θ, 0 < θ → |F θ| ≤ K / θ)
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : Tame G α β) (hβ : β ≤ 1) :
    (∫ r in Ioi (1 : ℝ), dilR G F r / r) = poleM F * poleP G := by
  have hp := integrable_dilR_div_prod hFm hFK hG
  have he : (∫ r in Ioi (1 : ℝ), dilR G F r / r) =
      ∫ r in Ioi (1 : ℝ), ∫ θ in Ioi (0 : ℝ), G θ * F (r * θ) / r := by
    simp only [dilR, integral_div]
  rw [he, integral_integral_swap hp]
  have hi : ∀ θ ∈ Ioi (0 : ℝ),
      (∫ r in Ioi (1 : ℝ), G θ * F (r * θ) / r) = G θ * poleM F := by
    intro θ hθ
    change 0 < θ at hθ
    by_cases hs : θ ∈ Icc α β
    · have hfun : (fun r : ℝ => G θ * F (r * θ) / r) =
          fun r => (G θ * θ) * (F (θ * r) / (θ * r)) := by
        funext r
        rw [mul_comm θ r]
        field_simp
      rw [hfun, integral_const_mul, integral_comp_mul_left_Ioi
        (fun η : ℝ => F η / η) 1 hθ, mul_one, smul_eq_mul]
      have hset : (∫ η in Ioi θ, F η / η) = ∫ η in Ioi (0 : ℝ), F η / η := by
        symm
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (Ioi_subset_Ioi hθ.le)
        intro η hη
        have hηθ : η ≤ θ := not_lt.mp hη.2
        rw [hF η (hηθ.trans (hs.2.trans hβ)), zero_div]
      rw [hset, poleM]
      field_simp
    · simp only [hG.supp θ hs, zero_mul, zero_div, integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hi, integral_mul_const]
  rw [Cvs.Xi.EImagePoleFunctionals.poleP_of_support hG.supp, Cvs.Xi.EImagePoleFunctionals.mellinR_one, Complex.ofReal_re]
  ring

/-- The reciprocal tail pole cancels the leading `1/r` part of the
separated arch weight. -/
theorem arch_weight_sub_inv {r : ℝ} (hr : 1 < r) :
    r / (r ^ 2 - 1) - 1 / r = 1 / (r * (r ^ 2 - 1)) := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans one_pos hr)
  have hd : r ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- The cubic correction is integrable under the same concrete tail and
window hypotheses; it does not rely on cancellation of divergent integrals. -/
theorem integrable_cubic_dilation {F G : ℝ → ℝ} {K α β : ℝ}
    (hFm : Measurable F) (hFK : ∀ θ, 0 < θ → |F θ| ≤ K / θ)
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : Tame G α β) (hβ : β ≤ 1)
    (hf2 : MemLp (logScale F) 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume) :
    IntegrableOn (fun r => dilR G F r / (r * (r ^ 2 - 1))) (Ioi (1 : ℝ)) := by
  have hsG : ∀ θ, 1 < θ → G θ = 0 :=
    fun θ hθ => hG.supp θ (fun h => by linarith [h.2])
  have hA := integrable_arch_dilation hF hsG hf2 hfl hG.log.2 hG.levy
  have hp := integrable_dilR_div_prod hFm hFK hG
  have hI : IntegrableOn (fun r => dilR G F r / r) (Ioi (1 : ℝ)) := by
    change Integrable (fun r : ℝ => dilR G F r / r) (volume.restrict (Ioi (1 : ℝ)))
    convert hp.integral_prod_left using 1
    funext r
    simp only [dilR, integral_div]
  refine (hA.sub hI).congr_fun (fun r hr => ?_) measurableSet_Ioi
  change 1 < r at hr
  change r / (r ^ 2 - 1) * dilR G F r - dilR G F r / r = _
  rw [show dilR G F r / r = (1 / r) * dilR G F r by ring, ← sub_mul,
    arch_weight_sub_inv hr]
  ring

/-- The separated arch channel and the reciprocal pole combine exactly
into a cubic-decay real-dilation weight. -/
theorem arch_add_reciprocal_pole_eq_cubic {F G : ℝ → ℝ} {K α β : ℝ}
    (hFm : Measurable F) (hFK : ∀ θ, 0 < θ → |F θ| ≤ K / θ)
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : Tame G α β) (hβ : β ≤ 1)
    (hf2 : MemLp (logScale F) 2 volume) (hf1 : Integrable (logScale F))
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume) :
    (∫ t, archSymbol t * crossSpec (logScale F) (logScale G) t) + poleM F * poleP G =
      -(∫ r in Ioi (1 : ℝ), dilR G F r / (r * (r ^ 2 - 1))) := by
  obtain ⟨hg1, hg2⟩ := hG.log
  have hsG : ∀ θ, 1 < θ → G θ = 0 :=
    fun θ hθ => hG.supp θ (fun h => by linarith [h.2])
  have hA := integrable_arch_dilation hF hsG hf2 hfl hg2 hG.levy
  have hp := integrable_dilR_div_prod hFm hFK hG
  have hI : IntegrableOn (fun r => dilR G F r / r) (Ioi (1 : ℝ)) := by
    change Integrable (fun r : ℝ => dilR G F r / r) (volume.restrict (Ioi (1 : ℝ)))
    convert hp.integral_prod_left using 1
    funext r
    simp only [dilR, integral_div]
  rw [integral_arch_eq_dilation hF hsG hf2 hf1 hfl hg2 hg1 hG.levy,
    ← integral_dilR_div_eq_poles hFm hFK hF hG hβ]
  have he : (∫ r in Ioi (1 : ℝ), r / (r ^ 2 - 1) * dilR G F r) -
      (∫ r in Ioi (1 : ℝ), dilR G F r / r) =
      ∫ r in Ioi (1 : ℝ), dilR G F r / (r * (r ^ 2 - 1)) := by
    rw [← integral_sub hA hI]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change 1 < r at hr
    change r / (r ^ 2 - 1) * dilR G F r - dilR G F r / r = _
    rw [show dilR G F r / r = (1 / r) * dilR G F r by ring, ← sub_mul,
      arch_weight_sub_inv hr]
    ring
  linarith

/-- The full actual coupling, with its separated arch channel expressed
in the same dilation orientation as the Mangoldt samples. -/
theorem coupling_eq_dilation {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) (hg0 : g 0 = 0) (hgi : ∫ s in (-1 : ℝ)..1, g s = 0)
    {w : ℝ → ℝ} {α β : ℝ} (hw : Tame w α β) (hβ : β ≤ 1) :
    weilθ (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) g) w =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil w (fullTail (psi c g)) n
        + (∫ r in Ioi (1 : ℝ), r / (r ^ 2 - 1) * dilR w (fullTail (psi c g)) r)
        - poleP (fullTail (psi c g)) * poleM w
        - poleM (fullTail (psi c g)) * poleP w := by
  rw [Cvs.L2a.RungWindowCouplingTail.coupling_formula hg hg₁ hg₂c heven hc hg0 hgi hw hβ,
    arch_fullTail_eq_dilation hg hg₁ hg₂c hc hw hβ]
  ring

/-- The actual aggregate coupling after cancellation of the reciprocal
pole. The remaining pole is retained explicitly as the continuous mean
channel; the Mangoldt sum is still the actual infinite one. -/
theorem coupling_eq_cubic_dilation {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hc : 0 < c) (hg0 : g 0 = 0) (hgi : ∫ s in (-1 : ℝ)..1, g s = 0)
    {w : ℝ → ℝ} {α β : ℝ} (hw : Tame w α β) (hβ : β ≤ 1) :
    weilθ (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) g) w =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil w (fullTail (psi c g)) n
        - poleP (fullTail (psi c g)) * poleM w
        + (∫ r in Ioi (1 : ℝ), dilR w (fullTail (psi c g)) r / (r * (r ^ 2 - 1))) := by
  obtain ⟨hf2, hf1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hC := arch_add_reciprocal_pole_eq_cubic
    (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)
    (fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ)
    (fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ) hw hβ hf2 hf1
    (Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc)
  rw [Cvs.L2a.RungWindowCouplingTail.coupling_formula hg hg₁ hg₂c heven hc hg0 hgi hw hβ]
  linarith

/-- The same aggregate expression for the negative tail pairing itself.
This applies to regularized profiles without additional symmetry or mean
premises on the Fourier tail. -/
theorem neg_weil_fullTail_eq_cubic {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c)
    {w : ℝ → ℝ} {α β : ℝ} (hw : Tame w α β) (hβ : β ≤ 1) :
    -weilθ (fullTail (psi c g)) w =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil w (fullTail (psi c g)) n
        - poleP (fullTail (psi c g)) * poleM w
        + (∫ r in Ioi (1 : ℝ), dilR w (fullTail (psi c g)) r / (r * (r ^ 2 - 1))) := by
  obtain ⟨hf2, hf1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hC := arch_add_reciprocal_pole_eq_cubic
    (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)
    (fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ)
    (fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ) hw hβ hf2 hf1
    (Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc)
  have hd : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (dil (fullTail (psi c g)) w n + dil w (fullTail (psi c g)) n) =
      (ArithmeticFunction.vonMangoldt n : ℝ) * dil w (fullTail (psi c g)) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Cvs.L2a.RungWindowCouplingTail.dil_fullTail_left_eq_zero _ hβ hw.supp hn, zero_add]
  unfold weilθ
  simp_rw [hd]
  linarith

/-- Regularization preserves the concrete two-derivative profile data. -/
theorem regProfile_derivative_data {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) :
    ∃ H₁ H₂ : ℝ → ℝ,
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (Cvs.L2a.WindowFormTailLimit.regProfile c g) (H₁ s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt H₁ (H₂ s) s) ∧
      ContinuousOn H₂ (uIcc (-1) 1) := by
  let t := -(2 * π / c * g 0)
  refine ⟨fun s => g₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s,
    fun s => g₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s, ?_, ?_, ?_⟩
  · intro s hs
    exact (hg s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA c s).const_mul t)
  · intro s hs
    exact (hg₁ s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA1 c s).const_mul t)
  · exact hg₂c.add (continuous_const.mul (Cvs.L2a.FullTailBilinearChannels.continuous_betaA2 c)).continuousOn

/-- The actual untruncated Connes cosine column has the cubic-weight
arch/pole correction, with its remaining continuous mean and all Mangoldt
samples retained. -/
theorem QWbil_connesClass_modeMap_eq_cubic {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.Approximant.CosineColumnTailPairing.connesClass hx) (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) n
      - poleP (Cvs.Approximant.CosineColumnTailPairing.connesTail x) * poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)
      + (∫ r in Ioi (1 : ℝ), dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) r /
          (r * (r ^ 2 - 1))) := by
  rw [Cvs.Approximant.CosineColumnTailPairing.QWbil_connesClass_modeMap hx N f]
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, _, _⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  obtain ⟨H₁, H₂, hH, hH₁, hH₂c⟩ := regProfile_derivative_data hg hg₁ hg₂c
  exact neg_weil_fullTail_eq_cubic hH hH₁ hH₂c (by linarith)
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) (le_refl 1)

end Cvs.WeilForm.SeparatedArchDilationPairing
