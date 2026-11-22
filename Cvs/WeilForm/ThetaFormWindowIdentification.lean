import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Xi.EImagePoleFunctionals
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.VerticalLineShift
import Cvs.Zeta.WeilPositivityStatement
import Cvs.Zeta.ZetaDerivFunctionalEquation
import Cvs.Zeta.ZetaDerivStripGrowth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
For `F` supported in `[α, β] ⊂ (0, ∞)` with Mellin transform `O(1/|t|)`, `weilθ F F` is the window's Weil
form `weilForm P R (logScale F)` once `P ≥ β/α` and `R log 2 ≥ log(β/α)`. The poles are `∫ F` and
`∫ F/θ`, `crossSpec f f` is the spectral density, and `(f ⋆ f)(log k) = √k ∫_{θ>0} F(θ) F(kθ)` turns
the prime-power side into the von Mangoldt sum of dilates, which stops at `n = β/α`.
-/

noncomputable section

namespace Cvs.WeilForm.ThetaFormWindowIdentification

open Real Set Filter Topology MeasureTheory
open Complex (I)
open scoped ComplexConjugate
open Cvs.WeilForm.ThetaSpaceParseval (mellinR poleP poleM dil weilθ)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.FullTailPolarisation (crossSpec)

/-! ### The log-scale self-convolution at `log k` -/

/-- `(f ⋆ f)(log k) = √k ∫_{θ>0} F(θ) F(kθ)` for `f = logScale F`, with no support condition on `F`. -/
theorem selfConvolution_logScale_log (F : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) (Real.log k)
      = √k * ∫ θ in Ioi (0 : ℝ), F θ * F (k * θ) := by
  unfold Cvs.Zeta.Explicit.Weil.selfConvolution
  have e : (fun x => logScale F x * logScale F (x + Real.log k))
      = fun x => exp x • (fun θ => √k * (F θ * F (k * θ))) (exp x) := by
    funext x; unfold logScale
    rw [smul_eq_mul, exp_add, exp_log hk, mul_comm (exp x) k]
    have h1 : exp ((x + Real.log k) / 2) = exp (x / 2) * √k := by
      rw [show (x + Real.log k) / 2 = x / 2 + Real.log k / 2 by ring, exp_add, sqrt_eq_rpow,
        rpow_def_of_pos hk]
      ring_nf
    rw [h1, ← Cvs.L2a.TailLogScaleTest.exp_half_sq x]; ring
  rw [e, ← integral_const_mul]
  exact Cvs.WeilForm.ThetaSpaceParseval.integral_exp_smul_Ioi (fun θ => √k * (F θ * F (k * θ)))

/-- The diagonal cross density is the spectral density. -/
theorem crossSpec_self (f : ℝ → ℝ) (t : ℝ) :
    crossSpec f f t = Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  unfold crossSpec Cvs.WeilForm.SelfConvolutionCosine.specDensity
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-! ### The pole channel -/

/-- `∫ f e^{s/2} = ∫_{θ>0} F` for `f = logScale F`. -/
theorem integral_logScale_mul_exp (F : ℝ → ℝ) :
    ∫ s, logScale F s * exp (s / 2) = ∫ θ in Ioi (0 : ℝ), F θ := by
  have e : (fun s => logScale F s * exp (s / 2)) = fun s => exp s • F (exp s) := by
    funext s; unfold logScale; rw [smul_eq_mul, ← Cvs.L2a.TailLogScaleTest.exp_half_sq]; ring
  rw [e, Cvs.WeilForm.ThetaSpaceParseval.integral_exp_smul_Ioi]

/-- `∫ f e^{−s/2} = P₋F` for `f = logScale F`. -/
theorem integral_logScale_mul_exp_neg (F : ℝ → ℝ) :
    ∫ s, logScale F s * exp (-(s / 2)) = poleM F := by
  have e : (fun s => logScale F s * exp (-(s / 2)))
      = fun s => exp s • (fun θ => F θ / θ) (exp s) := by
    funext s; unfold logScale
    rw [smul_eq_mul, mul_assoc, ← exp_add, show s / 2 + -(s / 2) = 0 by ring, exp_zero]
    field_simp
  rw [e]
  exact Cvs.WeilForm.ThetaSpaceParseval.integral_exp_smul_Ioi (fun θ => F θ / θ)

/-- For compactly supported `F`, `P₊F = ∫_{θ>0} F`. -/
theorem poleP_eq_integral {F : ℝ → ℝ} {α β : ℝ} (hsupp : ∀ θ ∉ Icc α β, F θ = 0) :
    poleP F = ∫ θ in Ioi (0 : ℝ), F θ := by
  rw [Cvs.Xi.EImagePoleFunctionals.poleP_of_support hsupp, Cvs.Xi.EImagePoleFunctionals.mellinR_one,
    Complex.ofReal_re]

/-! ### The arch channel -/

/-- Mellin decay `C/‖s‖` on `−½ ≤ Re s ≤ 2` gives the decay `C/|Im s|` for `|Im s| ≥ 1`. -/
theorem mellin_decay_of_div_norm {F : ℝ → ℝ}
    (h : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → s ≠ 0 → ‖mellinR F s‖ ≤ C / ‖s‖) :
    ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR F s‖ ≤ C / |s.im| := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun s h1 h2 h3 => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at h3
  have him : 0 < |s.im| := by linarith
  calc ‖mellinR F s‖ ≤ C / ‖s‖ := hC s h1 h2 hs0
    _ ≤ max C 0 / ‖s‖ := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 / |s.im| :=
        div_le_div_of_nonneg_left (le_max_right _ _) him (Complex.abs_im_le_norm s)

/-- Mellin decay on the critical line makes `ρ_f · (a(t) − a(0))` integrable, `f = logScale F`. -/
theorem integrable_specDensity_mul_arch_of_decay {F : ℝ → ℝ} (hf : Integrable (logScale F))
    (hdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR F s‖ ≤ C / |s.im|) :
    Integrable fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) t
      * (archSymbol t - archSymbol 0) := by
  obtain ⟨C, hC⟩ := hdec
  obtain ⟨C₁, hC₁⟩ := Cvs.Zeta.ZetaDerivFunctionalEquation.abs_archSymbol_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₁0 : 0 ≤ C₁ := by
    have h0 := hC₁ 0
    simp only [abs_zero, add_zero] at h0
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : C₁ * (1 + Real.log 2) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
    linarith [abs_nonneg (archSymbol 0)]
  set A := C₁ + |archSymbol 0| with hA
  have hA0 : 0 ≤ A := add_nonneg hC₁0 (abs_nonneg _)
  have hc : Continuous fun t => ((Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) t
      * (archSymbol t - archSymbol 0) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hf).mul
      (Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.sub continuous_const))
  have hbound : ∀ y : ℝ, 1 ≤ |y| →
      ‖((Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) y * (archSymbol y - archSymbol 0) : ℝ) : ℂ)‖
        ≤ (4 * C ^ 2 / (2 * π) * (33 * A)) * (1 + |y|) ^ (-(31 / 16 : ℝ)) := by
    intro y hy
    have hu : 0 < 1 + |y| := by positivity
    have hM : ‖mellinR F (1 / 2 - y * I)‖ ≤ C / |y| := by
      have h := hC (1 / 2 - y * I) (by simp; norm_num) (by simp; norm_num) (by simpa using hy)
      simpa using h
    have hsd : Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) y
        ≤ 4 * C ^ 2 / (2 * π) * (1 + |y|) ^ (-(2 : ℝ)) := by
      unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
      rw [Cvs.WeilForm.ThetaSpaceParseval.fourier_logScale]
      have h1 : ‖mellinR F (1 / 2 - y * I)‖ ^ 2 ≤ (C / |y|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hM 2
      have h2 : (C / |y|) ^ 2 ≤ 4 * C ^ 2 * (1 + |y|) ^ (-(2 : ℝ)) := by
        have hy0 : 0 < |y| := by linarith
        rw [Real.rpow_neg hu.le, Real.rpow_two, div_pow]
        have hsq : (1 + |y|) ^ 2 ≤ 4 * |y| ^ 2 := by nlinarith
        rw [div_le_iff₀ (by positivity)]
        calc C ^ 2 = C ^ 2 * ((1 + |y|) ^ 2)⁻¹ * (1 + |y|) ^ 2 := by field_simp
          _ ≤ C ^ 2 * ((1 + |y|) ^ 2)⁻¹ * (4 * |y| ^ 2) := by gcongr
          _ = 4 * C ^ 2 * ((1 + |y|) ^ 2)⁻¹ * |y| ^ 2 := by ring
      calc ‖mellinR F (1 / 2 - y * I)‖ ^ 2 / (2 * π)
          ≤ (4 * C ^ 2 * (1 + |y|) ^ (-(2 : ℝ))) / (2 * π) := by gcongr; exact h1.trans h2
        _ = 4 * C ^ 2 / (2 * π) * (1 + |y|) ^ (-(2 : ℝ)) := by ring
    have harch : |archSymbol y - archSymbol 0| ≤ 33 * A * (1 + |y|) ^ (1 / 16 : ℝ) := by
      have h1 := hC₁ y
      have h2 := Cvs.Zeta.ZetaDerivStripGrowth.one_add_log_le_rpow (abs_nonneg y)
      have hlog : 1 ≤ 1 + Real.log (2 + |y|) := by
        have : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
        linarith
      calc |archSymbol y - archSymbol 0| ≤ |archSymbol y| + |archSymbol 0| := by
            have := abs_sub_le (archSymbol y) 0 (archSymbol 0)
            simpa using this
        _ ≤ C₁ * (1 + Real.log (2 + |y|)) + |archSymbol 0| * (1 + Real.log (2 + |y|)) :=
            add_le_add h1 (le_mul_of_one_le_right (abs_nonneg _) hlog)
        _ = A * (1 + Real.log (2 + |y|)) := by rw [hA]; ring
        _ ≤ A * (33 * (1 + |y|) ^ (1 / 16 : ℝ)) := by gcongr
        _ = 33 * A * (1 + |y|) ^ (1 / 16 : ℝ) := by ring
    have hsd0 := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg (logScale F) y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hsd0]
    calc Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) y * |archSymbol y - archSymbol 0|
        ≤ (4 * C ^ 2 / (2 * π) * (1 + |y|) ^ (-(2 : ℝ))) * (33 * A * (1 + |y|) ^ (1 / 16 : ℝ)) :=
          mul_le_mul hsd harch (abs_nonneg _) (by positivity)
      _ = (4 * C ^ 2 / (2 * π) * (33 * A)) * ((1 + |y|) ^ (-(2 : ℝ)) * (1 + |y|) ^ (1 / 16 : ℝ)) := by
          ring
      _ = (4 * C ^ 2 / (2 * π) * (33 * A)) * (1 + |y|) ^ (-(31 / 16 : ℝ)) := by
          rw [← Real.rpow_add hu]; norm_num
  have hint := Cvs.Zeta.VerticalLineShift.integrable_of_decay hc (by norm_num : (1 : ℝ) < 31 / 16) hbound
  simpa using hint.re

/-! ### The prime channel -/

/-- `⟨F, F(n·)⟩ = 0` once `n > β/α`. -/
theorem dil_self_eq_zero {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, F θ = 0)
    {n : ℕ} (hn : β / α < n) : dil F F n = 0 := by
  unfold dil
  have hnα : β < n * α := by rwa [div_lt_iff₀ hα] at hn
  refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
  by_cases hθ : θ ∈ Icc α β
  · have hle : (n : ℝ) * α ≤ n * θ := mul_le_mul_of_nonneg_left hθ.1 (Nat.cast_nonneg n)
    have : F (n * θ) = 0 := hsupp _ fun h => by linarith [h.2]
    rw [this, mul_zero]
  · rw [hsupp θ hθ, zero_mul]

/-- A prime power `n ≤ P` with `log n ≤ R log 2` is one of the truncation's prime powers. -/
theorem mem_primePowIndex {P R n : ℕ} (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hP : n ≤ P) (hR : Real.log n ≤ R * Real.log 2) :
    n ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R := by
  have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  unfold Cvs.WeilForm.PrimePowerIndexed.primePowIndex
  refine Finset.mem_image.mpr ⟨(p, k), ?_, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hpP : p ≤ P := le_trans (Nat.le_self_pow hk.ne' p) hP
  have hkR : k ≤ R := by
    have h2k : (2 : ℝ) ^ k ≤ ((p ^ k : ℕ) : ℝ) := by
      push_cast; exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp2) k
    have hl : (k : ℝ) * Real.log 2 ≤ Real.log ((p ^ k : ℕ) : ℝ) := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2k
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact_mod_cast le_of_mul_le_mul_right (hl.trans hR) hl2
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  exact ⟨⟨Nat.lt_succ_of_le hpP, hp⟩, hk, hkR⟩

/-- **The prime channel.** The von Mangoldt sum of self-dilates is the truncated prime-power side
of `f ⋆ f` once `P ≥ β/α` and `R log 2 ≥ log(β/α)`. -/
theorem tsum_dil_self_eq {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, F θ = 0)
    {P R : ℕ} (hP : β / α ≤ P) (hR : Real.log (β / α) ≤ R * Real.log 2) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F F n + dil F F n)
      = Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
          (Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F)) := by
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  rw [tsum_eq_sum (s := Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [Cvs.L2a.TailLogScaleTest.selfConvolution_neg_log, selfConvolution_logScale_log F hk']
      have hs : (k : ℝ) ^ (-(1 / 2) : ℝ) * √(k : ℝ) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk']; norm_num
      unfold dil
      set d := ∫ θ in Ioi (0 : ℝ), F θ * F (k * θ)
      linear_combination (-(2 * ArithmeticFunction.vonMangoldt k * d)) * hs
  · intro n hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    by_cases hd : β / α < n
    · simp [dil_self_eq_zero hα hsupp hd]
    exfalso
    apply hn
    replace hd := not_lt.mp hd
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hΛ)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    exact mem_primePowIndex hΛ (by exact_mod_cast hd.trans hP)
      ((Real.log_le_log hn' hd).trans hR)

/-! ### The bridge -/

/-- **`weilθ F F` is the window's Weil form** of `logScale F`, for `F` bounded, measurable,
supported in `[α, β] ⊂ (0, ∞)`, with Mellin transform `O(1/|t|)`, `P ≥ β/α`, `R log 2 ≥ log(β/α)`. -/
theorem weilθ_self_eq_weilForm {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ θ ∉ Icc α β, F θ = 0) (hFm : Measurable F) (hFb : ∃ M, ∀ θ, |F θ| ≤ M)
    (hFdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR F s‖ ≤ C / |s.im|)
    {P R : ℕ} (hP : β / α ≤ P) (hR : Real.log (β / α) ≤ R * Real.log 2) :
    weilθ F F = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale F) := by
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨hf1, hf2⟩ := Cvs.WeilForm.EImageRadical.integrable_logScale_of_support hFm hM hα hsupp
  have hsq : Integrable fun s => logScale F s ^ 2 :=
    (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).mp hf2
  have hcross : ∀ u : ℝ, Integrable fun s => logScale F s * logScale F (s + u) :=
    Cvs.WeilForm.TruncatedFormPolarised.integrable_cross hf2 hf2
  have hsda := integrable_specDensity_mul_arch_of_decay hf1 hFdec
  have hnn : 0 ≤ᵐ[volume] fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) t
      * (archSymbol t - archSymbol 0) :=
    Eventually.of_forall fun t => mul_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t)
      (Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg t)
  have hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume :=
    (Cvs.WeilForm.LevyDomainSpectral.levyDom_iff hf2 hf1 hsq hcross).mpr
      ((hasFiniteIntegral_iff_ofReal hnn).mp hsda.2)
  have hsd := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.weilForm_spectral P R hf2 hf1 hsq hcross hlevy hsd hsda,
    integral_logScale_mul_exp, integral_logScale_mul_exp_neg, ← poleP_eq_integral hsupp,
    ← tsum_dil_self_eq hα hsupp hP hR]
  unfold weilθ
  simp_rw [crossSpec_self]
  ring

end Cvs.WeilForm.ThetaFormWindowIdentification
