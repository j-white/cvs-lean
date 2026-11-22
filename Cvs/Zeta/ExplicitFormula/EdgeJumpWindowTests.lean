import Mathlib
import Cvs.Approximant.ApproximantTransformFactors
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Mollify.ChannelsLipschitz
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ComposedApproximantL2
import Cvs.WeilForm.Mollify.DilateTranslate
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyLevyPointwise
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.Mollify.MollifySmooth
import Cvs.WeilForm.Mollify.WindowNormalisation
import Cvs.WeilForm.PositivityOfRH
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormHomogeneous
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.ExponentialSumTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.WeilPositivityStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit formula for window tests with a jump at the edge

For `f ∈ L²` vanishing off `(0, L]`, Lévy-integrable, with `‖W_L f(ξ)‖ ≤ C/(1 + |Re ξ|)` on `|Im ξ| ≤ ½`, at any complete
`(P, R)` (`e^L ≤ P`, `L ≤ R log 2`): the zero family `m_ρ Re sqTransform(zPoint ρ)` is summable and its sum is the
window Weil form, `kernelZeroSide(sqTransform L f) = weilForm P R f`. No continuity or vanishing at `0, L` is assumed.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Complex

namespace Cvs.Zeta.ExplicitFormula.EdgeJumpWindowTests
open Cvs.ZeroCounting

open Cvs.WeilForm.SelfConvolutionTransform (cf)
open Cvs.WeilForm.Mollify.ComposedApproximant (pre)

/-! ### The prime and archimedean side along the approximants -/

/-- **The window form converges along `ComposedApproximant`'s approximants**, for `η` in the constraint set. -/
theorem tendsto_weilForm_pre {L : ℝ} (hL : 0 < L) (P R : ℕ) {η : ℝ → ℝ}
    (hη : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) (hηm : Measurable η) :
    Tendsto (fun n : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (pre hL η n)) atTop
      (𝓝 (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R η)) := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hη
  set ρ : ℕ → ℝ → ℝ := fun n => Cvs.WeilForm.Mollify.MollifierKernel.kernel
    (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n) with hρ
  have hρc : ∀ n, Continuous (ρ n) := fun n => Cvs.WeilForm.Mollify.MollifierKernel.continuous_kernel _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    Cvs.WeilForm.Mollify.MollifierKernel.hasCompactSupport_kernel _
  have hρm : ∀ n, Measurable (ρ n) := fun n => Cvs.WeilForm.Mollify.MollifierKernel.measurable_kernel _
  have hρi : ∀ n, Integrable (ρ n) (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifierKernel.integrable_kernel _
  have hρnn : ∀ n, ∀ t : ℝ, 0 ≤ ρ n t := fun n t => Cvs.WeilForm.Mollify.MollifierKernel.kernel_nonneg _ t
  have hρ1 : ∀ n, (∫ t : ℝ, ρ n t) = 1 := fun n => Cvs.WeilForm.Mollify.MollifierKernel.integral_kernel _
  set S : ℕ → ℝ → ℝ := fun n => Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n with hS
  have hηwin : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := ⟨hmem, hsupp, hnorm, hlevy⟩
  have hSwin : ∀ n, S n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := fun n =>
    Cvs.WeilForm.Mollify.DilateTranslate.mem_windowSet_shifted hL hηwin n
  have hSmem : ∀ n, MemLp (S n) 2 (volume : Measure ℝ) := fun n => (hSwin n).1
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Cvs.WeilForm.Mollify.ComposedApproximant.measurable_shifted hηm L n
  have hSlevy : ∀ n, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (S n)) (Set.Ioi 0)
      (volume : Measure ℝ) := fun n => (hSwin n).2.2.2
  have hSnorm : ∀ n, (∫ x : ℝ, S n x ^ 2) = 1 := fun n => (hSwin n).2.2.1
  set F : ℕ → ℝ → ℝ := fun n => pre hL η n with hF
  have hFmem : ∀ n, MemLp (F n) 2 (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv (hSmem n) (hSm n) (hρc n) (hρs n) (hρm n) (hρi n)
      (hρnn n) (hρ1 n)
  have hFs : ∀ n, ∀ s ∉ Set.Ioc (0:ℝ) L, F n s = 0 := fun n =>
    Cvs.WeilForm.Mollify.ComposedApproximant.support_pre hL hsupp n
  have hFlevy : ∀ n, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (F n)) (Set.Ioi 0)
      (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifyLevyPointwise.integrableOn_levy_conv (hSmem n) (hSm n) (hρc n) (hρs n) (hρm n)
      (hρi n) (hρnn n) (hρ1 n) (hSlevy n)
  have hFbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ 1 := by
    intro n
    have h := Cvs.WeilForm.Mollify.MollifyLevyPointwise.integral_conv_sq_le (hSmem n) (hSm n) (hρc n) (hρs n)
      (hρm n) (hρi n) (hρnn n) (hρ1 n)
    rwa [hSnorm n] at h
  have hconv := Cvs.WeilForm.Mollify.ComposedApproximantL2.tendsto_pre_error hL hmem hηm
  have harchle : ∀ n, Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n)
      ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (S n) := fun n =>
    Cvs.WeilForm.Mollify.MollifyLevyPointwise.archFull_conv_le (hSmem n) (hSm n) (hρc n) (hρs n) (hρm n)
      (hρi n) (hρnn n) (hρ1 n) (hSlevy n)
  have hbtend := Cvs.WeilForm.Mollify.DilateTranslate.tendsto_archFull_shifted hηwin L
  have hFc : ∀ n, AEStronglyMeasurable (Cvs.Zeta.Explicit.Weil.selfConvolution (F n))
      (volume : Measure ℝ) := fun n =>
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution (hFmem n)).aestronglyMeasurable
  have hηc : AEStronglyMeasurable (Cvs.Zeta.Explicit.Weil.selfConvolution η) (volume : Measure ℝ) :=
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hmem).aestronglyMeasurable
  have harch := Cvs.WeilForm.Mollify.ChannelsLipschitz.tendsto_archFull_of_le (C := 1) hmem hFmem hηc hFc
    hlevy hFlevy hconv hFbdd harchle hbtend
  exact Cvs.WeilForm.Mollify.ChannelsLipschitz.tendsto_weilForm_of_tendsto_archFull (L := L) (C := 1)
    P R (by norm_num) hmem hFmem hsupp hFs hFbdd hconv harch

/-! ### The explicit formula for smooth tests -/

/-- **The zero side is the window form for `C²` tests** supported in `(0, L]`, at any complete
`(P, R)`. -/
theorem kernelZeroSide_eq_weilForm_of_contDiff {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) (lam a : ℝ)
    {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    kernelZeroSide (Cvs.Detection.sqTransform L (cf f)) lam a = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have hc := hf.continuous
  have h0 : f 0 = 0 := hsupp 0 (by simp)
  have hLz : f L = 0 := by
    have hlim : Filter.Tendsto f (nhdsWithin L (Ioi L)) (nhds (f L)) :=
      hc.continuousAt.continuousWithinAt.tendsto
    have hev : f =ᶠ[nhdsWithin L (Ioi L)] fun _ => 0 :=
      Filter.eventually_of_mem self_mem_nhdsWithin fun s hs => hsupp s fun h => by
        exact absurd h.2 (not_le.2 hs)
    exact tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  have hind : Set.indicator (Set.Ioc (0:ℝ) L) f = f := by
    funext s; by_cases hs : s ∈ Set.Ioc (0:ℝ) L
    · simp [hs]
    · simp [hs, hsupp s hs]
  have hcs : HasCompactSupport f :=
    HasCompactSupport.intro isCompact_Icc fun s hs => hsupp s fun h => hs (Ioc_subset_Icc_self h)
  have hf2 : ContDiff ℝ (1 + 1) f := by norm_num; exact hf
  have hd := contDiff_succ_iff_deriv.mp hf2
  have hf1 : ContDiff ℝ (0 + 1) (deriv f) := by simpa using hd.2.2
  have hd' := contDiff_succ_iff_deriv.mp hf1
  obtain ⟨M0, hM0⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨M2, hM2⟩ := hd'.2.2.continuous.bounded_above_of_compact_support hcs.deriv.deriv
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := Cvs.Finite.OddSectorZeroSide.admissible_of_C2 hL
    (fun s => (hd.1 s).hasDerivAt) (fun s => (hd'.1 s).hasDerivAt) hc hd.2.2.continuous
    hd'.2.2.continuous h0 hLz (M0 := M0) (M2 := M2) (fun s => by simpa using hM0 s)
    (fun s => by simpa using hM2 s)
  have hk := Cvs.WeilForm.PositivityOfRH.kernelZeroSide_eq_weilForm_of_complete hL hc h0 hLz hC0 hC2 hplain hquad lam a
    hP hR
  rwa [hind] at hk

/-! ### The zero side under a linear envelope -/

/-- `|Im zPoint ρ| = |Re ρ − ½| ≤ ½`. -/
theorem abs_zPoint_im_le (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    |(zPoint rho).im| ≤ 1 / 2 := by
  have h := Cvs.Zeta.GaussKernel.AdmissibleKernel.abs_re_sub_half_le rho
  have : (zPoint rho).im = -(((rho : ℂ)).re - 1 / 2) := by
    unfold zPoint; simp
  rw [this, abs_neg]; exact h

theorem abs_neg_zPoint_im_le (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    |(-zPoint rho).im| ≤ 1 / 2 := by
  rw [Complex.neg_im, abs_neg]; exact abs_zPoint_im_le rho

/-- **One zero-side summand under a linear envelope**: if `‖W(±zPoint ρ)‖ ≤ K/(1 + |γ|)`, then
`|m_ρ Re(W(z)W(−z))| ≤ m_ρ K²/(1 + γ²)`. -/
theorem abs_summand_le {W : ℂ → ℂ} {K : ℝ} (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet)
    (h1 : ‖W (zPoint rho)‖ ≤ K / (1 + |((rho : ℂ)).im|))
    (h2 : ‖W (-zPoint rho)‖ ≤ K / (1 + |((rho : ℂ)).im|)) :
    ‖(Cvs.Criterion.divisorWeight rho : ℝ) * (W (zPoint rho) * W (-zPoint rho)).re‖
      ≤ (Cvs.Criterion.divisorWeight rho : ℝ) * (K ^ 2 * (1 / (1 + ((rho : ℂ)).im ^ 2))) := by
  set γ := ((rho : ℂ)).im
  have hw : (0:ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
  have hr : 0 ≤ |γ| := abs_nonneg _
  have hK : 0 ≤ K / (1 + |γ|) := (norm_nonneg _).trans h1
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ hw
  calc |(W (zPoint rho) * W (-zPoint rho)).re| ≤ ‖W (zPoint rho) * W (-zPoint rho)‖ :=
        Complex.abs_re_le_norm _
    _ = ‖W (zPoint rho)‖ * ‖W (-zPoint rho)‖ := norm_mul _ _
    _ ≤ (K / (1 + |γ|)) * (K / (1 + |γ|)) := mul_le_mul h1 h2 (norm_nonneg _) hK
    _ = K ^ 2 * (1 / (1 + |γ|) ^ 2) := by rw [div_mul_div_comm, ← sq, ← sq, mul_one_div]
    _ ≤ K ^ 2 * (1 / (1 + γ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [sq_abs γ]

/-- A linear envelope at `zPoint ρ` and `−zPoint ρ`, read off the envelope on the strip `|Im| ≤ ½`. -/
theorem envelope_at {W : ℂ → ℂ} {K : ℝ}
    (henv : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 → ‖W ξ‖ ≤ K / (1 + |ξ.re|))
    (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    ‖W (zPoint rho)‖ ≤ K / (1 + |((rho : ℂ)).im|)
      ∧ ‖W (-zPoint rho)‖ ≤ K / (1 + |((rho : ℂ)).im|) := by
  have hre : (zPoint rho).re = ((rho : ℂ)).im := Cvs.Finite.ZeroSideGramMatrix.zPoint_re rho
  refine ⟨?_, ?_⟩
  · have := henv _ (abs_zPoint_im_le rho); rwa [hre] at this
  · have := henv _ (abs_neg_zPoint_im_le rho); rwa [Complex.neg_re, abs_neg, hre] at this

/-- **A linear envelope makes the zero family summable.** -/
theorem summable_of_envelope {L : ℝ} {f : ℝ → ℝ} {C : ℝ}
    (henv : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C / (1 + |ξ.re|)) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Detection.sqTransform L (cf f) (zPoint rho)).re := by
  refine Summable.of_norm_bounded
    ((Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left (C ^ 2)).congr fun rho => ?_)
    fun rho => abs_summand_le rho (envelope_at henv rho).1 (envelope_at henv rho).2
  ring

/-- **The zero sides converge along the approximants**, under a linear envelope on `|Im ξ| ≤ ½`. -/
theorem tendsto_zeroSide_pre {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ} (hη : MemLp η 2 volume)
    (hηm : Measurable η) (hηs : ∀ s ∉ Ioc (0 : ℝ) L, η s = 0) {C : ℝ}
    (henv : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf η) ξ‖ ≤ C / (1 + |ξ.re|)) (lam a : ℝ) :
    Tendsto (fun n => kernelZeroSide (Cvs.Detection.sqTransform L (cf (pre hL η n))) lam a) atTop
      (𝓝 (kernelZeroSide (Cvs.Detection.sqTransform L (cf η)) lam a)) := by
  set K : ℝ := 2 * Real.exp (L * (1 / 2) / 2) * C with hK
  have henvn : ∀ n, ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf (pre hL η n)) ξ‖ ≤ K / (1 + |ξ.re|) := fun n ξ hξ =>
    Cvs.Approximant.ApproximantTransformFactors.norm_windowTransform_pre_le hL hη hηs henv n ξ hξ
  unfold kernelZeroSide
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ) * (K ^ 2 * (1 / (1 + ((rho : ℂ)).im ^ 2))))
    ?_ ?_ ?_
  · refine (Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left (K ^ 2)).congr fun rho => ?_
    ring
  · intro rho
    have h1 := Cvs.Approximant.ApproximantTransformFactors.tendsto_windowTransform_pre hL hη hηm hηs (zPoint rho)
    have h2 := Cvs.Approximant.ApproximantTransformFactors.tendsto_windowTransform_pre hL hη hηm hηs (-zPoint rho)
    have hre := (Complex.continuous_re.tendsto _).comp (h1.mul h2)
    exact hre.const_mul (Cvs.Criterion.divisorWeight rho : ℝ)
  · refine Eventually.of_forall fun n rho => ?_
    exact abs_summand_le rho (envelope_at (henvn n) rho).1 (envelope_at (henvn n) rho).2

/-! ### The explicit formula on the constraint set, then for every enveloped test -/

/-- **The explicit formula on the constraint set**, under a linear envelope on `|Im ξ| ≤ ½`. -/
theorem kernelZeroSide_eq_weilForm_windowSet {L : ℝ} (hL : 0 < L) {η : ℝ → ℝ}
    (hη : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) (hηm : Measurable η) {C : ℝ}
    (henv : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf η) ξ‖ ≤ C / (1 + |ξ.re|)) (lam a : ℝ)
    {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    kernelZeroSide (Cvs.Detection.sqTransform L (cf η)) lam a = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R η := by
  have hZ := tendsto_zeroSide_pre hL hη.1 hηm hη.2.1 henv lam a
  have hW := tendsto_weilForm_pre hL P R hη hηm
  have heq : ∀ n, kernelZeroSide (Cvs.Detection.sqTransform L (cf (pre hL η n))) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (pre hL η n) := fun n =>
    kernelZeroSide_eq_weilForm_of_contDiff hL
      (Cvs.WeilForm.Mollify.MollifySmooth.contDiff_conv (Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hη.1 L n)
        (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n))
      (Cvs.WeilForm.Mollify.ComposedApproximant.support_pre hL hη.2.1 n) lam a hP hR
  exact tendsto_nhds_unique hZ (hW.congr fun n => (heq n).symm)

/-- The squared transform is quadratic in the test: `sqTransform(c f) = c² sqTransform f`. -/
theorem sqTransform_smul (L c : ℝ) (f : ℝ → ℝ) (ξ : ℂ) :
    Cvs.Detection.sqTransform L (cf fun x => c * f x) ξ
      = ((c ^ 2 : ℝ) : ℂ) * Cvs.Detection.sqTransform L (cf f) ξ := by
  have h : cf (fun x => c * f x) = fun s => (c : ℂ) * cf f s := by
    funext s; simp [cf]
  unfold Cvs.Detection.sqTransform
  rw [h, Cvs.Detection.windowTransform_const_mul, Cvs.Detection.windowTransform_const_mul]
  push_cast; ring

/-- **The explicit formula for window tests with a jump**: for `f ∈ L²` vanishing off `(0, L]`,
Lévy-integrable, with `‖W_L f(ξ)‖ ≤ C/(1 + |Re ξ|)` on `|Im ξ| ≤ ½`, at any complete `(P, R)`, the zero
family is summable and `kernelZeroSide(sqTransform L f) = weilForm P R f`. -/
theorem kernelZeroSide_eq_weilForm_of_envelope {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hfm : Measurable f) (hfs : ∀ s ∉ Ioc (0 : ℝ) L, f s = 0)
    (hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume) {C : ℝ}
    (henv : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C / (1 + |ξ.re|)) (lam a : ℝ)
    {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    kernelZeroSide (Cvs.Detection.sqTransform L (cf f)) lam a = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f
      ∧ Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (Cvs.Detection.sqTransform L (cf f) (zPoint rho)).re := by
  refine ⟨?_, summable_of_envelope henv⟩
  set E : ℝ := ∫ x : ℝ, f x ^ 2 with hE
  rcases lt_or_ge 0 E with hEpos | hEle
  · set c : ℝ := (Real.sqrt E)⁻¹ with hc
    have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hEpos).ne'
    have hηw := Cvs.WeilForm.Mollify.WindowNormalisation.mem_windowSet_normalised hf hfs hlevy hEpos
    have hηm : Measurable fun x => c * f x := measurable_const.mul hfm
    have hWη : ∀ ξ : ℂ, Cvs.Detection.windowTransform L (cf fun x => c * f x) ξ
        = (c : ℂ) * Cvs.Detection.windowTransform L (cf f) ξ := by
      intro ξ
      have h : cf (fun x => c * f x) = fun s => (c : ℂ) * cf f s := by
        funext s; simp [cf]
      rw [h, Cvs.Detection.windowTransform_const_mul]
    have henvη : ∀ ξ : ℂ, |ξ.im| ≤ 1 / 2 →
        ‖Cvs.Detection.windowTransform L (cf fun x => c * f x) ξ‖ ≤ (|c| * C) / (1 + |ξ.re|) := by
      intro ξ hξ
      rw [hWη, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (henv ξ hξ) (abs_nonneg c)
    have hk := kernelZeroSide_eq_weilForm_windowSet hL hηw hηm henvη lam a hP hR
    rw [Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul] at hk
    have hzs : kernelZeroSide (Cvs.Detection.sqTransform L (cf fun x => c * f x)) lam a
        = c ^ 2 * kernelZeroSide (Cvs.Detection.sqTransform L (cf f)) lam a := by
      unfold kernelZeroSide
      rw [← tsum_mul_left]
      refine tsum_congr fun rho => ?_
      rw [sqTransform_smul, Complex.re_ofReal_mul]
      ring
    rw [hzs] at hk
    exact mul_left_cancel₀ (pow_ne_zero 2 hc0) hk
  · have hE0 : E = 0 := le_antisymm hEle (integral_nonneg fun x => sq_nonneg _)
    have hae : (fun x => f x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hf.integrable_sq).1 hE0
    have hfae : f =ᵐ[volume] fun _ => 0 := hae.mono fun x hx => by
      simpa using hx
    have hW0 : ∀ ξ : ℂ, Cvs.Detection.windowTransform L (cf f) ξ = 0 := by
      intro ξ
      rw [Cvs.Approximant.ApproximantTransformFactors.windowTransform_eq_integral hL.le hfs]
      refine integral_eq_zero_of_ae (hfae.mono fun x hx => ?_)
      simp [hx]
    have hlhs : kernelZeroSide (Cvs.Detection.sqTransform L (cf f)) lam a = 0 := by
      unfold kernelZeroSide Cvs.Detection.sqTransform
      simp [hW0]
    rw [hlhs, Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R hfae]
    have h0 := Cvs.WeilForm.WeilFormHomogeneous.weilForm_smul P R 0 (fun _ => (0 : ℝ))
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h0
    exact h0.symm

end Cvs.Zeta.ExplicitFormula.EdgeJumpWindowTests
