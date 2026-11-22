import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.WeilForm.CentredGaussianTest
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.GaussianTestEnvelope
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.LipschitzTentBasis
import Cvs.WeilForm.PositivityOfRH
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WeightedZeroSide
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.OffsetKernelTest
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.WeightedPositivityRH
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LogEnvelopeSquareSummable
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Weil's criterion for windows: RH as nonnegativity of `Q` at `L = log x`

The zero side of `testL` at `L = log x` tends to `WeightedZeroSide`'s weighted Gaussian zero side (`GaussianTestEnvelope`'s
envelope and `LogEnvelopeSquareSummable`'s summability dominate it), and each term is a value of `Q` on a form-domain
class (Cvs.WeilForm.LipschitzTentBasis, Cvs.WeilForm.PositivityOfRH). So `0 ≤ Q` for all large `x` gives `WeightedPositivityRH`'s weighted positivity, hence RH;
Cvs.WeilForm.PositivityOfRH gives the converse.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.WindowWeilCriterion
open Cvs.ZeroCounting

open Cvs.WeilForm.CentredGaussianTest (testL)
open Cvs.WeilForm.GaussianTestEnvelope (V)

/-- **The zero side of `testL` converges** as `L → ∞`, to the zero side of `gaussAmp²`. -/
theorem tendsto_zeroSide_testL {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    Filter.Tendsto
      (fun L => kernelZeroSide (Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L))) lam a)
      Filter.atTop
      (nhds (kernelZeroSide (fun w => Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a w ^ 2) lam a)) := by
  obtain ⟨C, hC0, hC⟩ := Cvs.WeilForm.GaussianTestEnvelope.exists_V_envelope hlam a
  unfold kernelZeroSide
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ) * (C ^ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2)) ?_ ?_ ?_
  · have h := Cvs.Zeta.LogEnvelopeSquareSummable.summable_divisorWeight_phi_sq.mul_left (C ^ 2)
    refine h.congr fun rho => ?_
    ring
  · intro rho
    set z := zPoint rho with hz
    have hz1 := Cvs.Finite.ZeroSideGramMatrix.zPoint_im_le rho
    have hz2 := Cvs.Finite.ZeroSideGramMatrix.neg_zPoint_im_le rho
    have hprod := (Cvs.WeilForm.GaussianTestEnvelope.tendsto_V hlam a hz1).mul (Cvs.WeilForm.GaussianTestEnvelope.tendsto_V hlam a hz2)
    have hre := (Complex.continuous_re.tendsto _).comp hprod
    have hfin := hre.const_mul (Cvs.Criterion.divisorWeight rho : ℝ)
    have hlimv : (Cvs.Criterion.divisorWeight rho : ℝ) * (Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a z
        * Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a (-z)).re
        = (Cvs.Criterion.divisorWeight rho : ℝ)
          * ((fun w => Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a w ^ 2) z).re := by
      rw [Cvs.GaussKernel.gaussAmp_even]; simp only [pow_two]
    rw [← hlimv]
    refine hfin.congr' (Filter.Eventually.of_forall fun L => ?_)
    simp only [Function.comp_apply, Cvs.WeilForm.GaussianTestEnvelope.sqTransform_testL, hz]
  · filter_upwards [Filter.eventually_ge_atTop 0] with L hL
    intro rho
    set z := zPoint rho with hz
    have hz1 := Cvs.Finite.ZeroSideGramMatrix.zPoint_im_le rho
    have hz2 := Cvs.Finite.ZeroSideGramMatrix.neg_zPoint_im_le rho
    have hw : (0:ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
    have hre0 : 0 ≤ |z.re| := abs_nonneg _
    have hphi := Cvs.Zeta.LogEnvelopeSquareSummable.phi_nonneg hre0
    have hphi1 := Cvs.Zeta.LogEnvelopeSquareSummable.one_div_le_phi hre0
    rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ hw
    have hnegre : |(-z).re| = |z.re| := by rw [Complex.neg_re, abs_neg]
    have hb : ∀ w : ℂ, |w.im| ≤ 3 / 2 → |w.re| = |z.re| →
        ‖V lam a L w‖ ≤ C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re| := by
      intro w hw1 hw2
      refine (hC L hL w hw1).trans ?_
      rw [hw2, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hphi1 hC0
    have hzre : z.re = ((rho : ℂ)).im := Cvs.Finite.ZeroSideGramMatrix.zPoint_re rho
    calc |(Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) z).re|
        ≤ ‖Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) z‖ := Complex.abs_re_le_norm _
      _ = ‖V lam a L z‖ * ‖V lam a L (-z)‖ := by rw [Cvs.WeilForm.GaussianTestEnvelope.sqTransform_testL, norm_mul]
      _ ≤ (C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re|) * (C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re|) :=
          mul_le_mul (hb z hz1 rfl) (hb (-z) hz2 hnegre) (norm_nonneg _) (by positivity)
      _ = C ^ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2 := by rw [hzre]; ring

/-- The zero side of `gaussAmp²` is `WeightedZeroSide`'s weighted Gaussian zero side. -/
theorem kernelZeroSide_gaussAmp_sq (lam a : ℝ) :
    kernelZeroSide (fun w => Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a w ^ 2) lam a
      = Cvs.Zeta.ExplicitFormula.WeightedZeroSide.weilZeroSideWeighted Cvs.Criterion.divisorWeight lam a := by
  unfold kernelZeroSide
  rw [Cvs.Zeta.ExplicitFormula.WeightedZeroSide.weilZeroSideWeighted_eq]
  refine tsum_congr fun rho => ?_
  refine congrArg ((Cvs.Criterion.divisorWeight rho : ℝ) * ·) ?_
  rw [Cvs.Zeta.ExplicitFormula.WeightedZeroSide.summand, Cvs.Zeta.GaussKernel.AdmissibleKernel.weilSummand_gaussAmp lam a (rho : ℂ), zPoint]
  have hz : -Complex.I * ((rho : ℂ) - 1 / 2)
      = (((rho : ℂ)).im : ℂ) - ((((rho : ℂ)).re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  beta_reduce
  rw [hz]

/-- **Each zero side of `testL` at `L = log x` is a value of `Q`**, so it is nonnegative when `Q`
is nonnegative on the form domain. -/
theorem zeroSide_testL_nonneg {x : ℕ} (hx : 2 ≤ x)
    (hpos : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q _ x (Nat.clog 2 x) φ)
    {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    0 ≤ kernelZeroSide
      (Cvs.Detection.sqTransform (Real.log x) (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a (Real.log x)))) lam a := by
  obtain ⟨hL, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx
  set L := Real.log x with hLdef
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := Cvs.WeilForm.CentredGaussianTest.testL_admissible hlam a hL
  rw [Cvs.WeilForm.PositivityOfRH.kernelZeroSide_eq_weilForm_of_complete hL (Cvs.WeilForm.CentredGaussianTest.continuous_testL lam a L)
    (Cvs.WeilForm.CentredGaussianTest.testL_zero lam a L) (Cvs.WeilForm.CentredGaussianTest.testL_self lam a L) hC0 hC2 hplain hquad lam a hP hR]
  set F := (Set.Icc (0:ℝ) L).indicator (testL lam a L) with hFdef
  have hFc := Cvs.WeilForm.CentredGaussianTest.continuous_indicator_testL lam a hL
  have hfF : (Set.Ioc (0:ℝ) L).indicator (testL lam a L) = F := by
    funext s
    by_cases h1 : s ∈ Set.Ioc (0:ℝ) L
    · rw [indicator_of_mem h1, hFdef, indicator_of_mem (Ioc_subset_Icc_self h1)]
    · rw [indicator_of_notMem h1, hFdef]
      by_cases h2 : s ∈ Set.Icc (0:ℝ) L
      · have hs0 : s = 0 := by
          by_contra hne
          exact h1 ⟨lt_of_le_of_ne h2.1 (Ne.symm hne), h2.2⟩
        rw [indicator_of_mem h2, hs0, Cvs.WeilForm.CentredGaussianTest.testL_zero]
      · rw [indicator_of_notMem h2]
  rw [hfF]
  have hcs : HasCompactSupport F :=
    HasCompactSupport.intro isCompact_Icc fun s hs => indicator_of_notMem hs _
  have h2 : MemLp F 2 volume := hFc.memLp_of_hasCompactSupport hcs
  have hsF : ∀ᵐ s ∂volume, s ∉ Set.Ioc (0:ℝ) L → F s = 0 := by
    refine ae_of_all _ fun s hs => ?_
    rw [← hfF]; exact indicator_of_notMem hs _
  obtain ⟨K, hK⟩ := Cvs.WeilForm.CentredGaussianTest.lipschitz_indicator_testL hlam a hL
  have hmem : Cvs.Approximant.SpineSubspace.ofWin L h2 ∈ Cvs.WeilForm.FormDomain.formDomain hL.le :=
    Cvs.WeilForm.LipschitzTentBasis.lipschitz_mem_formDomain hL.le hFc hK (fun s hs => indicator_of_notMem hs _)
      (Cvs.Approximant.SpineSubspace.ofWin L h2) (Cvs.Approximant.SpineSubspace.rep_ofWin_ae h2 hsF)
  have hQ := hpos ⟨Cvs.Approximant.SpineSubspace.ofWin L h2, hmem⟩
  have hval : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) ⟨Cvs.Approximant.SpineSubspace.ofWin L h2, hmem⟩
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) F := Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (Cvs.Approximant.SpineSubspace.coe_ofWin_ae h2 hsF)
  rw [hval] at hQ
  exact hQ

/-- **Weil's criterion for windows**: `0 ≤ Q` on the form domain at `L = log x`, `P = x`,
`R = ⌈log₂ x⌉`, for every `x ≥ x₀`, gives RH. -/
theorem rh_of_windowPos (x₀ : ℕ)
    (h : ∀ x : ℕ, x₀ ≤ x → ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q _ x (Nat.clog 2 x) φ) : RiemannHypothesis := by
  apply Cvs.Zeta.GaussKernel.AdmissibleKernel.riemannHypothesis_iff.mp
  apply Cvs.Criterion.riemannHypothesis_of_weightedPositivity
  intro lam a hlam
  rw [← kernelZeroSide_gaussAmp_sq]
  have hlim := (tendsto_zeroSide_testL hlam a).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop (max x₀ 2)] with x hx
  exact zeroSide_testL_nonneg (le_of_max_le_right hx) (h x (le_of_max_le_left hx)) hlam a

/-- **RH is `0 ≤ Q` on the form domain at `L = log x`, `P = x`, `R = ⌈log₂ x⌉`, for every
`x ≥ x₀`**, for any `x₀ ≥ 2`. -/
theorem rh_iff_windowPos (x₀ : ℕ) (hx₀ : 2 ≤ x₀) :
    RiemannHypothesis ↔ ∀ x : ℕ, x₀ ≤ x → ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q _ x (Nat.clog 2 x) φ := by
  refine ⟨fun hRH x hx => ?_, rh_of_windowPos x₀⟩
  obtain ⟨hL, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x (hx₀.trans hx)
  exact Cvs.WeilForm.PositivityOfRH.Q_nonneg_of_RH hRH hL hP hR

end Cvs.WeilForm.WindowWeilCriterion
