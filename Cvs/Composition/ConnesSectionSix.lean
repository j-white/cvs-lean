import Mathlib
import Cvs.Approximant.FactSixFour
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Composition.SpineStepsAB
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.StepA.EvenPlaneGapAtTwo
import Cvs.StepA.StepAAtTwoAssembled
import Cvs.StepA.StepAPredicate
import Cvs.TheoremSixOne.MinimiserTransformRealZeros
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.Hurwitz
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.RiemannXi

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes' §6: Theorem 6.1, Step A, Fact 6.4 and Step B give the Riemann Hypothesis

Step A at every scale makes each recentred minimiser transform `θ̂_x` zero-free off the real axis
(Cvs.TheoremSixOne.MinimiserTransformRealZeros). Step B, rescaled `θ̂_x` uniformly close to the rescaled `k̂_λ` on closed substrips, with
Fact 6.4 (Cvs.Approximant.FactSixFour), makes `θ̂_x` converge to `Ξ` there, and Hurwitz on the strip gives RH.
-/

noncomputable section

open Real Set Filter MeasureTheory Topology

namespace Cvs.Composition.ConnesSectionSix
open Cvs.ZeroCounting

open Cvs.Limit.ZeroFreeApproximantsRH (Xi)

/-- The critical strip `|Im z| < 1/2` of `z = −i(s − 1/2)`, off the real axis. -/
def stripNonReal : Set ℂ := {z : ℂ | z.im ≠ 0 ∧ |z.im| < 1 / 2}

theorem isOpen_stripNonReal : IsOpen stripNonReal := by
  have h1 : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_compl_singleton.preimage Complex.continuous_im
  have h2 : IsOpen {z : ℂ | |z.im| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

/-- **`Ξ` zero-free on the strip off the real axis gives RH.** -/
theorem riemannHypothesis_of_Xi_ne_zero (hXi : ∀ z ∈ stripNonReal, Xi z ≠ 0) :
    RiemannHypothesis := by
  intro s hs hnt hs1
  by_cases hstrip : 0 < s.re ∧ s.re < 1
  · have hξ : Cvs.Zeta.riemannXi s = 0 :=
      (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta hstrip.1 hs1).mpr hs
    have hXz : Xi (Cvs.Limit.ZeroFreeApproximantsRH.zOf s) = 0 := by
      unfold Xi; rw [Cvs.Limit.ZeroFreeApproximantsRH.half_add_I_mul_zOf]; exact hξ
    by_contra hne
    have him : (Cvs.Limit.ZeroFreeApproximantsRH.zOf s).im ≠ 0 := by
      rw [Cvs.Limit.ZeroFreeApproximantsRH.zOf_im]; intro h; apply hne; linarith
    have hab : |(Cvs.Limit.ZeroFreeApproximantsRH.zOf s).im| < 1 / 2 := by
      rw [Cvs.Limit.ZeroFreeApproximantsRH.zOf_im, abs_lt]; constructor <;> linarith [hstrip.1, hstrip.2]
    exact hXi _ ⟨him, hab⟩ hXz
  · exact absurd (Cvs.Limit.ZeroFreeApproximantsRH.trivial_of_zero_off_strip hs hstrip hs1) hnt

/-- **Uniform convergence on every closed substrip `|Im z| ≤ a < 1/2` is locally uniform on the
strip off the real axis.** -/
theorem tendstoLocallyUniformlyOn_of_substrips {ι : Type*} {p : Filter ι} {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} (h : ∀ a < 1 / 2, TendstoUniformlyOn F f p {z : ℂ | |z.im| ≤ a}) :
    TendstoLocallyUniformlyOn F f p stripNonReal := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz => ?_
  set a := (|z.im| + 1 / 2) / 2 with ha
  have hza : |z.im| < a := by rw [ha]; linarith [hz.2]
  have ha2 : a < 1 / 2 := by rw [ha]; linarith [hz.2]
  refine ⟨{w : ℂ | |w.im| ≤ a}, ?_, h a ha2⟩
  have hopen : IsOpen {w : ℂ | |w.im| < a} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (hopen.mem_nhds hza) ?_)
  intro w hw
  exact le_of_lt (show |w.im| < a from hw)

/-- The Fourier transform of a scale's recentred minimiser, Connes' `θ̂_x`. -/
def thetaHat {L : ℝ} (hL : 0 < L) (η : Cvs.WeilForm.FormDomain.formDomain hL.le) : ℂ → ℂ :=
  FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.TheoremSixOne.MinimiserTransformRealZeros.centred hL η))

/-- **`θ̂_x` is entire** under Step A. -/
theorem differentiable_thetaHat {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA hL P R lam η) : Differentiable ℂ (thetaHat hL η) := by
  have e : thetaHat hL η = fun z => Complex.exp (-(Complex.I * z * ((L / 2 : ℝ) : ℂ)))
      * Cvs.Composition.SpineStepsAB.transform hL η z := by
    funext z; exact Cvs.TheoremSixOne.MinimiserTransformRealZeros.fourierLaplace_centred hL η z
  rw [e]
  exact (Complex.differentiable_exp.comp (by fun_prop)).mul
    (Cvs.Composition.SpineStepsAB.differentiable_transform hL P R h.stepA)

/-- **Connes' Step A at the base scale `x = 2`, with Theorem 6.1**: the truncated Weil form at
`L = log 2` has a simple even bottom, and its recentred minimiser's transform has only real zeros. -/
theorem exists_connesStepA_x2 :
    ∃ η, Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA Cvs.StepA.StepAAtTwoAssembled.log_two_pos 2 1
        (Cvs.WeilForm.BottomAttained.lam Cvs.StepA.StepAAtTwoAssembled.log_two_pos 2 1) η ∧
      ∀ z : ℂ, thetaHat Cvs.StepA.StepAAtTwoAssembled.log_two_pos η z = 0 → z.im = 0 := by
  obtain ⟨η, h⟩ := Cvs.StepA.EvenPlaneGapAtTwo.stepA_x2_unconditional
  have hC : Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA Cvs.StepA.StepAAtTwoAssembled.log_two_pos 2 1
      (Cvs.WeilForm.BottomAttained.lam Cvs.StepA.StepAAtTwoAssembled.log_two_pos 2 1) η :=
    ⟨h.bottom, h.attains, h.nonzero, h.simple, h.even⟩
  exact ⟨η, hC, fun z hz =>
    Cvs.TheoremSixOne.MinimiserTransformRealZeros.im_eq_zero_of_centred_eq_zero Cvs.StepA.StepAAtTwoAssembled.log_two_pos 2 1 hC hz⟩

/-- **Connes' §6 with Step B as convergence**: Step A at every scale of a sequence, and nonzero
rescalings of `θ̂_x` converging to `Ξ` uniformly on every closed substrip `|Im z| ≤ a < 1/2`,
give RH. -/
theorem riemannHypothesis_of_connesStepA_of_tendsto {L : ℕ → ℝ} (hL : ∀ n, 0 < L n)
    (P R : ℕ → ℕ) (lam : ℕ → ℝ) (η : ∀ n, Cvs.WeilForm.FormDomain.formDomain (hL n).le)
    (hA : ∀ n, Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA (hL n) (P n) (R n) (lam n) (η n))
    (c : ℕ → ℂ) (hc : ∀ n, c n ≠ 0)
    (hconv : ∀ a < 1 / 2, TendstoUniformlyOn (fun n z => c n * thetaHat (hL n) (η n) z) Xi atTop
      {z : ℂ | |z.im| ≤ a}) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_Xi_ne_zero fun z hz => ?_
  refine Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn isOpen_stripNonReal hz
    (fun n => ((differentiable_const (c n)).mul
      (differentiable_thetaHat (hL n) (P n) (R n) (hA n))).differentiableOn)
    (fun n w hw => mul_ne_zero (hc n) fun h0 =>
      hw.1 (Cvs.TheoremSixOne.MinimiserTransformRealZeros.im_eq_zero_of_centred_eq_zero (hL n) (P n) (R n) (hA n) h0))
    (tendstoLocallyUniformlyOn_of_substrips hconv) (Cvs.Limit.ZeroFreeApproximantsRH.not_eventually_zero z)

/-- **Connes' Step B** along scales `x_n`: some nonzero rescaling of `θ̂_{x_n}` is uniformly close,
on every closed substrip `|Im z| ≤ a < 1/2`, to `k̂_λ` under Fact 6.4's rescaling `overlap/16`. -/
def ConnesStepB (x : ℕ → ℝ) (hL : ∀ n, 0 < Real.log (x n))
    (η : ∀ n, Cvs.WeilForm.FormDomain.formDomain (hL n).le) : Prop :=
  ∃ c : ℕ → ℂ, (∀ n, c n ≠ 0) ∧ ∀ a < 1 / 2,
    TendstoUniformlyOn (fun n z => c n * thetaHat (hL n) (η n) z
        - ((Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x n) / 16 : ℝ) : ℂ)
          * Cvs.Approximant.FactSixFour.mellinHat (Cvs.Approximant.FactSixFour.kLambda (x n)) z)
      0 atTop {z : ℂ | |z.im| ≤ a}

/-- **Connes' §6** (arXiv:2602.04022, §6.1–§6.6): along scales `x_n → ∞`, Step A at every scale
(`MinimiserTransformRealZeros`'s Theorem 6.1), Fact 6.4 (Cvs.Approximant.FactSixFour) and Step B give the Riemann Hypothesis. -/
theorem riemannHypothesis_of_connes (x : ℕ → ℝ) (hx : Tendsto x atTop atTop)
    (hL : ∀ n, 0 < Real.log (x n)) (P R : ℕ → ℕ) (lam : ℕ → ℝ)
    (η : ∀ n, Cvs.WeilForm.FormDomain.formDomain (hL n).le)
    (hA : ∀ n, Cvs.TheoremSixOne.MinimiserTransformRealZeros.ConnesStepA (hL n) (P n) (R n) (lam n) (η n))
    (hB : ConnesStepB x hL η) : RiemannHypothesis := by
  obtain ⟨c, hc, hB⟩ := hB
  refine riemannHypothesis_of_connesStepA_of_tendsto hL P R lam η hA c hc fun a ha => ?_
  have hk := Cvs.Approximant.FactSixFour.tendstoUniformlyOn_mellinHat_kLambda ha
  rw [Metric.tendstoUniformlyOn_iff] at hk ⊢
  have hd := Metric.tendstoUniformlyOn_iff.mp (hB a ha)
  intro ε hε
  filter_upwards [hd (ε / 2) (by linarith), hx.eventually (hk (ε / 2) (by linarith))]
    with n hn1 hn2 z hz
  have h1 := hn1 z hz
  have h2 := hn2 z hz
  rw [Pi.zero_apply, dist_zero_left] at h1
  rw [dist_eq_norm] at h2 ⊢
  set K := ((Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x n) / 16 : ℝ) : ℂ)
    * Cvs.Approximant.FactSixFour.mellinHat (Cvs.Approximant.FactSixFour.kLambda (x n)) z
  calc ‖Xi z - c n * thetaHat (hL n) (η n) z‖
      = ‖(Xi z - K) - (c n * thetaHat (hL n) (η n) z - K)‖ := by ring_nf
    _ ≤ ‖Xi z - K‖ + ‖c n * thetaHat (hL n) (η n) z - K‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h2 h1
    _ = ε := by ring

end Cvs.Composition.ConnesSectionSix
