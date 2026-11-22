import Mathlib
import Cvs.Finite.AveragedApproximant
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTransformEnvelopes
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.ExponentialSumTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LogEnvelopeSquareSummable
import Cvs.Zeta.ZeroSideMoments

/-!
# The zero side of every even mode sum: the CvS matrix is a zero-side Gram matrix
Along `Cvs.Finite.AveragedApproximant`'s extension `f_N = f − (s/N)·avg_N` the transform is `W − (s/N)·T_N`; on the
zeros the difference is dominated by `Cvs.Finite.ModeTransformEnvelopes`'s envelopes and `Cvs.Zeta.LogEnvelopeSquareSummable`'s summable square and
vanishes pointwise, so the zero sides converge. Each `f_N` lies on the zero side by `Cvs.Finite.EvenSectorZeroSide`
and its window form converges by `Cvs.Finite.AveragedApproximant`: `kernelZeroSide (sqTransform f) = weilForm (modeSum)`
for every even mode sum, so `L·xiᵀ·ddMatrix·xi` is the zero side of the discrete route.
-/

noncomputable section

open Real Filter Topology Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.ZeroSideGramMatrix
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- **The transform of the extension** is `W − (s/N)·T_N`. -/
theorem windowTransform_E (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (M₀ N : ℕ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L
        (Cvs.Finite.AveragedApproximant.modeE mode M₀ N) (Cvs.Finite.AveragedApproximant.xiE xi N))) ξ
      = Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) ξ
        - (((∑ i, xi i) / N : ℝ) : ℂ)
          * Cvs.Detection.windowTransform L (cf (Cvs.Finite.ModeTransformEnvelopes.avg L M₀ N)) ξ := by
  have hfun : cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (Cvs.Finite.AveragedApproximant.modeE mode M₀ N)
      (Cvs.Finite.AveragedApproximant.xiE xi N))
      = fun y => cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi) y
        + ((-((∑ i, xi i) / N) : ℝ) : ℂ) * cf (Cvs.Finite.ModeTransformEnvelopes.avg L M₀ N) y := by
    funext y
    simp only [cf]
    rw [Cvs.Finite.AveragedApproximant.cosPoly_E]
    unfold Cvs.Finite.ModeTransformEnvelopes.avg
    push_cast
    ring
  have hc1 : Continuous (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) :=
    Complex.continuous_ofReal.comp (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L mode xi)
  have hc2 : Continuous (fun y => ((-((∑ i, xi i) / N) : ℝ) : ℂ)
      * cf (Cvs.Finite.ModeTransformEnvelopes.avg L M₀ N) y) := by
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    unfold Cvs.Finite.ModeTransformEnvelopes.avg; fun_prop
  rw [hfun, Cvs.Detection.windowTransform_add L hc1 hc2 ξ,
    Cvs.Detection.windowTransform_const_mul]
  push_cast
  ring

/-- The strip data of `zPoint`. -/
theorem zPoint_re (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    (Cvs.ZeroCounting.zPoint rho).re = ((rho : ℂ)).im := by
  unfold Cvs.ZeroCounting.zPoint; simp

theorem zPoint_im_le (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    |(Cvs.ZeroCounting.zPoint rho).im| ≤ 3 / 2 := by
  have h := Cvs.Zeta.GaussKernel.AdmissibleKernel.abs_re_sub_half_le rho
  unfold Cvs.ZeroCounting.zPoint
  simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.sub_re, Complex.one_re,
    Complex.neg_im, Complex.I_im, Complex.sub_im, Complex.one_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im]
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

theorem neg_zPoint_im_le (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    |(-Cvs.ZeroCounting.zPoint rho).im| ≤ 3 / 2 := by
  rw [Complex.neg_im, abs_neg]; exact zPoint_im_le rho

/-- **The zero sides converge along the extension.** -/
theorem tendsto_zeroSide_E {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) (M₀ : ℕ)
    (lam a : ℝ) :
    Tendsto (fun N : ℕ => Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L
        (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (Cvs.Finite.AveragedApproximant.modeE mode M₀ N)
          (Cvs.Finite.AveragedApproximant.xiE xi N)))) lam a) atTop
      (𝓝 (Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L
        (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi))) lam a)) := by
  obtain ⟨CW, hCW0, hCW⟩ := Cvs.Finite.ModeTransformEnvelopes.exists_cosPoly_bound hL mode xi
  obtain ⟨CE, hCE0, hCE⟩ := Cvs.Finite.ModeTransformEnvelopes.exists_avg_envelope hL M₀
  set s : ℝ := ∑ i, xi i with hs
  set W : ℂ → ℂ := Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi))
    with hW
  set T : ℕ → ℂ → ℂ := fun N => Cvs.Detection.windowTransform L
    (cf (Cvs.Finite.ModeTransformEnvelopes.avg L M₀ N)) with hT
  -- the envelope of both factors at a zero
  have hfac : ∀ N : ℕ, 1 ≤ N → ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖W ξ - ((s / N : ℝ) : ℂ) * T N ξ‖
        ≤ (CW + |s| * CE) * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := by
    intro N hN ξ hξ
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    have hre0 : 0 ≤ |ξ.re| := abs_nonneg _
    have hphi1 := Cvs.Zeta.LogEnvelopeSquareSummable.one_div_le_phi hre0
    have h1 : ‖W ξ‖ ≤ CW * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := by
      refine (hCW ξ hξ).trans ?_
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hphi1 hCW0
    have h2 : ‖((s / N : ℝ) : ℂ) * T N ξ‖ ≤ |s| * CE * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hNpos]
      have := hCE N hN ξ hξ
      calc |s| / N * ‖T N ξ‖ ≤ |s| / N * (N * (CE * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re|)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = |s| * CE * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := by field_simp
    calc ‖W ξ - ((s / N : ℝ) : ℂ) * T N ξ‖ ≤ ‖W ξ‖ + ‖((s / N : ℝ) : ℂ) * T N ξ‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hfac0 : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖W ξ‖ ≤ (CW + |s| * CE) * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := by
    intro ξ hξ
    have hre0 : 0 ≤ |ξ.re| := abs_nonneg _
    have hphi := Cvs.Zeta.LogEnvelopeSquareSummable.phi_nonneg hre0
    have hphi1 := Cvs.Zeta.LogEnvelopeSquareSummable.one_div_le_phi hre0
    refine (hCW ξ hξ).trans ?_
    rw [div_eq_mul_one_div]
    calc CW * (1 / (1 + |ξ.re|)) ≤ CW * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| :=
          mul_le_mul_of_nonneg_left hphi1 hCW0
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (abs_nonneg s) hCE0) hphi]
  unfold Cvs.ZeroCounting.kernelZeroSide
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * ((CW + |s| * CE) ^ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2))
    ?_ ?_ ?_
  · -- summability of the bound
    have h := Cvs.Zeta.LogEnvelopeSquareSummable.summable_divisorWeight_phi_sq.mul_left ((CW + |s| * CE) ^ 2)
    refine h.congr fun rho => ?_
    ring
  · -- pointwise convergence
    intro rho
    set z := Cvs.ZeroCounting.zPoint rho with hz
    have hz1 := zPoint_im_le rho
    have hz2 := neg_zPoint_im_le rho
    have hlim1 : Tendsto (fun N : ℕ => W z - ((s / N : ℝ) : ℂ) * T N z) atTop (𝓝 (W z)) := by
      have := (Cvs.Finite.ModeTransformEnvelopes.tendsto_avg_div hL M₀ s hz1).const_sub (W z)
      simpa using this
    have hlim2 : Tendsto (fun N : ℕ => W (-z) - ((s / N : ℝ) : ℂ) * T N (-z)) atTop
        (𝓝 (W (-z))) := by
      have := (Cvs.Finite.ModeTransformEnvelopes.tendsto_avg_div hL M₀ s hz2).const_sub (W (-z))
      simpa using this
    have hprod := hlim1.mul hlim2
    have hre := (Complex.continuous_re.tendsto _).comp hprod
    have hfin := hre.const_mul (Cvs.Criterion.divisorWeight rho : ℝ)
    refine hfin.congr fun N => ?_
    simp only [Function.comp_apply, Cvs.Detection.sqTransform, windowTransform_E, hs, hW, hT]
  · -- the domination, from `N ≥ 1` on
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    intro rho
    set z := Cvs.ZeroCounting.zPoint rho with hz
    have hz1 := zPoint_im_le rho
    have hz2 := neg_zPoint_im_le rho
    have hw : (0:ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
    have hre0 : 0 ≤ |z.re| := abs_nonneg _
    have hphi := Cvs.Zeta.LogEnvelopeSquareSummable.phi_nonneg hre0
    rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ hw
    have hval : Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L
        (Cvs.Finite.AveragedApproximant.modeE mode M₀ N) (Cvs.Finite.AveragedApproximant.xiE xi N))) z
        = (W z - ((s / N : ℝ) : ℂ) * T N z) * (W (-z) - ((s / N : ℝ) : ℂ) * T N (-z)) := by
      simp only [Cvs.Detection.sqTransform, windowTransform_E, hs, hW, hT]
    have hnegre : |(-z).re| = |z.re| := by rw [Complex.neg_re, abs_neg]
    have hb1 := hfac N hN z hz1
    have hb2 := hfac N hN (-z) hz2
    rw [hnegre] at hb2
    have hzre : z.re = ((rho : ℂ)).im := zPoint_re rho
    calc |(Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L
          (Cvs.Finite.AveragedApproximant.modeE mode M₀ N) (Cvs.Finite.AveragedApproximant.xiE xi N))) z).re|
        ≤ ‖Cvs.Detection.sqTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L
          (Cvs.Finite.AveragedApproximant.modeE mode M₀ N) (Cvs.Finite.AveragedApproximant.xiE xi N))) z‖ :=
          Complex.abs_re_le_norm _
      _ = ‖W z - ((s / N : ℝ) : ℂ) * T N z‖ * ‖W (-z) - ((s / N : ℝ) : ℂ) * T N (-z)‖ := by
          rw [hval, norm_mul]
      _ ≤ ((CW + |s| * CE) * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re|)
          * ((CW + |s| * CE) * Cvs.Zeta.LogEnvelopeSquareSummable.phi |z.re|) :=
          mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
      _ = (CW + |s| * CE) ^ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((rho : ℂ)).im| ^ 2 := by
          rw [hzre]; ring

/-- **The zero side of every even mode sum is its window Weil form.** -/
theorem zeroSide_modeSum {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) {neg : ι → ι}
    (hinv : Function.Involutive neg) (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ}
    (hxieven : ∀ i, xi (neg i) = xi i) (lam a : ℝ) :
    Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L
        (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi))) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
          (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) := by
  classical
  set M₀ : ℕ := ∑ i, (mode i).natAbs with hM₀
  have hM : ∀ i, |((mode i : ℤ) : ℝ)| ≤ M₀ := by
    intro i
    rw [← Int.cast_abs, ← Nat.cast_natAbs, hM₀]
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le ((mode j).natAbs))
      (Finset.mem_univ i)
  have hZ := tendsto_zeroSide_E hL mode xi M₀ lam a
  have hWf := Cvs.Finite.AveragedApproximant.tendsto_weilForm_E hL ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
    mode hinv hmode hxieven M₀ hM
  have heq : ∀ᶠ N : ℕ in atTop,
      Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L
        (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (Cvs.Finite.AveragedApproximant.modeE mode M₀ N)
          (Cvs.Finite.AveragedApproximant.xiE xi N)))) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
          (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.AveragedApproximant.modeE mode M₀ N)
            (Cvs.Finite.AveragedApproximant.xiE xi N)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact Cvs.Finite.EvenSectorZeroSide.zeroSide_modeSum_of_sum_zero hL _
      (Cvs.Finite.AveragedApproximant.sum_xiE xi hN) lam a
  exact tendsto_nhds_unique hZ (hWf.congr' (heq.mono fun N h => h.symm))

/-- **The CvS quadratic form is the zero side**, for injective modes. -/
theorem zeroSide_eq_ddMatrix [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i)
    (lam a : ℝ) :
    Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L
        (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi))) lam a
      = L * (xi ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix
          (fun k => Cvs.Finite.PairFormDividedDifference.aval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (fun k => Cvs.Finite.PairFormDividedDifference.bval ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode k))
          (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode) *ᵥ xi)) := by
  rw [zeroSide_modeSum hL mode hinv hmode hxieven lam a,
    Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix hL _ _ hinj hinv hmode hxieven]

end Cvs.Finite.ZeroSideGramMatrix
