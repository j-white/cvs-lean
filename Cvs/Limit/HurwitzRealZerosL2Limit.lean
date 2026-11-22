import Mathlib
import Cvs.Limit.TransformStripLipschitz
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.Hurwitz
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero

/-!
# The Hurwitz step: real zeros survive an L² limit

    real-zero transforms, converging in `L²`  ⟹  the limit's transform has only real zeros

`Cvs.Limit.TransformStripLipschitz` turns the `L²` convergence into local uniformity, `Cvs.WeilForm.TransformNowhereLocallyZero` rules out the identically
zero limit, and `Cvs.Upstream.Hurwitz` does the rest.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Complex

namespace Cvs.Limit.HurwitzRealZerosL2Limit

/-- The transforms converge locally uniformly. -/
theorem tendstoLocallyUniformly_transforms {L : ℝ} (hL : 0 ≤ L) {ξ : ℝ → ℝ} {Ξ : ℕ → ℝ → ℝ}
    (hξ : MemLp ξ 2 (volume : Measure ℝ)) (hΞ : ∀ k, MemLp (Ξ k) 2 (volume : Measure ℝ))
    (hξs : ∀ s ∉ Set.Ioc (0:ℝ) L, ξ s = 0)
    (hΞs : ∀ k, ∀ s ∉ Set.Ioc (0:ℝ) L, Ξ k s = 0)
    (hconv : Tendsto (fun k => ∫ x : ℝ, (Ξ k x - ξ x) ^ 2) atTop (nhds 0)) :
    TendstoLocallyUniformlyOn
      (fun k => FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Ξ k)))
      (FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ)) atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  -- the imaginary part is bounded on a compact set
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ K, |z.im| ≤ M := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨R, fun z hz => ?_⟩
    have := hR hz
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at this
    exact le_trans (Complex.abs_im_le_norm z) this
  set C : ℝ := Real.sqrt (Real.exp (2 * L * M) * L) with hC
  have hCnn : 0 ≤ C := Real.sqrt_nonneg _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- the L² distances go to zero, so the sup over K does
  have hs : Tendsto (fun k => Real.sqrt (∫ x : ℝ, (Ξ k x - ξ x) ^ 2)) atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa [Real.sqrt_zero, Function.comp_def] using this
  have hlt : ∀ᶠ k in atTop, Real.sqrt (∫ x : ℝ, (Ξ k x - ξ x) ^ 2) * (C + 1) < ε := by
    refine (hs.mul_const (C + 1)).eventually_lt_const ?_
    simpa using hε
  filter_upwards [hlt] with k hk z hz
  have hb0 := Cvs.Limit.TransformStripLipschitz.norm_fourierLaplace_sub_le hL hξ (hΞ k) hξs (hΞs k) z
  have hsymm : (∫ x : ℝ, (ξ x - Ξ k x) ^ 2) = ∫ x : ℝ, (Ξ k x - ξ x) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsymm] at hb0
  have hb := hb0
  rw [Complex.dist_eq]
  refine lt_of_le_of_lt (le_trans hb ?_) hk
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hmono : Real.exp (2 * L * |z.im|) * L ≤ Real.exp (2 * L * M) * L := by
    have h1 : Real.exp (2 * L * |z.im|) ≤ Real.exp (2 * L * M) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hM z hz, abs_nonneg z.im, hL]
    nlinarith [h1, hL, (Real.exp_pos (2 * L * |z.im|)).le]
  calc Real.sqrt (Real.exp (2 * L * |z.im|) * L) ≤ C := Real.sqrt_le_sqrt hmono
    _ ≤ C + 1 := by linarith

/-- **Real zeros survive an `L²` limit.** -/
theorem zeros_real_of_approx {L : ℝ} (hL : 0 < L) {ξ : ℝ → ℝ} {Ξ : ℕ → ℝ → ℝ}
    (hξ : MemLp ξ 2 (volume : Measure ℝ)) (hξs : ∀ s ∉ Set.Ioc (0:ℝ) L, ξ s = 0)
    (hξn : (∫ x : ℝ, ξ x ^ 2) = 1)
    (hΞ : ∀ k, MemLp (Ξ k) 2 (volume : Measure ℝ))
    (hΞs : ∀ k, ∀ s ∉ Set.Ioc (0:ℝ) L, Ξ k s = 0)
    (hT2 : ∀ k, ∀ z : ℂ,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Ξ k)) z = 0 → z.im = 0)
    (hconv : Tendsto (fun k => ∫ x : ℝ, (Ξ k x - ξ x) ^ 2) atTop (nhds 0)) :
    ∀ z : ℂ, FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) z = 0 → z.im = 0 := by
  intro z₀ hz
  refine Cvs.Upstream.Hurwitz.im_eq_zero_of_tendstoLocallyUniformlyOn isOpen_univ
    (Set.mem_univ z₀) (fun k => ?_) (fun k z _ => hT2 k z)
    (tendstoLocallyUniformly_transforms hL.le hξ hΞ hξs hΞs hconv) ?_ hz
  · have hint : Integrable (Ξ k) (volume : Measure ℝ) :=
      Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL.le (hΞ k) (hΞs k)
    exact (FourierLaplace.differentiable_fourierLaplace_of_integrable hint.ofReal
      (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf (hΞs k))).differentiableOn
  · exact Cvs.WeilForm.TransformNowhereLocallyZero.not_eventually_zero hL.le hξ hξs hξn z₀

end Cvs.Limit.HurwitzRealZerosL2Limit
