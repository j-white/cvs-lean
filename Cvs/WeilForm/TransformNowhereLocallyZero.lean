import Mathlib
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.PlancherelTimeLimited
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# A unit window function's transform is nowhere locally zero

    ‖ξ‖ = 1  ⟹  the entire function `fourierLaplace (cf ξ)` vanishes on no neighbourhood

Plancherel supplies the injectivity: a transform vanishing on an open set vanishes everywhere,
and `Cvs.Upstream.PlancherelTimeLimited` reads that back as `∫ ξ² = 0`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace Cvs.WeilForm.TransformNowhereLocallyZero

/-- The two transforms differ by the frequency's scale. -/
theorem fourier_eq_fourierLaplace (g : ℝ → ℂ) (w : ℝ) :
    𝓕 g w = FourierLaplace.fourierLaplace g (-(2 * π) * (w : ℂ)) := by
  rw [Real.fourier_eq, FourierLaplace.fourierLaplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hinner : (inner ℝ v w : ℝ) = v * w := by
    rw [RCLike.inner_apply']
    simp [mul_comm]
  simp only [Circle.smul_def, Real.fourierChar_apply, hinner, smul_eq_mul]
  rw [mul_comm (Complex.exp _) (g v)]
  congr 1
  push_cast
  ring

/-- A window function has compact support. -/
theorem hasCompactSupport_cf {L : ℝ} {ξ : ℝ → ℝ}
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, ξ s = 0) :
    HasCompactSupport (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0:ℝ)) (b := L)) ?_
  intro x hx
  by_contra hmem
  exact hx (by
    rw [Function.mem_support] at hx
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, ne_eq, Complex.ofReal_eq_zero] at hx
    exact absurd (hsupp x (fun hc => hmem ⟨hc.1.le, hc.2⟩)) hx)

/-- **The transform vanishes on no neighbourhood.** -/
theorem not_eventually_zero {L : ℝ} (hL : 0 ≤ L) {ξ : ℝ → ℝ}
    (hξ : MemLp ξ 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, ξ s = 0)
    (hnorm : (∫ x : ℝ, ξ x ^ 2) = 1) (z₀ : ℂ) :
    ¬ (∀ᶠ z in nhds z₀, FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) z = 0) := by
  intro hev
  have hξint : Integrable ξ (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hξ hsupp
  have hcf : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) (volume : Measure ℝ) := hξint.ofReal
  have hsc : HasCompactSupport (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) := hasCompactSupport_cf hsupp
  have hent : Differentiable ℂ
      (FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ)) :=
    FourierLaplace.differentiable_fourierLaplace_of_integrable hcf hsc
  -- an entire function vanishing near a point vanishes everywhere
  have hall : ∀ z : ℂ, FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) z = 0 := by
    intro z
    have hana : AnalyticOnNhd ℂ
        (FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ)) Set.univ :=
      hent.differentiableOn.analyticOnNhd isOpen_univ
    have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_univ) (Set.mem_univ z₀) hev
    exact this (Set.mem_univ z)
  -- so the spectral mass vanishes, contradicting the unit norm
  have hzero : ∀ w : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) w‖ ^ 2 = 0 := by
    intro w
    rw [fourier_eq_fourierLaplace, hall]
    simp
  have hP := Cvs.Upstream.PlancherelTimeLimited.plancherel_of_integrable hξ hξint
  rw [hnorm] at hP
  rw [show (∫ w : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) w‖ ^ 2) = ∫ _w : ℝ, (0:ℝ) from
    integral_congr_ae (Filter.Eventually.of_forall hzero)] at hP
  simp at hP

end Cvs.WeilForm.TransformNowhereLocallyZero
