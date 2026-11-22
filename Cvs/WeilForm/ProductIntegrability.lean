import Mathlib
import Cvs.WeilForm.Archimedean.ArchTrigonometricData
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The product-space integrability is not an extra hypothesis

    Integrable (fun (u, t) => ρ(u)·(1 − cos(tu/2))·W t)  on  Ioi 0 ×ˢ ℝ

follows from `W` integrable against the symbol's increment, because the sections in `u` are
`Cvs.WeilForm.Archimedean.ArchTrigonometricData`'s Lévy integrand and their integrals are exactly that product.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Function
open scoped FourierTransform

namespace Cvs.WeilForm.ProductIntegrability

open Cvs.WeilForm.Archimedean.LevyDensity Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-- **`hprod` follows from `hWA`.**  Each section in `u` is a multiple of the Lévy
integrand, and its integral is the symbol's increment. -/
theorem integrable_prod_of_arch {W : ℝ → ℝ} (hWnn : ∀ t, 0 ≤ W t) (hWm : Measurable W)
    (hWA : Integrable fun t : ℝ => W t * (archSymbol t - archSymbol 0)) :
    Integrable (uncurry fun u t : ℝ => densityU u * ((1 - Real.cos (t / 2 * u)) * W t))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (uncurry fun u t : ℝ => densityU u * ((1 - Real.cos (t / 2 * u)) * W t))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.comp measurable_fst).mul ?_)
    refine (measurable_const.sub ?_).mul (hWm.comp measurable_snd)
    exact Real.measurable_cos.comp
      ((measurable_snd.div_const 2).mul measurable_fst)
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  simp only [uncurry]
  constructor
  · refine Filter.Eventually.of_forall fun t => ?_
    have hsec : (fun u : ℝ => densityU u * ((1 - Real.cos (t / 2 * u)) * W t))
        = fun u : ℝ => W t * Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u := by
      funext u
      unfold Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand
      ring
    rw [hsec]
    exact (Cvs.WeilForm.Archimedean.ArchTrigonometricData.integrableOn_levyIntegrand t).const_mul (W t)
  · have hval : (fun t : ℝ =>
        ∫ u in Ioi (0:ℝ), ‖densityU u * ((1 - Real.cos (t / 2 * u)) * W t)‖)
        = fun t : ℝ => W t * (archSymbol t - archSymbol 0) := by
      funext t
      have hnorm : ∀ u : ℝ, u ∈ Ioi (0:ℝ) →
          ‖densityU u * ((1 - Real.cos (t / 2 * u)) * W t)‖
            = W t * Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u := by
        intro u hu
        have hd : 0 ≤ densityU u := (densityU_pos hu).le
        have hc : 0 ≤ 1 - Real.cos (t / 2 * u) := by
          have := Real.cos_le_one (t / 2 * u); linarith
        rw [Real.norm_of_nonneg (mul_nonneg hd (mul_nonneg hc (hWnn t)))]
        unfold Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand
        ring
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm, integral_const_mul,
        Cvs.WeilForm.Archimedean.ArchTrigonometricData.integral_levyIntegrand]
    rw [hval]
    exact hWA

/-- **`hWi` follows from `hFsq`.**  The density is the transform's square modulus rescaled,
and rescaling preserves integrability. -/
theorem integrable_specDensity {f : ℝ → ℝ}
    (hFsq : Integrable fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) :
    Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) := by
  have hR : ((2 * π)⁻¹ : ℝ) ≠ 0 := by
    refine inv_ne_zero (ne_of_gt ?_)
    positivity
  have h := hFsq.comp_mul_left' hR
  have hfun : Cvs.WeilForm.SelfConvolutionCosine.specDensity f
      = fun t : ℝ => (2 * π)⁻¹ * ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ((2 * π)⁻¹ * t)‖ ^ 2 := by
    funext t
    unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
    rw [div_eq_inv_mul, div_eq_inv_mul]
  rw [hfun]
  exact h.const_mul _

end Cvs.WeilForm.ProductIntegrability
