import Mathlib
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WindowSpectralDensityBound
import Cvs.Zeta.WeilPositivityStatement

/-!
# The transforms of unit window functions are uniformly bounded

    ‖𝓕 (cf f) ξ‖ ≤ √L      for `f` supported in `(0, L]` of unit energy

Translation to the centred window multiplies the transform by a phase of unit modulus, so
`Cvs.WeilForm.WindowSpectralDensityBound`'s bound there is a bound here.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform RealInnerProductSpace

namespace Cvs.WeilForm.UnitWindowTransformBounded

/-- **Translation moves the transform by a phase.** -/
theorem norm_fourier_translate (f : ℝ → ℂ) (c ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => f (x + c)) ξ‖ = ‖𝓕 f ξ‖ := by
  have h := VectorFourier.fourierIntegral_comp_add_right (E := ℂ) Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) f c
  have hfun : (fun x : ℝ => f (x + c)) = f ∘ fun v : ℝ => v + c := rfl
  rw [hfun]
  have hval : 𝓕 (f ∘ fun v : ℝ => v + c) ξ
      = (Real.fourierChar ((innerₗ ℝ) c ξ) : ℂ) • 𝓕 f ξ := by
    exact congrFun h ξ
  rw [hval, norm_smul]
  simp [Circle.norm_coe]

/-- The self-convolution at zero is the energy. -/
theorem selfConvolution_zero (f : ℝ → ℝ) : selfConvolution f 0 = ∫ s : ℝ, f s ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [add_zero]
  ring

/-- **The transforms are uniformly bounded on the window.** -/
theorem norm_fourier_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    (hnorm : (∫ x : ℝ, f x ^ 2) = 1) (ξ : ℝ) :
    ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ≤ Real.sqrt L := by
  set g : ℝ → ℝ := fun x => f (x + L / 2) with hg
  have hgsupp : ∀ x, x ∉ Set.Icc (-(L / 2)) (L / 2) → g x = 0 :=
    Cvs.WeilForm.CentredWindowTranslate.support_translate hsupp
  have hgmem : MemLp g 2 (volume : Measure ℝ) := Cvs.WeilForm.CentredWindowTranslate.memLp_translate _ hf
  have hgsq : (∫ x : ℝ, g x ^ 2) = 1 := by
    rw [hg, Cvs.WeilForm.CentredWindowTranslate.integral_sq_translate f (L / 2)]
    exact hnorm
  have hfint : Integrable f (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf hsupp
  have hgint : Integrable g (volume : Measure ℝ) := hfint.comp_add_right (L / 2)
  have hgsqi : Integrable (fun s : ℝ => g s ^ 2) (volume : Measure ℝ) := hgmem.integrable_sq
  have hb := Cvs.WeilForm.WindowSpectralDensityBound.norm_fourier_sq_le hL hgsupp hgint hgsqi ξ
  rw [selfConvolution_zero g, hgsq, mul_one] at hb
  -- transfer to `f` by the phase
  have hcf : (Cvs.WeilForm.SelfConvolutionTransform.cf g)
      = fun x : ℝ => (Cvs.WeilForm.SelfConvolutionTransform.cf f) (x + L / 2) := rfl
  rw [hcf, norm_fourier_translate] at hb
  calc ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖
      = Real.sqrt (‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hb

end Cvs.WeilForm.UnitWindowTransformBounded
