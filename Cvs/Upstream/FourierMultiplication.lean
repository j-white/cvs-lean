import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The multiplication formula on the line

    ∫ 𝓕 f ξ · g ξ  =  ∫ f x · 𝓕 g x

for integrable `f g : ℝ → ℂ`.  Mathlib has this for a general bilinear pairing; on `ℝ` the
pairing is its own flip, so the two transforms are the same one.  Mathlib only.
-/

noncomputable section

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

namespace Cvs.Upstream.FourierMultiplication

/-- **The real pairing is its own flip.** -/
theorem innerₗ_real_flip : (innerₗ ℝ).flip = innerₗ ℝ :=
  LinearMap.ext fun a => LinearMap.ext fun b => by
    simp only [LinearMap.flip_apply]
    exact real_inner_comm a b

/-- **The multiplication formula.**  The transform may be moved from one factor to the
other. -/
theorem integral_fourier_mul (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ : ℝ, 𝓕 f ξ * g ξ) = ∫ x : ℝ, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    Real.continuous_fourierChar (by fun_prop) hf hg
  rw [innerₗ_real_flip] at h
  exact h

end Cvs.Upstream.FourierMultiplication
