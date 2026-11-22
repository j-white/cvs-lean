import Mathlib
import Cvs.Zeta.FourierShift

/-!
# The convention bridge to Mathlib's Fourier transform
-/

namespace Cvs.Detection

open Complex MeasureTheory FourierTransform
open scoped Real RealInnerProductSpace

/-- **The convention bridge.**  `Cvs.Zeta.fourierReal` and Mathlib's `𝓕` differ by
`2π` in the frequency variable. -/
theorem fourierReal_eq_fourier (h : ℂ → ℂ) (t : ℝ) :
    Cvs.Zeta.fourierReal h t = 𝓕 (fun x : ℝ => h (x : ℂ)) (t / (2 * π)) := by
  rw [Cvs.Zeta.fourierReal, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  have hinner : (⟪x, t / (2 * π)⟫ : ℝ) = x * (t / (2 * π)) := by
    rw [RCLike.inner_apply]
    simp [mul_comm]
  rw [hinner]
  have hpi : (2 : ℝ) * π ≠ 0 := by positivity
  push_cast
  field_simp

end Cvs.Detection
