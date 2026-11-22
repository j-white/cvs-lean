import Mathlib
import Cvs.Finite.ExponentialKernelLocalises

/-!
# The channel kernel's cosine eigenfunction

The half-window moments of `cos (t (u − L/2))` are elementary, their oscillatory parts cancel on
addition, and the two boundary terms carry the single factor `b cos (tL/2) − t sin (tL/2)`.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.WeilForm.ChannelKernelCosineEigen

open Cvs.Finite.ExponentialKernelLocalises intervalIntegral

variable {b t L : ℝ}

/-- The cosine wave centred on the window. -/
def wave (t L : ℝ) (u : ℝ) : ℝ := Real.cos (t * (u - L / 2))

/-- The left antiderivative. -/
def leftAnti (b t L : ℝ) (u : ℝ) : ℝ :=
  Real.exp (b * u) * (b * Real.cos (t * (u - L / 2)) + t * Real.sin (t * (u - L / 2)))

/-- The right antiderivative. -/
def rightAnti (b t L : ℝ) (u : ℝ) : ℝ :=
  Real.exp (-b * u) * (-b * Real.cos (t * (u - L / 2)) + t * Real.sin (t * (u - L / 2)))

theorem hasDerivAt_leftAnti (hbt : b ^ 2 + t ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (fun u => leftAnti b t L u / (b ^ 2 + t ^ 2))
      (Real.exp (b * u) * wave t L u) u := by
  have harg : HasDerivAt (fun u : ℝ => t * (u - L / 2)) t u := by
    simpa using ((hasDerivAt_id u).sub_const (L / 2)).const_mul t
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (b * u)) (Real.exp (b * u) * b) u := by
    simpa using ((hasDerivAt_id u).const_mul b).exp
  have hin := (harg.cos.const_mul b).add (harg.sin.const_mul t)
  refine ((hexp.mul hin).div_const (b ^ 2 + t ^ 2)).congr_deriv ?_
  simp only [Pi.add_apply]
  unfold wave
  field_simp
  ring

theorem hasDerivAt_rightAnti (hbt : b ^ 2 + t ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (fun u => rightAnti b t L u / (b ^ 2 + t ^ 2))
      (Real.exp (-b * u) * wave t L u) u := by
  have harg : HasDerivAt (fun u : ℝ => t * (u - L / 2)) t u := by
    simpa using ((hasDerivAt_id u).sub_const (L / 2)).const_mul t
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-b * u)) (Real.exp (-b * u) * -b) u := by
    simpa using ((hasDerivAt_id u).const_mul (-b)).exp
  have hin := (harg.cos.const_mul (-b)).add (harg.sin.const_mul t)
  refine ((hexp.mul hin).div_const (b ^ 2 + t ^ 2)).congr_deriv ?_
  simp only [Pi.add_apply]
  unfold wave
  field_simp
  ring

theorem leftMoment_wave (hbt : b ^ 2 + t ^ 2 ≠ 0) (s : ℝ) :
    leftMoment b (wave t L) s = (leftAnti b t L s - leftAnti b t L 0) / (b ^ 2 + t ^ 2) := by
  rw [leftMoment, integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_leftAnti hbt u)
    (by apply Continuous.intervalIntegrable; unfold wave; fun_prop)]
  ring

theorem rightMoment_wave (hbt : b ^ 2 + t ^ 2 ≠ 0) (s : ℝ) :
    rightMoment b L (wave t L) s = (rightAnti b t L L - rightAnti b t L s) / (b ^ 2 + t ^ 2) := by
  rw [rightMoment, integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_rightAnti hbt u)
    (by apply Continuous.intervalIntegrable; unfold wave; fun_prop)]
  ring

/-- **The oscillatory parts cancel.**  The two half-window moments add to the resolvent multiple of
the wave, plus two boundary terms sharing the factor `b cos (tL/2) − t sin (tL/2)`. -/
theorem convSplit_wave (hbt : b ^ 2 + t ^ 2 ≠ 0) (s : ℝ) :
    convSplit b L (wave t L) s
      = 2 * b / (b ^ 2 + t ^ 2) * wave t L s
        - (Real.exp (-b * s) + Real.exp (b * (s - L)))
            * (b * Real.cos (t * (L / 2)) - t * Real.sin (t * (L / 2))) / (b ^ 2 + t ^ 2) := by
  have he : Real.exp (b * (s - L)) = Real.exp (b * s) * Real.exp (-b * L) := by
    rw [← Real.exp_add]; ring_nf
  simp only [convSplit, leftMoment_wave hbt, rightMoment_wave hbt, leftAnti, rightAnti, wave,
    mul_zero, Real.exp_zero]
  rw [show t * (L - L / 2) = t * (L / 2) from by ring,
    show t * (0 - L / 2) = -(t * (L / 2)) from by ring, Real.cos_neg, Real.sin_neg, he,
    show -b * s = -(b * s) from by ring, Real.exp_neg]
  have hE : Real.exp (b * s) ≠ 0 := Real.exp_ne_zero _
  field_simp
  ring

end Cvs.WeilForm.ChannelKernelCosineEigen
