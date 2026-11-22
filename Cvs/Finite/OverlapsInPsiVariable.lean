import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The overlaps, in `ψ`'s variable

`Cvs.Finite.ModeOverlapsClosedForm` gives the mode overlaps in `y`; `CvS`'s `ψ` reads them in `1 − y/L`. At integer modes
the two differ by a sign on the sine and not at all on the cosine, which turns the off-diagonal
overlap into a divided difference and the diagonal into `ψ'`'s integrand.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.Finite.OverlapsInPsiVariable

/-- At an integer mode the sine flips sign under `y ↦ 1 − y/L`. -/
theorem sin_reflect (n : ℤ) (L y : ℝ) :
    Real.sin (2 * π * n * (1 - y / L)) = -Real.sin (2 * π * n * y / L) := by
  have harg : 2 * π * (n : ℝ) * (1 - y / L)
      = (n : ℝ) * (2 * π) - 2 * π * (n : ℝ) * y / L := by ring
  rw [harg, Real.sin_int_mul_two_pi_sub]

/-- At an integer mode the cosine is unchanged. -/
theorem cos_reflect (n : ℤ) (L y : ℝ) :
    Real.cos (2 * π * n * (1 - y / L)) = Real.cos (2 * π * n * y / L) := by
  have harg : 2 * π * (n : ℝ) * (1 - y / L)
      = -(2 * π * (n : ℝ) * y / L) + (n : ℝ) * (2 * π) := by ring
  rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_neg]

/-- **The off-diagonal overlap is a divided difference of `ψ`'s integrand.** -/
theorem overlap_ne_eq_divided_difference (L : ℝ) (m n : ℤ) (y : ℝ) :
    (Real.sin (2 * π * m * y / L) - Real.sin (2 * π * n * y / L)) / (π * ((n : ℝ) - m))
      = (1 / π) * ((Real.sin (2 * π * n * (1 - y / L))
          - Real.sin (2 * π * m * (1 - y / L))) / ((n : ℝ) - m)) := by
  rw [sin_reflect, sin_reflect]
  by_cases h : ((n : ℝ) - m) = 0
  · rw [h]; simp
  · field_simp
    ring

/-- **The diagonal overlap is `ψ'`'s integrand.** -/
theorem overlap_self_eq_deriv_integrand (L : ℝ) (n : ℤ) (y : ℝ) :
    2 * (1 - y / L) * Real.cos (2 * π * n * y / L)
      = 2 * (1 - y / L) * Real.cos (2 * π * n * (1 - y / L)) := by
  rw [cos_reflect]

end Cvs.Finite.OverlapsInPsiVariable
