import Mathlib

/-!
# From `C/‖ξ‖³` to `guinand_weil_classical`'s hypothesis shape
-/

namespace Cvs.Detection

open Complex
open scoped Real

/-- `−i(z−½)` exchanges the two vertical directions: its real part is `z.im`. -/
theorem critical_re (z : ℂ) : (-I * (z - 1 / 2)).re = z.im := by
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]

/-- …and its imaginary part is `−(Re z − ½)`, which the strip bounds by `3/2`. -/
theorem critical_im (z : ℂ) : (-I * (z - 1 / 2)).im = -(z.re - 1 / 2) := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]

theorem critical_im_le {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    |(-I * (z - 1 / 2)).im| ≤ 3 / 2 := by
  rw [critical_im, abs_neg, abs_le]
  constructor <;> linarith

end Cvs.Detection
