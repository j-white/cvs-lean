import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical

/-!
# Every zero of `ξ` lies in the open critical strip

`rect_argument_principle_riemannXi` requires the zeros to sit *strictly inside* the rectangle.
-/

open Complex

namespace Cvs.Zeta

@[simp] theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- `ξ` does not vanish on the closed half-plane `Re s ≥ 1`.  Off `s = 1` this is
`riemannXi_eq_zero_iff_riemannZeta` plus Mathlib's `riemannZeta_ne_zero_of_one_le_re`; at
`s = 1` the prefactor `s(s−1)` kills the pole and leaves `ξ(1) = ½`. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [riemannXi_one]; norm_num
  · rw [Ne, riemannXi_eq_zero_iff_riemannZeta (by linarith) h1]
    exact riemannZeta_ne_zero_of_one_le_re hs

/-- `ξ` does not vanish on `Re s ≤ 0` — by the functional equation, which maps that half-plane
onto `Re s ≥ 1`. -/
theorem riemannXi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : riemannXi s ≠ 0 := by
  intro h
  refine riemannXi_ne_zero_of_one_le_re (s := 1 - s) (by simp; linarith) ?_
  rw [riemannXi_one_sub]
  exact h

/-- **Every zero of `ξ` lies in the open critical strip.**  This is what discharges the
"strictly inside the rectangle" hypothesis of `rect_argument_principle_riemannXi` in the
real direction, for any rectangle at least as wide as `[−1, 2]`. -/
theorem riemannXi_zero_mem_strip {s : ℂ} (h : riemannXi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hc
    exact riemannXi_ne_zero_of_re_le_zero (not_lt.mp hc) h
  · by_contra hc
    exact riemannXi_ne_zero_of_one_le_re (not_lt.mp hc) h

/-- The zeros are strictly inside the horizontal extent `[−1, 2]`. -/
theorem riemannXi_zero_re_mem {s : ℂ} (h : riemannXi s = 0) :
    (-1 : ℝ) < s.re ∧ s.re < 2 := by
  obtain ⟨h1, h2⟩ := riemannXi_zero_mem_strip h
  exact ⟨by linarith, by linarith⟩

end Cvs.Zeta
