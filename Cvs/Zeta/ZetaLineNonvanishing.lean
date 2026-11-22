import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip
import Cvs.Zeta.XiZeroCountBridge
import Cvs.Zeta.XiZetaBridge

/-!
# `ζ` does not vanish on the horizontal segment at a collar height

`Cvs.Zeta.XiHorizontal` leaves one hypothesis to its caller: that `ζ` has no zero on the
segment `[−1, 2] × {T'}`.
-/

open Complex

namespace Cvs.Zeta

/-- `ζ` has no zero with `Re s ≤ 0` off the real axis. -/
theorem riemannZeta_ne_zero_of_re_le_zero {s : ℂ} (hre : s.re ≤ 0) (him : s.im ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro h
  refine riemannXi_ne_zero_of_re_le_zero hre ?_
  rw [riemannXi_eq_gammaR_mul_zeta (ne_zero_of_im_ne_zero him) (ne_one_of_im_ne_zero him)
    (gammaR_ne_zero_of_im_ne_zero him), h]
  ring

/-- **`ζ` does not vanish on the horizontal segment at a collar height.** This is the last
hypothesis `Cvs.Zeta.XiHorizontal` leaves to its caller, and the collar discharges it. -/
theorem zeta_ne_zero_on_collar_line {T' δ : ℝ} (hT' : 1 ≤ T') (hδ0 : 0 < δ)
    (hcollar : ∀ u : ℂ, riemannXi u = 0 → |u.im| < T' ∨ T' + δ ≤ |u.im|) :
    ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta ((x : ℂ) + T' * I) ≠ 0 := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
  have him : (((x : ℂ) + T' * I)).im = T' := by simp
  have hre : (((x : ℂ) + T' * I)).re = x := by simp
  have him0 : (((x : ℂ) + T' * I)).im ≠ 0 := by rw [him]; linarith
  rcases le_or_gt x 0 with h0 | h0
  · exact riemannZeta_ne_zero_of_re_le_zero (by rw [hre]; exact h0) him0
  · rcases le_or_gt 1 x with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact h1)
    · intro hz
      have hxi : riemannXi ((x : ℂ) + T' * I) = 0 :=
        (riemannXi_eq_zero_iff_riemannZeta (by rw [hre]; exact h0)
          (ne_one_of_im_ne_zero him0)).mpr hz
      have habs : |(((x : ℂ) + T' * I)).im| = T' := by
        rw [him, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T')]
      rcases hcollar _ hxi with hc | hc <;> rw [habs] at hc <;> linarith

end Cvs.Zeta
