import Mathlib

/-!
# A window mode's transform, in closed form

    ∫₀ᴸ cos(2πn x/L)·e^{izx} dx = 2z·e^{izL/2}·sin(zL/2) / (z² − (2πn/L)²)

so a finite cosine combination's transform is `sin(zL/2)` times a partial-fraction sum, and
its zeros are the lattice's — which are real — together with the sum's.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Complex intervalIntegral

namespace Cvs.Finite.WindowModeTransformClosed

/-- **A single window mode's transform.** -/
theorem integral_cos_mode {L : ℝ} (hL : L ≠ 0) (n : ℕ) {z : ℂ}
    (hz : z ^ 2 ≠ ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2) :
    (∫ x in (0:ℝ)..L, (Real.cos (2 * Real.pi * n / L * x) : ℂ)
        * Complex.exp (Complex.I * z * (x : ℂ)))
      = 2 * z * Complex.exp (Complex.I * z * (L : ℂ) / 2)
          * Complex.sin (z * (L : ℂ) / 2) / (z ^ 2 - ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2) := by
  set w : ℂ := ((2 * Real.pi * n / L : ℝ) : ℂ) with hw
  -- split the cosine into the two characters
  have hsplit : ∀ x : ℝ, ((Real.cos (2 * Real.pi * n / L * x) : ℝ) : ℂ)
      * Complex.exp (Complex.I * z * (x : ℂ))
      = (Complex.exp (Complex.I * (w + z) * (x : ℂ))
          + Complex.exp (Complex.I * (z - w) * (x : ℂ))) / 2 := by
    intro x
    rw [Complex.ofReal_cos, Complex.cos, hw]
    push_cast
    rw [div_mul_eq_mul_div, add_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> ring
  rw [intervalIntegral.integral_congr (fun x _ => hsplit x)]
  -- the two frequencies are nonzero
  have hsq : (z - w) * (z + w) ≠ 0 := by
    rw [show (z - w) * (z + w) = z ^ 2 - w ^ 2 by ring]
    exact sub_ne_zero.mpr hz
  have hz1 : w + z ≠ 0 := by
    intro hc
    exact hsq (by rw [show z + w = w + z by ring, hc, mul_zero])
  have hz2 : z - w ≠ 0 := by
    intro hc
    exact hsq (by rw [hc, zero_mul])
  have hc1 : Complex.I * (w + z) ≠ 0 := mul_ne_zero Complex.I_ne_zero hz1
  have hc2 : Complex.I * (z - w) ≠ 0 := mul_ne_zero Complex.I_ne_zero hz2
  -- the lattice makes both endpoint values the same
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hwL : w * (L : ℂ) = 2 * Real.pi * (n : ℂ) := by
    rw [hw]
    push_cast
    field_simp
  have hlat : Complex.exp (Complex.I * (w * (L : ℂ))) = 1 := by
    rw [hwL, show Complex.I * (2 * (Real.pi : ℂ) * (n : ℂ))
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I (n : ℤ) |>.trans rfl
  have hint1 : IntervalIntegrable
      (fun x : ℝ => Complex.exp (Complex.I * (w + z) * (x : ℂ)))
      MeasureTheory.volume 0 L :=
    (Complex.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun x : ℝ => Complex.exp (Complex.I * (z - w) * (x : ℂ)))
      MeasureTheory.volume 0 L :=
    (Complex.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hint1 hint2,
    integral_exp_mul_complex hc1, integral_exp_mul_complex hc2]
  have hE1 : Complex.exp (Complex.I * (w + z) * (L : ℂ))
      = Complex.exp (Complex.I * z * (L : ℂ)) := by
    rw [show Complex.I * (w + z) * (L : ℂ)
        = Complex.I * (w * (L : ℂ)) + Complex.I * z * (L : ℂ) by ring,
      Complex.exp_add, hlat, one_mul]
  have hE2 : Complex.exp (Complex.I * (z - w) * (L : ℂ))
      = Complex.exp (Complex.I * z * (L : ℂ)) := by
    rw [show Complex.I * (z - w) * (L : ℂ)
        = Complex.I * z * (L : ℂ) - Complex.I * (w * (L : ℂ)) by ring,
      Complex.exp_sub, hlat, div_one]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, hE1, hE2]
  -- the half-angle form
  have hsin : Complex.sin (z * (L : ℂ) / 2)
      = (Complex.exp (-(z * (L : ℂ) / 2) * Complex.I)
        - Complex.exp (z * (L : ℂ) / 2 * Complex.I)) * Complex.I / 2 := by
    rw [Complex.sin]
  have hhalf : Complex.exp (Complex.I * z * (L : ℂ) / 2)
      * Complex.exp (z * (L : ℂ) / 2 * Complex.I)
      = Complex.exp (Complex.I * z * (L : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hhalf' : Complex.exp (Complex.I * z * (L : ℂ) / 2)
      * Complex.exp (-(z * (L : ℂ) / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add,
      show Complex.I * z * (L : ℂ) / 2 + -(z * (L : ℂ) / 2) * Complex.I = 0 by ring,
      Complex.exp_zero]
  rw [hsin]
  have hden : z ^ 2 - w ^ 2 ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring_nf
  have hA : Complex.exp (Complex.I * z * (L : ℂ) * (1 / 2))
      * Complex.exp (Complex.I * z * (L : ℂ) * (-1 / 2)) = 1 := by
    rw [← Complex.exp_add,
      show Complex.I * z * (L : ℂ) * (1 / 2) + Complex.I * z * (L : ℂ) * (-1 / 2) = 0 by ring,
      Complex.exp_zero]
  have hB : Complex.exp (Complex.I * z * (L : ℂ) * (1 / 2)) ^ 2
      = Complex.exp (Complex.I * z * (L : ℂ)) := by
    rw [sq, ← Complex.exp_add]
    congr 1
    ring
  linear_combination (-(2 * (z ^ 3 - z * w ^ 2)) * Complex.I ^ 2) * hA
    + ((2 * (z ^ 3 - z * w ^ 2)) * Complex.I ^ 2) * hB
    + ((2 * (z ^ 3 - z * w ^ 2))
        * (Complex.exp (Complex.I * z * (L : ℂ)) - 1)) * Complex.I_sq

end Cvs.Finite.WindowModeTransformClosed
