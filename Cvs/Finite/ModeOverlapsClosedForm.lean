import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The mode overlaps, in closed form

`∫ e^{i(m−n)x} ` over a period vanishes off the diagonal and returns the length on it, so the
Gram of the exponential modes is diagonal and the real part is read off directly.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex intervalIntegral

namespace Cvs.Finite.ModeOverlapsClosedForm

/-! ### The two overlap integrals -/

/-- **The off-diagonal overlap, in closed form.** -/
theorem integral_overlap_ne {L : ℝ} (hL : L ≠ 0) {m n : ℤ} (hmn : m ≠ n) (y : ℝ) :
    (1 / (L : ℂ)) * ∫ x in y..L,
        Complex.exp (2 * π * I * m * ((y : ℂ) - x) / L + 2 * π * I * n * x / L)
      = (Complex.exp (2 * π * I * m * y / L) - Complex.exp (2 * π * I * n * y / L))
          / (2 * π * I * ((n : ℂ) - m)) := by
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : ((n : ℂ) - (m : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  have hnum : 2 * (π : ℂ) * I * ((n : ℂ) - m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero) hd
  set c : ℂ := 2 * π * I * ((n : ℂ) - m) / L with hcdef
  have hcne : c ≠ 0 := div_ne_zero hnum hLC
  -- split off the `x`-free factor
  have hmerge : ∀ x : ℝ,
      Complex.exp (2 * π * I * m * ((y : ℂ) - x) / L + 2 * π * I * n * x / L)
        = Complex.exp (2 * π * I * m * y / L) * Complex.exp (c * x) := by
    intro x
    rw [← Complex.exp_add, hcdef]
    congr 1
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hmerge x),
    intervalIntegral.integral_const_mul, integral_exp_mul_complex hcne]
  -- the upper endpoint lands on the lattice
  have hcL : Complex.exp (c * (L : ℝ)) = 1 := by
    rw [hcdef, show 2 * (π : ℂ) * I * ((n : ℂ) - m) / (L : ℂ) * (L : ℂ)
        = ((n - m : ℤ) : ℂ) * (2 * π * I) by push_cast; field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I _
  -- the lower endpoint turns the `m`-mode into the `n`-mode
  have hcy : Complex.exp (2 * π * I * m * y / L) * Complex.exp (c * (y : ℝ))
      = Complex.exp (2 * π * I * n * y / L) := by
    rw [← Complex.exp_add, hcdef]
    congr 1
    field_simp
    ring
  have expand : Complex.exp (2 * π * I * m * y / L) * ((1 - Complex.exp (c * (y : ℝ))) / c)
      = (Complex.exp (2 * π * I * m * y / L) - Complex.exp (2 * π * I * n * y / L)) / c := by
    rw [← hcy]; ring
  rw [hcL, expand, hcdef]
  field_simp

/-- **The diagonal overlap, in closed form.** -/
theorem integral_overlap_self {L : ℝ} (hL : L ≠ 0) (n : ℤ) (y : ℝ) :
    (1 / (L : ℂ)) * ∫ x in y..L,
        Complex.exp (2 * π * I * n * ((y : ℂ) - x) / L + 2 * π * I * n * x / L)
      = (1 - (y : ℂ) / L) * Complex.exp (2 * π * I * n * y / L) := by
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hconst : ∀ x : ℝ,
      Complex.exp (2 * π * I * n * ((y : ℂ) - x) / L + 2 * π * I * n * x / L)
        = Complex.exp (2 * π * I * n * y / L) := by
    intro x
    congr 1
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hconst x), intervalIntegral.integral_const,
    Complex.real_smul]
  push_cast
  field_simp

/-! ### The symmetrisation `z ↦ 2 Re z`, in real form -/

/-- The mode `e^{2πiky/L}`, split into its real and imaginary parts. -/
private theorem exp_mode_eq (L : ℝ) (k : ℤ) (y : ℝ) :
    Complex.exp (2 * π * I * k * y / L)
      = (Real.cos (2 * π * k * y / L) : ℂ) + (Real.sin (2 * π * k * y / L) : ℂ) * I := by
  rw [show 2 * (π : ℂ) * I * (k : ℂ) * (y : ℂ) / (L : ℂ)
      = ((2 * π * k * y / L : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **The off-diagonal symmetrisation, in real form.** -/
theorem two_re_overlap_ne (L : ℝ) (m n : ℤ) (y : ℝ) :
    2 * ((Complex.exp (2 * π * I * m * y / L) - Complex.exp (2 * π * I * n * y / L))
          / (2 * π * I * ((n : ℂ) - m))).re
      = (Real.sin (2 * π * m * y / L) - Real.sin (2 * π * n * y / L)) / (π * ((n : ℝ) - m)) := by
  rcases eq_or_ne m n with rfl | hmn
  · simp
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdR : ((n : ℝ) - (m : ℝ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  have hd : ((n : ℂ) - (m : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  set cm : ℝ := Real.cos (2 * π * m * y / L)
  set sm : ℝ := Real.sin (2 * π * m * y / L)
  set cn : ℝ := Real.cos (2 * π * n * y / L)
  set sn : ℝ := Real.sin (2 * π * n * y / L)
  have hq : ((cm : ℂ) + (sm : ℂ) * I - ((cn : ℂ) + (sn : ℂ) * I))
        / (2 * π * I * ((n : ℂ) - m))
      = (((sm - sn) / (2 * π * ((n : ℝ) - m)) : ℝ) : ℂ)
          - (((cm - cn) / (2 * π * ((n : ℝ) - m)) : ℝ) : ℂ) * I := by
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero) hd)]
    push_cast
    field_simp
    linear_combination ((cm : ℂ) - cn) * Complex.I_sq
  rw [exp_mode_eq, exp_mode_eq, hq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  field_simp

/-- **The diagonal symmetrisation, in real form.** -/
theorem two_re_overlap_self (L : ℝ) (n : ℤ) (y : ℝ) :
    2 * ((1 - (y : ℂ) / L) * Complex.exp (2 * π * I * n * y / L)).re
      = 2 * (1 - y / L) * Real.cos (2 * π * n * y / L) := by
  rw [exp_mode_eq, show (1 : ℂ) - (y : ℂ) / (L : ℂ) = ((1 - y / L : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, zero_add,
    add_zero]
  ring

/-! ### The two symmetrised overlaps -/

/-- **The off-diagonal entry of CvS's matrix.** -/
theorem two_re_integral_overlap_ne {L : ℝ} (hL : L ≠ 0) {m n : ℤ} (hmn : m ≠ n) (y : ℝ) :
    2 * ((1 / (L : ℂ)) * ∫ x in y..L,
        Complex.exp (2 * π * I * m * ((y : ℂ) - x) / L + 2 * π * I * n * x / L)).re
      = (Real.sin (2 * π * m * y / L) - Real.sin (2 * π * n * y / L)) / (π * ((n : ℝ) - m)) := by
  rw [integral_overlap_ne hL hmn y, two_re_overlap_ne]

/-- **The diagonal entry of CvS's matrix.** -/
theorem two_re_integral_overlap_self {L : ℝ} (hL : L ≠ 0) (n : ℤ) (y : ℝ) :
    2 * ((1 / (L : ℂ)) * ∫ x in y..L,
        Complex.exp (2 * π * I * n * ((y : ℂ) - x) / L + 2 * π * I * n * x / L)).re
      = 2 * (1 - y / L) * Real.cos (2 * π * n * y / L) := by
  rw [integral_overlap_self hL n y, two_re_overlap_self]

end Cvs.Finite.ModeOverlapsClosedForm
