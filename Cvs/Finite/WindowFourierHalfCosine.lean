import Mathlib

/-!
# The window's Fourier coefficient is half the cosine coefficient

    fourierCoeffOn (0 < L) g n = (1/L)·∫₀ᴸ g x cos(2πnx/L) dx

for a symmetric `g`, the sine part vanishing, so Mathlib's Parseval speaks about the cosine
coefficients.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Complex

namespace Cvs.Finite.WindowFourierHalfCosine

variable {L : ℝ}

/-- The sine modes are antisymmetric, at integer frequencies. -/
theorem sin_symm_int (hL : L ≠ 0) (k : ℤ) (x : ℝ) :
    Real.sin (2 * π * k / L * (L - x)) = -Real.sin (2 * π * k / L * x) := by
  have hrw : 2 * π * (k : ℝ) / L * (L - x) = (k : ℝ) * (2 * π) - 2 * π * k / L * x := by
    field_simp
  rw [hrw, Real.sin_int_mul_two_pi_sub]

/-- **A symmetric function has no sine content, at any integer frequency.** -/
theorem integral_sin_of_symm_int (hL : L ≠ 0) {g : ℝ → ℝ}
    (hg : ∀ x : ℝ, g (L - x) = g x) (k : ℤ) :
    (∫ x in (0:ℝ)..L, g x * Real.sin (2 * π * k / L * x)) = 0 := by
  have hrefl : (∫ x in (0:ℝ)..L, g (L - x) * Real.sin (2 * π * k / L * (L - x)))
      = ∫ x in (0:ℝ)..L, g x * Real.sin (2 * π * k / L * x) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun y : ℝ => g y * Real.sin (2 * π * k / L * y)) L (a := 0) (b := L)
    simpa using h
  have hneg : (∫ x in (0:ℝ)..L, g (L - x) * Real.sin (2 * π * k / L * (L - x)))
      = -∫ x in (0:ℝ)..L, g x * Real.sin (2 * π * k / L * x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hg x, sin_symm_int hL k x]
    ring
  rw [hrefl] at hneg
  linarith

/-- **The Fourier coefficient of a symmetric window function is real.** -/
theorem fourierCoeffOn_eq (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hg : ∀ x : ℝ, g (L - x) = g x) (k : ℤ) :
    fourierCoeffOn hL (fun x => (g x : ℂ)) k
      = (((1 / L) * ∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hint : ∀ x : ℝ,
      (fourier (-k) ((x : ℝ) : AddCircle (L - 0))) • ((g x : ℂ))
      = ((g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ)
        - ((g x * Real.sin (2 * π * k / L * x) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [smul_eq_mul, fourier_coe_apply]
    have hLne : (L : ℂ) ≠ 0 := by simpa using hL.ne'
    have harg : (2 * π * Complex.I * ((-k : ℤ) : ℂ) * (x : ℂ) / ((L - 0 : ℝ) : ℂ))
        = ((-(2 * π * (k : ℝ) / L * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp
      ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hi1 : IntervalIntegrable
      (fun x : ℝ => ((g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ)) volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable
      (fun x : ℝ => ((g x * Real.sin (2 * π * k / L * x) : ℝ) : ℂ) * Complex.I)
      volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hkey : (∫ x in (0:ℝ)..L,
        (fourier (-k) ((x : ℝ) : AddCircle (L - 0))) • ((g x : ℂ)))
      = ((∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * k / L * x) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (fun x _ => hint x),
      intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      integral_sin_of_symm_int hL.ne' hg k]
    push_cast
    ring
  rw [hkey, Complex.real_smul, sub_zero]
  push_cast
  ring

end Cvs.Finite.WindowFourierHalfCosine
