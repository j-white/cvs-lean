import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Elementary bounds on the complex `Γ`, with no asymptotics

Two bounds that Mathlib does not have, both immediate from exact identities:
-/

open MeasureTheory Set Complex Real

namespace Cvs.Zeta

/-- `|Γ(s)| ≤ Γ(Re s)` on the right half-plane: in the Euler integral the factor
`x^{i·Im s}` has modulus `1`, so the imaginary part contributes nothing. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 2

/-- `|sin z| ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  have hb1 : Real.exp (-z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs _)
  have hb2 : Real.exp z.im ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self _)
  have hsum := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  rw [h1, h2] at hsum
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **`1/Γ` off the real axis, for `Re z < 1`.** Euler reflection turns the reciprocal into
`Γ(1-z) sin(πz)/π`, and both factors are then bounded by elementary means: `|Γ(1-z)| ≤ Γ(1 -
Re z)` and `|sin(πz)| ≤ e^{π|Im z|}`. -/
theorem norm_inv_Gamma_le {z : ℂ} (h0 : z.im ≠ 0) (h1 : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (1 - z.re) * Real.exp (π * |z.im|) / π := by
  -- `z` is not a nonpositive integer, so `Γ z ≠ 0`
  have hz : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    exact h0 (by rw [hm]; simp)
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
  -- `sin (π z) ≠ 0`, since the complex zeros of `sin` are the real integer multiples of `π`
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hc
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hzk : z = (k : ℂ) := by
      rw [mul_comm (π : ℂ) z] at hk
      exact mul_right_cancel₀ hpi hk
    exact h0 (by rw [hzk]; simp)
  -- Euler reflection, rearranged
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have key : (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    refine inv_eq_of_mul_eq_one_right ?_
    rw [show Complex.Gamma z * (Complex.Gamma (1 - z) * Complex.sin (π * z) / π)
        = Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (π * z) / π by ring, hrefl]
    field_simp
  rw [key, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hg : ‖Complex.Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have := norm_Gamma_le_Gamma_re (s := 1 - z) (by simp; linarith)
    simpa using this
  have hs : ‖Complex.sin (π * z)‖ ≤ Real.exp (π * |z.im|) := by
    refine (norm_sin_le_exp_abs_im _).trans_eq ?_
    congr 1
    simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]
  have hg0 : (0 : ℝ) ≤ ‖Complex.Gamma (1 - z)‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ ‖Complex.sin (π * z)‖ := norm_nonneg _
  gcongr

/-! ### `Γ` on a strip reaching arbitrarily far left -/

end Cvs.Zeta
