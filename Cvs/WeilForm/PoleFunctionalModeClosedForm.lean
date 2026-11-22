import Mathlib

/-!
# The pole functional on a mode, in closed form

    ∫_{−L/2}^{L/2} cos(2πns/L)·e^{s/2} ds = (−1)ⁿ·sinh(L/4)/(¼ + (2πn/L)²)

`Cvs.WeilForm.PoleTermRankTwo` showed the pole term is `2·A·M`; on a mode both functionals are this number, so the
rank-one obstruction is explicit.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.PoleFunctionalModeClosedForm

/-- The antiderivative of `cos(ωx)·e^{x/2}`. -/
def antideriv (ω x : ℝ) : ℝ :=
  Real.exp (x / 2) * (Real.cos (ω * x) / 2 + ω * Real.sin (ω * x)) / (1 / 4 + ω ^ 2)

theorem hasDerivAt_antideriv (ω x : ℝ) :
    HasDerivAt (antideriv ω) (Real.cos (ω * x) * Real.exp (x / 2)) x := by
  have hd : (0:ℝ) < 1 / 4 + ω ^ 2 := by positivity
  have he : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) / 2) x :=
    (((hasDerivAt_id x).div_const 2).exp).congr_deriv (by simp only [id_eq]; ring)
  have hc : HasDerivAt (fun y : ℝ => Real.cos (ω * y) / 2)
      (-(ω * Real.sin (ω * x)) / 2) x :=
    ((((hasDerivAt_id x).const_mul ω).cos).congr_deriv (by simp only [id_eq]; ring)).div_const 2
  have hs : HasDerivAt (fun y : ℝ => ω * Real.sin (ω * y)) (ω * (ω * Real.cos (ω * x))) x :=
    ((((hasDerivAt_id x).const_mul ω).sin).congr_deriv (by simp only [id_eq]; ring)).const_mul ω
  have hprod : HasDerivAt
      (fun y : ℝ => Real.exp (y / 2) * (Real.cos (ω * y) / 2 + ω * Real.sin (ω * y)))
      (Real.exp (x / 2) / 2 * (Real.cos (ω * x) / 2 + ω * Real.sin (ω * x))
        + Real.exp (x / 2) * (-(ω * Real.sin (ω * x)) / 2 + ω * (ω * Real.cos (ω * x)))) x :=
    he.mul (hc.add hs)
  have hfin := hprod.div_const (1 / 4 + ω ^ 2)
  refine hfin.congr_deriv ?_
  field_simp
  ring

/-- **The integral, in closed form.** -/
theorem integral_cos_mul_exp (ω a b : ℝ) :
    (∫ x in a..b, Real.cos (ω * x) * Real.exp (x / 2))
      = antideriv ω b - antideriv ω a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_antideriv ω x) ?_
  exact (Continuous.intervalIntegrable (by fun_prop) a b)

/-- **The pole functional on a mode.**  At `ω = 2πn/L` the endpoints are `±L/2`, where
`ωx = ±πn`, so the sine vanishes and the cosine is `(−1)ⁿ`. -/
theorem pole_functional_mode (n : ℕ) {L : ℝ} (hL : 0 < L) :
    (∫ x in (-(L/2))..(L/2), Real.cos (2 * π * n / L * x) * Real.exp (x / 2))
      = (-1) ^ n * Real.sinh (L / 4) / (1 / 4 + (2 * π * n / L) ^ 2) := by
  set ω : ℝ := 2 * π * n / L with hω
  have hd : (0:ℝ) < 1 / 4 + ω ^ 2 := by positivity
  have hend : ω * (L / 2) = (n : ℝ) * π := by
    rw [hω]; field_simp
  have hstart : ω * (-(L / 2)) = -((n : ℝ) * π) := by
    rw [hω]; field_simp
  rw [integral_cos_mul_exp, antideriv, antideriv, hend, hstart,
    Real.cos_neg, Real.sin_neg]
  have hcos : Real.cos ((n : ℝ) * π) = (-1) ^ n := by
    have := Real.cos_int_mul_pi (n : ℤ)
    push_cast at this
    simpa using this
  have hsin : Real.sin ((n : ℝ) * π) = 0 := Real.sin_nat_mul_pi n
  rw [hcos, hsin, Real.sinh_eq]
  field_simp
  ring

end Cvs.WeilForm.PoleFunctionalModeClosedForm
