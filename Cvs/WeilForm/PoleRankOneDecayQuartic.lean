import Mathlib
import Cvs.WeilForm.PoleFunctionalModeClosedForm

/-!
# The rank-one obstruction decays like `n⁻⁴`

    2·A(n)² ≤ sinh²(L/4)·L⁴ / (8π⁴n⁴)

`Cvs.WeilForm.PoleFunctionalModeClosedForm` made the pole functional explicit; its denominator grows like `n²`, so the negative
square that obstructs Connes' step (a) is concentrated on the low modes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.PoleRankOneDecayQuartic

/-- **The pole functional decays quadratically in the mode.** -/
theorem abs_pole_functional_le (n : ℕ) (hn : 0 < n) {L : ℝ} (hL : 0 < L) :
    |(∫ x in (-(L/2))..(L/2), Real.cos (2 * π * n / L * x) * Real.exp (x / 2))|
      ≤ Real.sinh (L / 4) * L ^ 2 / (4 * π ^ 2 * n ^ 2) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_pos
  set ω : ℝ := 2 * π * n / L with hω
  have hω2 : ω ^ 2 = 4 * π ^ 2 * (n:ℝ) ^ 2 / L ^ 2 := by
    rw [hω]; field_simp; ring
  have hden : (0:ℝ) < 1 / 4 + ω ^ 2 := by positivity
  have hlow : 4 * π ^ 2 * (n:ℝ) ^ 2 / L ^ 2 ≤ 1 / 4 + ω ^ 2 := by
    rw [hω2]; linarith
  have hsinh : 0 ≤ Real.sinh (L / 4) := Real.sinh_nonneg_iff.mpr (by linarith)
  rw [Cvs.WeilForm.PoleFunctionalModeClosedForm.pole_functional_mode n hL, abs_div,
    abs_of_pos hden, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hsinh]
  rw [div_le_div_iff₀ hden (by positivity)]
  have hkey : 4 * π ^ 2 * (n:ℝ) ^ 2 ≤ L ^ 2 * (1 / 4 + ω ^ 2) := by
    have hL2 : (0:ℝ) < L ^ 2 := by positivity
    rw [hω2]
    field_simp
    nlinarith [hL2]
  nlinarith [mul_le_mul_of_nonneg_left hkey hsinh]

/-- **So the rank-one term is `O(n⁻⁴)`.**  `Cvs.WeilForm.PoleTermRankTwo`'s pole form on a mode is `2A²`, and the
obstruction Connes' step (a) has to absorb is therefore concentrated at low `n`. -/
theorem pole_form_mode_le (n : ℕ) (hn : 0 < n) {L : ℝ} (hL : 0 < L) :
    2 * (∫ x in (-(L/2))..(L/2), Real.cos (2 * π * n / L * x) * Real.exp (x / 2)) ^ 2
      ≤ Real.sinh (L / 4) ^ 2 * L ^ 4 / (8 * π ^ 4 * (n:ℝ) ^ 4) := by
  have hb := abs_pole_functional_le n hn hL
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_pos
  set A : ℝ := ∫ x in (-(L/2))..(L/2), Real.cos (2 * π * n / L * x) * Real.exp (x / 2) with hA
  set C : ℝ := Real.sinh (L / 4) * L ^ 2 / (4 * π ^ 2 * (n:ℝ) ^ 2) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have : 0 ≤ Real.sinh (L / 4) := Real.sinh_nonneg_iff.mpr (by linarith)
    positivity
  have hsq : A ^ 2 ≤ C ^ 2 := by
    have := abs_nonneg A
    nlinarith [sq_abs A, hb, hC0]
  have hCsq : C ^ 2 = Real.sinh (L / 4) ^ 2 * L ^ 4 / (16 * π ^ 4 * (n:ℝ) ^ 4) := by
    rw [hC]; field_simp; ring
  rw [hCsq] at hsq
  have heq : 2 * (Real.sinh (L / 4) ^ 2 * L ^ 4 / (16 * π ^ 4 * (n:ℝ) ^ 4))
      = Real.sinh (L / 4) ^ 2 * L ^ 4 / (8 * π ^ 4 * (n:ℝ) ^ 4) := by
    field_simp
    ring
  linarith [hsq, heq]

end Cvs.WeilForm.PoleRankOneDecayQuartic
