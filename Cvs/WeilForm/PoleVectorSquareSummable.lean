import Mathlib
import Cvs.WeilForm.PoleFunctionalModeClosedForm
import Cvs.WeilForm.PoleVectorModes

/-!
# The pole vector is square-summable

    |poleCoeff L n| = sinh(L/4)/(¼ + ωₙ²) ≤ sinh(L/4)·(L/2πn)²

so its squares are `O(n⁻⁴)`.  This is the last hypothesis the direct method asks of the rank
one for the even-sector Weil form.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.WeilForm.PoleVectorModes

namespace Cvs.WeilForm.PoleVectorSquareSummable

/-- **The pole coefficient decays like `n⁻²`.** -/
theorem sq_poleCoeff_le {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : n ≠ 0) :
    (poleCoeff L n) ^ 2
      ≤ (Real.sinh (L / 4) * (L / (2 * π)) ^ 2) ^ 2 * (1 / ((n : ℝ) ^ 2) ^ 2) := by
  have hpi := Real.pi_pos
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsinh : 0 < Real.sinh (L / 4) := Real.sinh_pos_iff.mpr (by linarith)
  have hω : (0:ℝ) < 2 * π * (n : ℝ) / L := by positivity
  have hval : poleCoeff L n
      = (-1) ^ n * Real.sinh (L / 4) / (1 / 4 + (2 * π * (n : ℝ) / L) ^ 2) := by
    unfold poleCoeff
    exact Cvs.WeilForm.PoleFunctionalModeClosedForm.pole_functional_mode n hL
  have hden : (2 * π * (n : ℝ) / L) ^ 2 ≤ 1 / 4 + (2 * π * (n : ℝ) / L) ^ 2 := by linarith
  have hdenpos : (0:ℝ) < (2 * π * (n : ℝ) / L) ^ 2 := by positivity
  have habs : |poleCoeff L n| ≤ Real.sinh (L / 4) / (2 * π * (n : ℝ) / L) ^ 2 := by
    rw [hval, abs_div, abs_mul, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 1 / 4 + (2 * π * (n : ℝ) / L) ^ 2)]
    have hsign : |((-1 : ℝ)) ^ n| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [hsign, one_mul, abs_of_pos hsinh]
    exact div_le_div_of_nonneg_left hsinh.le hdenpos hden
  have hrw : Real.sinh (L / 4) / (2 * π * (n : ℝ) / L) ^ 2
      = Real.sinh (L / 4) * (L / (2 * π)) ^ 2 * (1 / (n : ℝ) ^ 2) := by
    field_simp
  rw [hrw] at habs
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  have hsq : (poleCoeff L n) ^ 2
      ≤ (Real.sinh (L / 4) * (L / (2 * π)) ^ 2 * (1 / (n : ℝ) ^ 2)) ^ 2 := sq_le_sq' h1 h2
  calc (poleCoeff L n) ^ 2
      ≤ (Real.sinh (L / 4) * (L / (2 * π)) ^ 2 * (1 / (n : ℝ) ^ 2)) ^ 2 := hsq
    _ = (Real.sinh (L / 4) * (L / (2 * π)) ^ 2) ^ 2 * (1 / ((n : ℝ) ^ 2) ^ 2) := by
      rw [mul_pow]
      congr 1
      rw [div_pow, one_pow]

/-- **So the pole vector is square-summable**, which is what the direct method needs. -/
theorem summable_sq_poleCoeff {L : ℝ} (hL : 0 < L) :
    Summable fun n : ℕ => (poleCoeff L n) ^ 2 := by
  have h4 : Summable fun n : ℕ => (1:ℝ) / (((n : ℝ) + 1) ^ 2) ^ 2 := by
    have hbase : Summable fun n : ℕ => (1:ℝ) / (n : ℝ) ^ 4 :=
      (Real.summable_one_div_nat_pow (p := 4)).mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).2 hbase
    refine hshift.congr fun n => ?_
    push_cast
    rw [← pow_mul]
  have hC := h4.mul_left ((Real.sinh (L / 4) * (L / (2 * π)) ^ 2) ^ 2)
  refine (summable_nat_add_iff 1).mp ?_
  refine hC.of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  have hb := sq_poleCoeff_le hL (n + 1) (Nat.succ_ne_zero n)
  push_cast at hb
  exact hb

end Cvs.WeilForm.PoleVectorSquareSummable
