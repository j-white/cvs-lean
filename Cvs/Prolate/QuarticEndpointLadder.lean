import Mathlib
import Cvs.Prolate.EndpointLadderLaw
import Cvs.Prolate.EvenOcticLevelComparison
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.SepticLevelComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The quartic endpoint ladder

`EndpointLadderLaw`'s law `C c^{(χ₄ − χ₂)/(2c)} h₄(1)² ≤ h₈(1)²` with `χ₄ ≥ 17c − 291/2` (Cvs.Prolate.EvenOcticLevelComparison) and `χ₂ ≤ 9c + 1/4` (Cvs.Prolate.EvenRungDavisKahan):
the exponent is at least `4 − 73/c`, so `C e^{−73} c⁴ h₄(1)² ≤ h₈(1)²` at `c = 2πx`, `x ≥ 80`, the measured power.
-/

noncomputable section

open Real Set Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.QuarticEndpointLadder
open Cvs.ZeroCounting

/-- **The quartic law**: at `c = 2πx`, `x ≥ 80`, `C e^{−73} c⁴ h₄(1)² ≤ h₈(1)²`. -/
theorem ladder_quartic (x : ℕ) (hx : 80 ≤ x) :
    Cvs.Prolate.EndpointLadderLaw.lawC * exp (-73) * (2 * π * x) ^ (4 : ℝ) * rung (2 * π * x) 2 1 ^ 2 ≤ rung (2 * π * x) 4 1 ^ 2 := by
  have hx' : (80 : ℝ) ≤ x := by exact_mod_cast hx
  set c := 2 * π * (x : ℝ) with hcd
  have hpi := Real.pi_gt_three
  have hc0 : 0 < c := by rw [hcd]; positivity
  have hc480 : 480 ≤ c := by rw [hcd]; nlinarith
  have hpi' := Real.pi_lt_d2
  have h4 := Cvs.Prolate.SepticLevelComparison.exists_isLevelIdx_of_le_four (c := c) (by linarith) (k := 4) le_rfl
  have hχb17 : 17 * c - 291 / 2 ≤ lev c 4 := Cvs.Prolate.EvenOcticLevelComparison.seventeen_mul_sub_le_lev_four (by linarith)
  have hχa : lev c 2 ≤ 9 * c + 1 / 4 := by
    have h := Cvs.Prolate.EvenRungDavisKahan.sq_lev_two_sub_le (c := c) (by linarith)
    rw [Cvs.Prolate.EvenRungDavisKahan.mu_two, Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2] at h
    have h11 : |lev c 2 - (9 * c - 43 / 4)| ≤ 11 := by
      rw [← Real.sqrt_sq_eq_abs, show (11 : ℝ) = √(11 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [abs_le] at h11; linarith
  have hexp : 4 - 73 / c ≤ (lev c 4 - lev c 2) / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    have : (4 - 73 / c) * (2 * c) = 8 * c - 146 := by field_simp; ring
    rw [this]; linarith
  have hc1 : 1 ≤ c := by linarith
  have hlog : log c ≤ c := (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
  have hmono : c ^ (4 - 73 / c) ≤ c ^ ((lev c 4 - lev c 2) / (2 * c)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 hexp
  have hsplit : c ^ (4 - 73 / c) = c ^ (4 : ℝ) * exp (-(73 / c * log c)) := by
    rw [Real.rpow_sub hc0, Real.rpow_def_of_pos hc0 (73 / c), div_eq_mul_inv, ← Real.exp_neg]; ring_nf
  have hsmall : exp (-73) ≤ exp (-(73 / c * log c)) := by
    apply exp_le_exp.2
    have : 73 / c * log c ≤ 73 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc0]; nlinarith
    linarith
  have hlaw := Cvs.Prolate.EndpointLadderLaw.ladder_law x hx
  rw [← hcd] at hlaw
  calc Cvs.Prolate.EndpointLadderLaw.lawC * exp (-73) * c ^ (4 : ℝ) * rung c 2 1 ^ 2
      ≤ Cvs.Prolate.EndpointLadderLaw.lawC * (c ^ (4 : ℝ) * exp (-(73 / c * log c))) * rung c 2 1 ^ 2 := by
        have := Cvs.Prolate.EndpointLadderLaw.lawC_pos
        have h3 : 0 ≤ c ^ (4 : ℝ) := by positivity
        have : exp (-73) * c ^ (4 : ℝ) ≤ c ^ (4 : ℝ) * exp (-(73 / c * log c)) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hsmall h3
        have h' := mul_le_mul_of_nonneg_left this Cvs.Prolate.EndpointLadderLaw.lawC_pos.le
        have := mul_le_mul_of_nonneg_right h' (sq_nonneg (rung c 2 1))
        calc _ = Cvs.Prolate.EndpointLadderLaw.lawC * (exp (-73) * c ^ (4 : ℝ)) * rung c 2 1 ^ 2 := by ring
          _ ≤ _ := this
    _ = Cvs.Prolate.EndpointLadderLaw.lawC * c ^ (4 - 73 / c) * rung c 2 1 ^ 2 := by rw [hsplit]
    _ ≤ Cvs.Prolate.EndpointLadderLaw.lawC * c ^ ((lev c 4 - lev c 2) / (2 * c)) * rung c 2 1 ^ 2 := by
        have := Cvs.Prolate.EndpointLadderLaw.lawC_pos
        gcongr
    _ ≤ rung c 4 1 ^ 2 := hlaw

end Cvs.Prolate.QuarticEndpointLadder
