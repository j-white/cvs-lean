import Mathlib
import Cvs.Prolate.EndpointLadder
import Cvs.Prolate.EndpointLadderFourEight
import Cvs.Prolate.EndpointLadderHermiteAmp
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.LevelsBelowLinearBound
import Cvs.Prolate.SepticLevelComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint ladder law on `h₄`, `h₈`

Cvs.Prolate.EndpointLadderHermiteAmp at `g_a = rung c 2`, `g_b = rung c 4`, `c = 2πx`, `x ≥ 80`: the amplitudes give a constant
(`3c/(16√χ₄) ≥ 3√c/(16√(10π))`, `1 + 2√(χ₂/3) ≤ 5√c`), `B ≥ e^{−L₀}` and `R ≥ √c/18` (Cvs.Prolate.EndpointLadderFourEight), so
`C c^{(χ₄ − χ₂)/(2c)} h₄(1)² ≤ h₈(1)²`, the ladder law with its exact exponent. With `χ₄ − χ₂ ≥ 6c − 122`
(Cvs.Prolate.SepticLevelComparison, Cvs.Prolate.EvenRungDavisKahan) this is `C' c³ h₄(1)² ≤ h₈(1)²`.
-/

noncomputable section

open Real Set Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.EndpointLadderLaw
open Cvs.ZeroCounting

open Cvs.Prolate.EndpointLadder (aS startB ladR)
open Cvs.Prolate.EndpointLadderFourEight (ladL)

/-- The ladder-law constant `C = e^{−2L₀} · 3/(80√(10π)) · 18^{−10π}`. -/
def lawC : ℝ := exp (-(2 * ladL)) * (3 / (80 * √(10 * π))) * (18 : ℝ) ^ (-(10 * π))

theorem lawC_pos : 0 < lawC := by unfold lawC; positivity

set_option maxHeartbeats 2000000 in
/-- **The endpoint ladder law on the rungs**: at `c = 2πx`, `x ≥ 80`,
`C c^{(χ₄ − χ₂)/(2c)} h₄(1)² ≤ h₈(1)²`, `χ_k = lev c k`. -/
theorem ladder_law (x : ℕ) (hx : 80 ≤ x) :
    lawC * (2 * π * x) ^ ((lev (2 * π * x) 4 - lev (2 * π * x) 2) / (2 * (2 * π * x)))
      * rung (2 * π * x) 2 1 ^ 2 ≤ rung (2 * π * x) 4 1 ^ 2 := by
  have hx' : (80 : ℝ) ≤ x := by exact_mod_cast hx
  set c := 2 * π * (x : ℝ) with hcd
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  have hc : 160 * π ≤ c := by rw [hcd]; nlinarith
  have hc0 : 0 < c := by linarith
  have hc480 : 480 ≤ c := by nlinarith
  obtain ⟨hlt4, h4⟩ := Cvs.Prolate.LevelsBelowLinearBound.lev_lt_lin (c := c) (k := 4) (by push_cast; nlinarith)
  push_cast at hlt4
  have h2 : ∃ χ, IsLevelIdx c 2 χ := by
    obtain ⟨χ, hχ⟩ := h4; exact exists_isLevelIdx_of_le hχ (by norm_num)
  set χa := lev c 2 with hχad
  set χb := lev c 4 with hχbd
  have hχb10 : χb ≤ 10 * π * c := by linarith
  have hχb15 : 15 * c - 241 / 2 ≤ χb := Cvs.Prolate.SepticLevelComparison.fifteen_mul_sub_le_lev_four (by linarith)
  have hχa9 : χa ≤ 9 * c + 1 / 4 ∧ 0 < χa := by
    have h := Cvs.Prolate.EvenRungDavisKahan.sq_lev_two_sub_le (c := c) (by linarith)
    rw [Cvs.Prolate.EvenRungDavisKahan.mu_two, Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2] at h
    have h11 : |χa - (9 * c - 43 / 4)| ≤ 11 := by
      rw [← Real.sqrt_sq_eq_abs, show (11 : ℝ) = √(11 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [abs_le] at h11
    constructor <;> linarith
  have hχab : χa ≤ χb := lev_le h4 (by norm_num)
  have hχb0 : 0 < χb := by linarith
  have hT : √χb / c ≤ 1 / 4 := by
    rw [div_le_iff₀ hc0]
    calc √χb ≤ √((1 / 4 * c) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 / 4 * c := Real.sqrt_sq (by positivity)
  have ha2 : aS c χb ≤ 1 / 2 := by
    unfold aS; rw [show 2 * √χb / c = 2 * (√χb / c) by ring]; linarith
  obtain ⟨ha, ha₁, -, hanga, hevena, hnorma⟩ := rung_spec h2
  obtain ⟨hb, hb₁, -, hangb, hevenb, hnormb⟩ := rung_spec h4
  have H := Cvs.Prolate.EndpointLadderHermiteAmp.ladder_sq_sharp ha ha₁ hanga hevena hnorma (rung_one_ne_zero h2)
    hb hb₁ hangb hevenb hnormb (rung_one_ne_zero h4) hc0 hχa9.2 hχab ha2
  -- the closed-form factors
  have hL : Cvs.Prolate.EndpointLadderFourEight.startL c χb ≤ ladL := by
    unfold Cvs.Prolate.EndpointLadderFourEight.startL ladL
    have hr : χb / c ≤ 10 * π := by rw [div_le_iff₀ hc0]; linarith
    have hr0 : 0 ≤ χb / c := by positivity
    have e1 : 4 * χb / c = 4 * (χb / c) := by ring
    have e2 : 6 * χb ^ 2 / c ^ 2 = 6 * (χb / c) ^ 2 := by ring
    rw [e1, e2]
    nlinarith
  have hB : exp (-ladL) ≤ startB c χb :=
    (exp_le_exp.2 (neg_le_neg hL)).trans (Cvs.Prolate.EndpointLadderFourEight.exp_neg_startL_le hc0 hχb0 hT)
  have hR : √c / 18 ≤ ladR c χb := Cvs.Prolate.EndpointLadderFourEight.sqrt_div_le_ladR (by linarith) (by linarith) (by nlinarith)
  set s := √c with hsd
  have hs0 : 0 < s := Real.sqrt_pos.2 hc0
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0.le
  -- the amplitude ratio
  have hamp : 3 / (80 * √(10 * π)) ≤ 3 * c / (16 * √χb) / (1 + 2 * √(χa / 3)) := by
    have hχbs : √χb ≤ √(10 * π) * s := by
      rw [hsd, ← Real.sqrt_mul (by positivity)]; exact Real.sqrt_le_sqrt (by linarith)
    have hχas : √(χa / 3) ≤ 2 * s := by
      calc √(χa / 3) ≤ √((2 * s) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * s := Real.sqrt_sq (by positivity)
    have hs1 : 1 ≤ s := by nlinarith
    have hU : 1 + 2 * √(χa / 3) ≤ 5 * s := by linarith
    have hr10 : 0 < √(10 * π) := by positivity
    rw [div_div, le_div_iff₀ (by positivity)]
    calc 3 / (80 * √(10 * π)) * (16 * √χb * (1 + 2 * √(χa / 3)))
        ≤ 3 / (80 * √(10 * π)) * (16 * (√(10 * π) * s) * (5 * s)) := by
          gcongr
      _ = 3 * c := by rw [← hs2]; field_simp; ring
  -- the power
  set y := (χb - χa) / c with hyd
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hc0.le
  have hy10 : y ≤ 10 * π := by rw [hyd, div_le_iff₀ hc0]; linarith
  have hpow : (18 : ℝ) ^ (-(10 * π)) * c ^ ((χb - χa) / (2 * c)) ≤ ladR c χb ^ y := by
    have e : c ^ ((χb - χa) / (2 * c)) = s ^ y := by
      rw [hsd, Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le, hyd]; congr 1; field_simp
    rw [e]
    have h1 : (18 : ℝ) ^ (-(10 * π)) ≤ (18 : ℝ) ^ (-y) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (18 : ℝ) ^ (-y) * s ^ y = (s / 18) ^ y := by
      rw [Real.div_rpow hs0.le (by norm_num), Real.rpow_neg (by norm_num)]; field_simp
    calc (18 : ℝ) ^ (-(10 * π)) * s ^ y ≤ (18 : ℝ) ^ (-y) * s ^ y :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (s / 18) ^ y := h2
      _ ≤ ladR c χb ^ y := Real.rpow_le_rpow (by positivity) hR hy0
  have hcoef : lawC * c ^ ((χb - χa) / (2 * c))
      ≤ startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3)) * ladR c χb ^ y := by
    have hB2 : exp (-ladL) ^ 2 ≤ startB c χb ^ 2 := pow_le_pow_left₀ (exp_pos _).le hB 2
    have e : lawC * c ^ ((χb - χa) / (2 * c))
        = exp (-ladL) ^ 2 * (3 / (80 * √(10 * π))) * ((18 : ℝ) ^ (-(10 * π)) * c ^ ((χb - χa) / (2 * c))) := by
      unfold lawC; rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e, show startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3)) * ladR c χb ^ y
        = startB c χb ^ 2 * (3 * c / (16 * √χb) / (1 + 2 * √(χa / 3))) * ladR c χb ^ y by ring]
    exact mul_le_mul (mul_le_mul hB2 hamp (by positivity) (by positivity)) hpow (by positivity) (by positivity)
  calc lawC * c ^ ((χb - χa) / (2 * c)) * rung c 2 1 ^ 2
      ≤ startB c χb ^ 2 * (3 * c / (16 * √χb)) / (1 + 2 * √(χa / 3)) * ladR c χb ^ y * rung c 2 1 ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ rung c 4 1 ^ 2 := H

end Cvs.Prolate.EndpointLadderLaw
