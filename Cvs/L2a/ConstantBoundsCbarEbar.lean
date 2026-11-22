import Mathlib
import Cvs.L2a.LowConstantUniform
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Upstream.LogFiveSevenBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `C̄(80, r̄_f) ≤ 16` and `Ē ≤ 9`

`log 80 = 4 log 2 + log 5` encloses `r̄`, `r̄_f`; `C̄(80, r̄_f) ≤ 16`, `F̄ ≤ 100.8`, `W̄ ≤ 0.312`, `R̄₀ ≤ 3/2` and the
exact `R̄₁` then give `Ē = ((√F̄ + √W̄ + √R̄₀)/√(1 + log 80) + √R̄₁)²/π ≤ 9`.
-/

noncomputable section

open Real Set Cvs.L2a.LowConstantUniform Cvs.Prolate.Mellin.FarPartLevelBound Cvs.Prolate.Mellin.GreenBoundaryBound Cvs.Prolate.Mellin.GreenBulkBound Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.Prolate.Mellin.EdgeRemainderClosedForm Cvs.Prolate.EdgeBesselCount

namespace Cvs.L2a.ConstantBoundsCbarEbar

theorem log80_bounds : (43820257 / 10000000 : ℝ) ≤ Real.log 80 ∧ Real.log 80 ≤ 43820278 / 10000000 := by
  have e : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
    rw [show (80 : ℝ) = 2 ^ 4 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [e]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Cvs.Enclosure.log_five_bounds'.1,
    Cvs.Enclosure.log_five_bounds'.2]

theorem rBar_le : rBar ≤ 34563 / 1000000 := by
  have h := log80_bounds.1
  unfold rBar
  have : 1 / (1 + Real.log 80) ^ 2 ≤ 1 / (1 + 43820257 / 10000000) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  norm_num at this ⊢
  linarith

theorem rBarF_le : rBarF ≤ 8641 / 1000000 := by
  have h := log80_bounds.1
  unfold rBarF
  have : 1 / (4 * (1 + Real.log 80) ^ 2) ≤ 1 / (4 * (1 + 43820257 / 10000000) ^ 2) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by norm_num))
  norm_num at this ⊢
  linarith

theorem a0_le : a0 ≤ 11429 / 10000 := by
  unfold a0 betaEdge
  have e : Real.log (12 / 5) = 2 * Real.log 2 + Real.log 3 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [e]
  have := Real.log_two_lt_d9
  have := Real.log_three_lt_d9
  have := Cvs.Enclosure.log_five_bounds'.1
  norm_num
  linarith

theorem a1_eq : a1 = 15035625 / 31826560 := by unfold a1 betaEdge; norm_num

theorem a0_nonneg : 0 ≤ a0 := by
  unfold a0 betaEdge
  have : 0 ≤ Real.log (12 / 5) := Real.log_nonneg (by norm_num)
  positivity

theorem S1at80_le : S1at80 ≤ 9172 / 1000 := by
  unfold S1at80
  have h80 := log80_bounds.2
  have h16 : Real.log 16 ≤ 27725888 / 10000000 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num; linarith [Real.log_two_lt_d9]
  have h160 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have ha0 := a0_le
  have ha00 := a0_nonneg
  rw [a1_eq]
  have hx : a0 + 15035625 / 31826560 * Real.log 80 ≤ 11429 / 10000 + 15035625 / 31826560 * (43820278 / 10000000) := by
    linarith
  have hx0 : 0 ≤ a0 + 15035625 / 31826560 * Real.log 80 := by
    have := log80_bounds.1; nlinarith
  nlinarith [mul_le_mul hx h16 h160 (by norm_num)]

theorem R1bar_eq : R1bar = 16 / 15 * (3 / 50) * (15035625 / 31826560) := by unfold R1bar; rw [a1_eq]

theorem e1_le : e1 rBar ≤ 16419 / 10000 := by
  have hr := rBar_le
  have hr0 := rBar_mem.1
  have s5 : (2236067 / 1000000 : ℝ) ≤ √5 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s30 : (5477225 / 1000000 : ℝ) ≤ √30 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h1 : 2 / √5 ≤ 2 / (2236067 / 1000000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) s5
  have h2 : 14 / √30 ≤ 14 / (5477225 / 1000000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) s30
  have h3 : 32 / √5 ≤ 32 / (2236067 / 1000000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) s5
  have h0 : 0 ≤ 14 / √30 + 32 / √5 := by positivity
  have hn : 2 / √5 + rBar * (14 / √30 + 32 / √5)
      ≤ 2 / (2236067 / 1000000) + 34563 / 1000000 * (14 / (5477225 / 1000000) + 32 / (2236067 / 1000000)) := by
    have := mul_le_mul hr (add_le_add h2 h3) h0 (by norm_num)
    linarith
  have hd : (1 - 34563 / 1000000 : ℝ) ^ 3 ≤ (1 - rBar) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  unfold e1
  rw [div_le_iff₀ (by have : (0 : ℝ) < 1 - rBar := by linarith
                      positivity)]
  norm_num at hn hd ⊢
  nlinarith

theorem Wbar_le : Wbar ≤ 312 / 1000 := by
  have hr := rBar_le
  have hr0 := rBar_mem.1
  have sr : √rBar ≤ 18592 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have s3 : √3 ≤ 17320509 / 10000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : (3965437 / 1000000 : ℝ) ≤ 4 - rBar := by linarith
  have h4' : (3965437 / 1000000 : ℝ) ^ 2 ≤ (4 - rBar) ^ 2 := pow_le_pow_left₀ (by norm_num) h4 2
  have a : 2 * √rBar / (4 - rBar) ≤ 2 * (18592 / 100000) / (3965437 / 1000000) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) h4
  have b : 64 / (3 * (4 - rBar) ^ 2 * 80) ≤ 64 / (3 * (3965437 / 1000000) ^ 2 * 80) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have c : 32 * √3 / (3 * (4 - rBar) ^ 2) ≤ 32 * (17320509 / 10000000) / (3 * (3965437 / 1000000) ^ 2) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by nlinarith)
  have hx0 : 0 ≤ 2 * √rBar / (4 - rBar) + 64 / (3 * (4 - rBar) ^ 2 * 80) := by
    have : 0 < 4 - rBar := by linarith
    positivity
  have hx : 2 * √rBar / (4 - rBar) + 64 / (3 * (4 - rBar) ^ 2 * 80)
      ≤ 2 * (18592 / 100000) / (3965437 / 1000000) + 64 / (3 * (3965437 / 1000000) ^ 2 * 80) := by linarith
  have hsq := pow_le_pow_left₀ hx0 hx 2
  unfold Wbar omega2Sq
  norm_num at hsq c ⊢
  linarith

end Cvs.L2a.ConstantBoundsCbarEbar
