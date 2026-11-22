import Mathlib
import Cvs.L2a.BandEdgeLowMass
import Cvs.L2a.ConstantBoundsCbarEbar
import Cvs.L2a.ConstantBoundsKappa
import Cvs.L2a.ConstantBoundsSbarLambda
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullSpanLowConstant
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PerLevelFarLeak
import Cvs.L2a.RampCutSumsUniform
import Cvs.L2a.SpanPlungeBound
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.GreenBulkBound
import Cvs.StepA.DirichletCosineTrial
import Cvs.WeilForm.Archimedean.ArchConstantRationalBounds
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.Zeta.Digamma.DigammaQuarterConstant

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `Ē_full ≤ 16` and the full-span threshold at a floor `κ₀`

`C̄ ≤ 15.9`, `R̄₀ ≤ 1.35` and `B̄ ≤ 14.05` give `Ē_full ≤ 16`. At `κ_F ≥ κ₀ > 0` and `κ⋆ = max(2, 2Ē_full/κ₀)`,
`bBarFull ≥ ½log(T/2) − B₀(κ₀)`, so `bBarFull ≥ 1` past `c₀(κ₀)`; `κ_full ≥ κ₀` once the JA margin exceeds
`κ₀ + (7/500)√κ₀`; `c₀(κ₀) ≤ (16384/κ₀²)e^{4(76.21 + 43.95/√κ₀ + 41.27/κ₀) + 4}` for `κ₀ ≤ 1`.
At `κ₀ = 1/38`: `B₀^F ≤ 1916` and `e^{1360} ≤ c₀^F ≤ e^{7700}`.
-/

noncomputable section

open Real Set Cvs.L2a.LowConstantUniform Cvs.Prolate.Mellin.FarPartLevelBound Cvs.Prolate.Mellin.GreenBoundaryBound Cvs.Prolate.Mellin.GreenBulkBound Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.Prolate.Mellin.EdgeRemainderClosedForm Cvs.Prolate.EdgeBesselCount Cvs.L2a.ConstantBoundsCbarEbar
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

namespace Cvs.L2a.FullSpanThreshold

/-! ### `Ē_full ≤ 16` -/

/-- **`C̄(80, r̄_f) ≤ 15.9`**. -/
theorem Cbar_le_sharp : Cbar 80 rBarF ≤ 159 / 10 := by
  have hr := rBarF_le
  have hr0 := rBarF_mem.1
  have hb : betaSq 80 rBarF ≤ 1825 / 1000 := by
    unfold betaSq
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hrho : rhoSq 80 rBarF ≤ 13161 / 1000 := by
    unfold rhoSq
    have h1 : (1 - 8641 / 1000000 : ℝ) ^ 4 ≤ (1 - rBarF) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have sb : √(betaSq 80 rBarF) ≤ 1351 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have sr : √(rhoSq 80 rBarF) ≤ 36279 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  unfold Cbar
  nlinarith

/-- `F̄ ≤ 99.55`. -/
theorem Fbar_le_sharp : Fbar ≤ 9955 / 100 := by
  have h := Cbar_le_sharp
  have h0 := (Cbar_le (le_refl (80 : ℝ)) (le_refl rBarF)).1
  unfold Fbar
  nlinarith

/-- `L_c(80) ≤ 2.9574282`. -/
theorem Lc80_le : Lc 80 ≤ 29574282 / 10000000 := by
  unfold Lc
  rw [show (80 : ℝ) / 5 = 2 ^ 4 by norm_num, Real.log_pow]
  norm_num
  have := Real.log_two_lt_d9
  rw [div_le_iff₀ (by norm_num)]
  norm_num at this ⊢
  linarith

/-- `√(I₁(r̄)I₂(r̄)) ≤ 8.4464`. -/
theorem sqrtI_le : √(I1bar rBar * I2bar rBar) ≤ 84464 / 10000 := by
  have hr := rBar_le
  have hr0 := rBar_mem.1
  have he := e1_le
  have h1r : (965437 / 1000000 : ℝ) ≤ 1 - rBar := by linarith
  have s32 : √(32 / 15 : ℝ) ≤ 14606 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hI1 : I1bar rBar ≤ (14606 / 10000 + 16419 / 10000) ^ 2 := by
    unfold I1bar
    have : 0 ≤ e1 rBar := by
      unfold e1; have : 0 < 1 - rBar := by linarith
      positivity
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hI2 : I2bar rBar ≤ 1 / (3 * (965437 / 1000000)) + (2 * (2 + 34563 / 1000000)
      + (2 + 34563 / 1000000) ^ 2 / 2) / (965437 / 1000000) ^ 4 := by
    unfold I2bar
    have a : 1 / (3 * (1 - rBar)) ≤ 1 / (3 * (965437 / 1000000)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have b : (2 * (2 + rBar) + (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4
        ≤ (2 * (2 + 34563 / 1000000) + (2 + 34563 / 1000000) ^ 2 / 2) / (965437 / 1000000) ^ 4 := by
      apply div_le_div₀ (by positivity) _ (by norm_num) (pow_le_pow_left₀ (by norm_num) h1r 4)
      have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 + rBar by linarith)
        (show 2 + rBar ≤ 2 + 34563 / 1000000 by linarith) 2
      linarith
    linarith
  have hI20 : 0 ≤ I2bar rBar := by
    unfold I2bar; have : 0 < 1 - rBar := by linarith
    positivity
  rw [Real.sqrt_le_left (by norm_num)]
  have := mul_le_mul hI1 hI2 hI20 (by positivity)
  norm_num at this ⊢
  linarith

/-- **`R̄₀ ≤ 1.35`**: `ConstantBoundsCbarEbar`'s `R0bar_le` term bounds, summed. -/
theorem R0bar_le_sharp : R0bar ≤ 135 / 100 := by
  have hr := rBar_le
  have hr0 := rBar_mem.1
  have h80 := log80_bounds
  have ha0 := a0_le
  have ha00 := a0_nonneg
  have hS := S1at80_le
  have he := e1_le
  have he0 : 0 ≤ e1 rBar := by
    unfold e1; have : 0 < 1 - rBar := by linarith
    positivity
  have hS0 : 0 ≤ S1at80 := by
    unfold S1at80; rw [a1_eq]
    have : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log 80 := by linarith
    positivity
  have h1r : (965437 / 1000000 : ℝ) ≤ 1 - rBar := by linarith
  have hlin : 2 * (a0 + a1 * Real.log 80) / 5 ≤ 12853 / 10000 := by
    rw [a1_eq]; nlinarith
  have hlin0 : 0 ≤ 2 * (a0 + a1 * Real.log 80) / 5 := by
    rw [a1_eq]; nlinarith
  have hmax : max a0 a1 ≤ 11429 / 10000 := max_le ha0 (by rw [a1_eq]; norm_num)
  have s32 : √(32 / 15 : ℝ) ≤ 14606 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have t2a : 21 / 80 / (1 + Real.log 80) ^ 2 ≤ 21 / 80 / 28 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have t2 : 2 / (3 * (1 - rBar)) * (max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2 + S1at80 / (4 * 80 ^ 2))
      ≤ 2 / (3 * (965437 / 1000000)) * (11429 / 10000 + 21 / 80 / 28 + 9172 / 1000 / (4 * 80 ^ 2)) := by
    have hk : 2 / (3 * (1 - rBar)) ≤ 2 / (3 * (965437 / 1000000)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have hin0 : 0 ≤ max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2 + S1at80 / (4 * 80 ^ 2) := by
      have : 0 ≤ max a0 a1 := le_trans ha00 (le_max_left _ _)
      positivity
    have hin : max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2 + S1at80 / (4 * 80 ^ 2)
        ≤ 11429 / 10000 + 21 / 80 / 28 + 9172 / 1000 / (4 * 80 ^ 2) := by
      have : S1at80 / (4 * 80 ^ 2) ≤ 9172 / 1000 / (4 * 80 ^ 2) := div_le_div_of_nonneg_right hS (by norm_num)
      linarith
    exact mul_le_mul hk hin hin0 (by norm_num)
  have t3 : √(32 / 15) * e1 rBar * (2 * (a0 + a1 * Real.log 80) / 5) / 80
      ≤ 14606 / 10000 * (16419 / 10000) * (12853 / 10000) / 80 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (mul_le_mul s32 he he0 (by norm_num)) hlin hlin0 (by norm_num)
  have t4 : e1 rBar ^ 2 / 2 * S1at80 / 80 ^ 2 ≤ (16419 / 10000) ^ 2 / 2 * (9172 / 1000) / 80 ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ he0 he 2) (by norm_num)) hS hS0 (by positivity)
  have hLc := Lc80_le
  have hLc0 : 0 ≤ Lc 80 := Lc_nonneg le_rfl
  have t5 : 2 * rBar * (21 / 80) * (2 * (2 + rBar) * Lc 80 + (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4
      ≤ 2 * (34563 / 1000000) * (21 / 80) * (2 * (2 + 34563 / 1000000) * (29574282 / 10000000)
        + (2 + 34563 / 1000000) ^ 2 / 2) / (965437 / 1000000) ^ 4 := by
    apply div_le_div₀ (by positivity) _ (by norm_num) (pow_le_pow_left₀ (by norm_num) h1r 4)
    have hin : 2 * (2 + rBar) * Lc 80 + (2 + rBar) ^ 2 / 2
        ≤ 2 * (2 + 34563 / 1000000) * (29574282 / 10000000) + (2 + 34563 / 1000000) ^ 2 / 2 := by
      have := mul_le_mul (show 2 * (2 + rBar) ≤ 2 * (2 + 34563 / 1000000) by linarith) hLc hLc0 (by norm_num)
      have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 + rBar by linarith)
        (show 2 + rBar ≤ 2 + 34563 / 1000000 by linarith) 2
      linarith
    exact mul_le_mul (by nlinarith) hin (by positivity) (by norm_num)
  have sI := sqrtI_le
  have t6 : √(I1bar rBar * I2bar rBar) * (2 * (a0 + a1 * Real.log 80) / 5) / 80
      ≤ 84464 / 10000 * (12853 / 10000) / 80 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul sI hlin hlin0 (by norm_num)
  have t1 : 16 / 15 * (3 / 50) * a0 ≤ 16 / 15 * (3 / 50) * (11429 / 10000) := by linarith
  unfold R0bar
  norm_num at t1 t2 t3 t4 t5 t6 ⊢
  linarith

/-- `C_M(80, 2) = 1 + 3(121/118) log 3`. -/
theorem CM80_eq : Cvs.L2a.BandEdgeLowMass.CM 80 2 = 1 + 3 * (121 / 118) * Real.log 3 := by
  unfold Cvs.L2a.BandEdgeLowMass.CM
  norm_num

/-- `C_M(80, 2) ≤ 4.37963`. -/
theorem CM80_le : Cvs.L2a.BandEdgeLowMass.CM 80 2 ≤ 437963 / 100000 := by
  rw [CM80_eq]
  have := Real.log_three_lt_d9
  norm_num at this ⊢
  linarith

/-- `80·LE(80, r̄, 5) ≤ 0.0328`. -/
theorem LE80_le : 80 * lemmaEBound 80 rBar 5 ≤ 328 / 10000 := by
  have hr := rBar_le
  have hr0 := rBar_mem.1
  have he := e1_le
  have he0 : 0 ≤ e1 rBar := by
    unfold e1; have : 0 < 1 - rBar := by linarith
    positivity
  have h1r : (965437 / 1000000 : ℝ) ≤ 1 - rBar := by linarith
  have s32 : √(32 / 15 : ℝ) ≤ 14606 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have s320 : 0 ≤ √(32 / 15 : ℝ) := Real.sqrt_nonneg _
  have hLc := Lc80_le
  have hLc0 : 0 ≤ Lc 80 := Lc_nonneg le_rfl
  have sI := sqrtI_le
  have key : 80 * lemmaEBound 80 rBar 5
      = (√(32 / 15) + 5 / 80 * e1 rBar) ^ 2 / 250
        + 2 * rBar * (1 / (3 * (1 - rBar)) + (2 * (2 + rBar) * (5 * (Lc 80 / 80))
          + 5 / 80 * (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4) / 5
        + √(I1bar rBar * I2bar rBar) / 25 / 80 := by
    unfold lemmaEBound
    field_simp
    ring
  rw [key]
  have t1 : (√(32 / 15) + 5 / 80 * e1 rBar) ^ 2 / 250 ≤ (14606 / 10000 + 5 / 80 * (16419 / 10000)) ^ 2 / 250 := by
    gcongr
  have hin : 2 * (2 + rBar) * (5 * (Lc 80 / 80)) + 5 / 80 * (2 + rBar) ^ 2 / 2
      ≤ 2 * (2 + 34563 / 1000000) * (5 * (29574282 / 10000000 / 80)) + 5 / 80 * (2 + 34563 / 1000000) ^ 2 / 2 := by
    have := mul_le_mul (show 2 * (2 + rBar) ≤ 2 * (2 + 34563 / 1000000) by linarith)
      (show 5 * (Lc 80 / 80) ≤ 5 * (29574282 / 10000000 / 80) by linarith) (by positivity) (by norm_num)
    have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 + rBar by linarith)
      (show 2 + rBar ≤ 2 + 34563 / 1000000 by linarith) 2
    linarith
  have hq : (2 * (2 + rBar) * (5 * (Lc 80 / 80)) + 5 / 80 * (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4
      ≤ (2 * (2 + 34563 / 1000000) * (5 * (29574282 / 10000000 / 80)) + 5 / 80 * (2 + 34563 / 1000000) ^ 2 / 2)
        / (965437 / 1000000) ^ 4 :=
    div_le_div₀ (by positivity) hin (by norm_num) (pow_le_pow_left₀ (by norm_num) h1r 4)
  have hk : 1 / (3 * (1 - rBar)) ≤ 1 / (3 * (965437 / 1000000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hbr0 : 0 ≤ 1 / (3 * (1 - rBar)) + (2 * (2 + rBar) * (5 * (Lc 80 / 80))
      + 5 / 80 * (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4 := by
    have : 0 < 1 - rBar := by linarith
    positivity
  have t2 : 2 * rBar * (1 / (3 * (1 - rBar)) + (2 * (2 + rBar) * (5 * (Lc 80 / 80))
        + 5 / 80 * (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4) / 5
      ≤ 2 * (34563 / 1000000) * (1 / (3 * (965437 / 1000000))
        + (2 * (2 + 34563 / 1000000) * (5 * (29574282 / 10000000 / 80)) + 5 / 80 * (2 + 34563 / 1000000) ^ 2 / 2)
          / (965437 / 1000000) ^ 4) / 5 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (by linarith) (by linarith) hbr0 (by norm_num)
  have t3 : √(I1bar rBar * I2bar rBar) / 25 / 80 ≤ 84464 / 10000 / 25 / 80 := by gcongr
  norm_num at t1 t2 t3 ⊢
  linarith

/-- **`B̄ ≤ 14.05`**. -/
theorem Bbar_le : Cvs.L2a.FullSpanLowConstant.Bbar ≤ 1405 / 100 := by
  have hr := rBar_le
  have hr0 := rBar_mem.1
  have hCM := CM80_le
  have hCM0 : 0 ≤ Cvs.L2a.BandEdgeLowMass.CM 80 2 := by
    rw [CM80_eq]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity
  have hx := LE80_le
  have sx : √(80 * lemmaEBound 80 rBar 5) ≤ 18111 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hy : 5 / (2 * (1 - rBar)) ≤ 25896 / 10000 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have sy : √(5 / (2 * (1 - rBar))) ≤ 16093 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hs0 : 0 ≤ √(80 * lemmaEBound 80 rBar 5) + √(5 / (2 * (1 - rBar))) := by positivity
  have hsq := pow_le_pow_left₀ hs0 (add_le_add sx sy) 2
  unfold Cvs.L2a.FullSpanLowConstant.Bbar
  have := mul_le_mul hCM hsq (sq_nonneg _) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **`Ē_full ≤ 16`**. -/
theorem EbarFull_le : Cvs.L2a.FullSpanLowConstant.EbarFull ≤ 16 := by
  have hF := Fbar_le_sharp
  have hW := Wbar_le
  have hR := R0bar_le_sharp
  have hB := Bbar_le
  have h80 := log80_bounds.1
  have sF : √Fbar ≤ 99775 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have sW : √Wbar ≤ 55858 / 100000 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have sR : √R0bar ≤ 11619 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
  have sB : √Cvs.L2a.FullSpanLowConstant.Bbar ≤ 374834 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have sL : (231991 / 100000 : ℝ) ≤ √(1 + Real.log 80) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have sR1 : √R1bar ≤ 173884 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num), R1bar_eq]; norm_num
  have hS0 : 0 ≤ √Fbar + 2 * √Wbar + √R0bar + √Cvs.L2a.FullSpanLowConstant.Bbar := by positivity
  have hq : (√Fbar + 2 * √Wbar + √R0bar + √Cvs.L2a.FullSpanLowConstant.Bbar) / √(1 + Real.log 80)
      ≤ (99775 / 10000 + 2 * (55858 / 100000) + 11619 / 10000 + 374834 / 100000) / (231991 / 100000) :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) sL
  have hX0 : 0 ≤ (√Fbar + 2 * √Wbar + √R0bar + √Cvs.L2a.FullSpanLowConstant.Bbar) / √(1 + Real.log 80) + √R1bar := by
    positivity
  have hX : (√Fbar + 2 * √Wbar + √R0bar + √Cvs.L2a.FullSpanLowConstant.Bbar) / √(1 + Real.log 80) + √R1bar
      ≤ (99775 / 10000 + 2 * (55858 / 100000) + 11619 / 10000 + 374834 / 100000) / (231991 / 100000)
        + 173884 / 1000000 := by linarith
  have hsq := pow_le_pow_left₀ hX0 hX 2
  have hπ := Real.pi_gt_d6
  unfold Cvs.L2a.FullSpanLowConstant.EbarFull
  rw [div_le_iff₀ Real.pi_pos]
  norm_num at hsq ⊢
  nlinarith

/-! ### The threshold at a floor `κ₀` -/

/-- `κ⋆(κ₀) = max(2, 2Ē_full/κ₀)`, so that `Ē_full/(κ⋆(κ₀)κ_F) ≤ ½` once `κ_F ≥ κ₀`. -/
def kapStarAt (κ₀ : ℝ) : ℝ := max 2 (2 * Cvs.L2a.FullSpanLowConstant.EbarFull / κ₀)

/-- `B₀(κ₀) = 57/4 + ½log π − ½a(0) + 58 + log 2 + 4√(24C̄²/π)√(1/(16κ₀)) + (63/40)(Λ̄₀ + κ̄)/κ₀`:
the constant with `bBarFull ≥ ½log(T/2) − B₀(κ₀)` at `κ_F ≥ κ₀`. -/
def B0At (κ₀ : ℝ) : ℝ :=
  57 / 4 + Real.log π / 2 - archSymbol 0 / 2 + 58 + Real.log 2
    + 4 * √(24 * Cbar 80 rBarF ^ 2 / π) * √(1 / (16 * κ₀))
    + 63 / 40 * (Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar) / κ₀

/-- **The threshold at floor `κ₀`**: `c₀(κ₀) = max(10¹⁶, 49/κ₀, 16κ⋆(κ₀)²e^{4B₀(κ₀)+4})`. -/
def c0At (κ₀ : ℝ) : ℝ :=
  max (max (10 ^ 16) (49 / κ₀)) (16 * kapStarAt κ₀ ^ 2 * exp (4 * B0At κ₀ + 4))

theorem B0At_nonneg {κ₀ : ℝ} (hκ₀ : 0 < κ₀) : 0 ≤ B0At κ₀ := by
  have ha := Cvs.StepA.DirichletCosineTrial.archSymbol_zero_upper
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL := add_nonneg Cvs.L2a.RampCutSumsUniform.LambdaBar0_nonneg Cvs.L2a.KappaUniformInX.kappaBar_nonneg
  have hs := mul_nonneg (Real.sqrt_nonneg (24 * Cbar 80 rBarF ^ 2 / π)) (Real.sqrt_nonneg (1 / (16 * κ₀)))
  have hd : 0 ≤ 63 / 40 * (Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar) / κ₀ :=
    div_nonneg (mul_nonneg (by norm_num) hL) hκ₀.le
  unfold B0At
  nlinarith

/-- **The full-span bracket against `T` at floor `κ₀`**: for `κ ≥ max(2, 2Ē_full/κ₀)`, `c ≥ max(10¹⁶, 49/κ₀)`,
`J ≤ c/4 + 1`, `κ_F ≥ κ₀ > 0` and `T = TL c κ ≥ 2`, `½log(T/2) − B₀(κ₀) ≤ bBarFull c κ J κ_F`. -/
theorem bBarFull_ge_log_at {c κ J κF κ₀ : ℝ} (hκ₀ : 0 < κ₀) (hc : 10 ^ 16 ≤ c) (hc₀ : 49 / κ₀ ≤ c)
    (hκ2 : 2 ≤ κ) (hκE : 2 * Cvs.L2a.FullSpanLowConstant.EbarFull / κ₀ ≤ κ) (hJ : J ≤ c / 4 + 1) (hκF : κ₀ ≤ κF)
    (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ) :
    Real.log (Cvs.L2a.FullTailDeepSpan.TL c κ / 2) / 2 - B0At κ₀ ≤ Cvs.L2a.FullSpanWiring.bBarFull c κ J κF := by
  set T := Cvs.L2a.FullTailDeepSpan.TL c κ with hTd
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hκF0 : 0 < κF := lt_of_lt_of_le hκ₀ hκF
  have hlogc : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc80
  have hlog80 : 0 ≤ Real.log 80 := Real.log_nonneg (by norm_num)
  have hK0 : 1 ≤ κ * (1 + Real.log c) := by nlinarith
  have hTc : T ≤ c := div_le_self hc0.le hK0
  have hT0 : 0 < T := by linarith
  -- the arch terms
  have f1 := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge hT
  have f2 : 57 / T ≤ 57 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  have f2' : 114 / T ≤ 57 := by
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 114) (by norm_num) hT; linarith
  have f3 := Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg T
  have f4 : Cvs.L2a.FullSpanLowConstant.EbarFull / (κ * κF) ≤ 1 / 2 := by
    have h1 : 2 * Cvs.L2a.FullSpanLowConstant.EbarFull ≤ κ * κ₀ := by
      rw [div_le_iff₀ hκ₀] at hκE; linarith
    have h2 : κ * κ₀ ≤ κ * κF := mul_le_mul_of_nonneg_left hκF (by linarith)
    rw [div_le_iff₀ (by positivity)]; linarith
  have f5 := mul_le_mul_of_nonneg_left f4 f3
  -- the loc term
  set Cb := Cbar 80 rBarF
  have hr : Cvs.L2a.FullTailDeepSpan.rL c κ ≤ rBarF := by
    have e : Cvs.L2a.FullTailDeepSpan.rL c κ = 1 / (κ * (1 + Real.log c)) ^ 2 + 1 / (16 * c ^ 2) := by
      unfold Cvs.L2a.FullTailDeepSpan.rL Cvs.L2a.FullTailDeepSpan.TL; field_simp
    rw [e]; unfold rBarF
    have h1 : 1 / (κ * (1 + Real.log c)) ^ 2 ≤ 1 / (4 * (1 + Real.log 80) ^ 2) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : 2 * (1 + Real.log 80) ≤ κ * (1 + Real.log c) := by nlinarith
      nlinarith
    have h2 : 1 / (16 * c ^ 2) ≤ 1 / (16 * 80 ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith
  obtain ⟨hC0, hC⟩ := Cbar_le hc80 hr
  have hA : Cvs.L2a.PerLevelFarLeak.ALoc J c (Cvs.L2a.FullTailDeepSpan.rL c κ) T κF ≤ 3 * Cb ^ 2 / (π * κ₀) := by
    unfold Cvs.L2a.PerLevelFarLeak.ALoc
    have hCC : Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 ≤ Cb ^ 2 := pow_le_pow_left₀ hC0 hC 2
    have hnum : 6 * J * Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 * T ≤ 6 * (c / 2) * Cb ^ 2 * c := by
      have s1 : 6 * J ≤ 6 * (c / 2) := by linarith
      have s2 : 6 * J * Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 ≤ 6 * (c / 2) * Cb ^ 2 :=
        mul_le_mul s1 hCC (sq_nonneg _) (by positivity)
      exact mul_le_mul s2 hTc hT0.le (by positivity)
    have hden : π * c ^ 2 * κ₀ ≤ π * c ^ 2 * κF := mul_le_mul_of_nonneg_left hκF (by positivity)
    calc 6 * J * Cbar c (Cvs.L2a.FullTailDeepSpan.rL c κ) ^ 2 * T / (π * c ^ 2 * κF)
        ≤ 6 * (c / 2) * Cb ^ 2 * c / (π * c ^ 2 * κ₀) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 3 * Cb ^ 2 / (π * κ₀) := by field_simp; ring
  have f6 : √(Cvs.L2a.PerLevelFarLeak.ALoc J c (Cvs.L2a.FullTailDeepSpan.rL c κ) T κF / 2)
      ≤ √(24 * Cb ^ 2 / π) * √(1 / (16 * κ₀)) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := div_le_div_of_nonneg_right hA (by norm_num : (0 : ℝ) ≤ 2)
    have e : 3 * Cb ^ 2 / (π * κ₀) / 2 = 24 * Cb ^ 2 / π * (1 / (16 * κ₀)) := by field_simp; ring
    linarith
  -- the NS and tail terms
  set L := Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar
  have hL0 : 0 ≤ L := add_nonneg Cvs.L2a.RampCutSumsUniform.LambdaBar0_nonneg Cvs.L2a.KappaUniformInX.kappaBar_nonneg
  have f7 : 63 / 40 * L / κF ≤ 63 / 40 * L / κ₀ :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hL0) hκ₀ hκF
  have f8 : 49 * (c / 4 + 1) / (2 * c ^ 2 * κF) ≤ 1 := by
    have h49 : 49 ≤ c * κ₀ := by rw [div_le_iff₀ hκ₀] at hc₀; linarith
    have h2 : c * κ₀ ≤ c * κF := mul_le_mul_of_nonneg_left hκF hc0.le
    have h3 := mul_le_mul_of_nonneg_left (h49.trans h2) (by positivity : (0 : ℝ) ≤ 2 * c)
    rw [div_le_one (by positivity)]; nlinarith
  unfold Cvs.L2a.FullSpanWiring.bBarFull
  rw [← hTd]
  unfold B0At
  nlinarith

/-- **`bBarFull ≥ 1` past `c₀(κ₀)`**: for `κ₀ > 0`, `c ≥ c₀(κ₀)`, `0 ≤ J ≤ c/4 + 1` and `κ_F ≥ κ₀`,
`T = TL c κ⋆(κ₀) ≥ 2` and `bBarFull(c, κ⋆(κ₀), J, κ_F) ≥ 1`; `T ≥ √c/(2κ⋆) ≥ 2e^{2B₀+2}` from `1 + log c ≤ 2√c`. -/
theorem bBarFull_ge_one_at {c J κF κ₀ : ℝ} (hκ₀ : 0 < κ₀) (hc : c0At κ₀ ≤ c) (_hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) (hκF : κ₀ ≤ κF) :
    2 ≤ Cvs.L2a.FullTailDeepSpan.TL c (kapStarAt κ₀)
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull c (kapStarAt κ₀) J κF := by
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hc49 : 49 / κ₀ ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hcB : 16 * kapStarAt κ₀ ^ 2 * exp (4 * B0At κ₀ + 4) ≤ c := le_trans (le_max_right _ _) hc
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hκ2 : 2 ≤ kapStarAt κ₀ := le_max_left _ _
  have hκ0 : 0 < kapStarAt κ₀ := by linarith
  have hsc := Real.sqrt_pos.2 hc0
  have hlog : 1 + Real.log c ≤ 2 * √c := by
    have h1 := Real.log_le_sub_one_of_pos hsc
    rw [Real.log_sqrt hc0.le] at h1
    linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hTge : √c / (2 * kapStarAt κ₀) ≤ Cvs.L2a.FullTailDeepSpan.TL c (kapStarAt κ₀) := by
    unfold Cvs.L2a.FullTailDeepSpan.TL
    have e : √c / (2 * kapStarAt κ₀) = c / (kapStarAt κ₀ * (2 * √c)) := by
      rw [show c = √c * √c from (Real.mul_self_sqrt hc0.le).symm]
      rw [Real.sqrt_mul_self hsc.le]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hc0.le (by positivity) (mul_le_mul_of_nonneg_left hlog hκ0.le)
  have hE := exp_pos (2 * B0At κ₀ + 2)
  have hsq : 4 * kapStarAt κ₀ * exp (2 * B0At κ₀ + 2) ≤ √c := by
    have e : 16 * kapStarAt κ₀ ^ 2 * exp (4 * B0At κ₀ + 4) = (4 * kapStarAt κ₀ * exp (2 * B0At κ₀ + 2)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e] at hcB
    calc 4 * kapStarAt κ₀ * exp (2 * B0At κ₀ + 2) = √((4 * kapStarAt κ₀ * exp (2 * B0At κ₀ + 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √c := Real.sqrt_le_sqrt hcB
  have hT2 : 2 * exp (2 * B0At κ₀ + 2) ≤ Cvs.L2a.FullTailDeepSpan.TL c (kapStarAt κ₀) := by
    refine le_trans ?_ hTge
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE1 : 1 ≤ exp (2 * B0At κ₀ + 2) := Real.one_le_exp (by linarith [B0At_nonneg hκ₀])
  have hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c (kapStarAt κ₀) := by linarith
  refine ⟨hT, ?_⟩
  have hb := bBarFull_ge_log_at hκ₀ hc16 hc49 hκ2 (le_max_right _ _) hJ hκF hT
  have hl : 2 * B0At κ₀ + 2 ≤ Real.log (Cvs.L2a.FullTailDeepSpan.TL c (kapStarAt κ₀) / 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  linarith

/-! ### The floor from the JA margin -/

/-- `κ₀ + 2ε√κ₀ ≤ t` gives `κ₀ ≤ (√(t + ε²) − ε)²` for `κ₀ ≥ 0`. -/
theorem floor_of_margin {ε t κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (h : κ₀ + 2 * ε * √κ₀ ≤ t) :
    κ₀ ≤ (√(t + ε ^ 2) - ε) ^ 2 := by
  have hs := Real.sq_sqrt hκ₀
  have hs0 := Real.sqrt_nonneg κ₀
  have h1 : √κ₀ + ε ≤ √(t + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : (√κ₀) ^ 2 ≤ (√(t + ε ^ 2) - ε) ^ 2 := pow_le_pow_left₀ hs0 (by linarith) 2
  linarith

/-- **`κ_full ≥ κ₀`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1`, `κ₀ ≥ 0` and
`ρ + r_S(c, σ₀) + θ + κ₀ + (7/500)√κ₀ ≤ 153/1000`; `ε_τ(5) ≤ 7/1000`. -/
theorem kappaFfull_ge_floor {c J ρ σ₀ θ κ₀ : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1)
    (hκ₀ : 0 ≤ κ₀)
    (hm : ρ + Cvs.L2a.MiddlePartQStep.rStrip c σ₀ + θ + κ₀ + 7 / 500 * √κ₀ ≤ 153 / 1000) :
    κ₀ ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c J ρ σ₀ θ := by
  have hA := Cvs.L2a.FullSpanFrameFloor.aJAfull_ge (ρ := ρ) (σ₀ := σ₀) (θ := θ) hc hJ0 hJ
  have hε := Cvs.L2a.SpanPlungeBound.epsTauFlat_five_le
  have hεs := mul_le_mul_of_nonneg_right hε (Real.sqrt_nonneg κ₀)
  have h2 : 2 * Cvs.L2a.SpanPlungeBound.epsTauFlat 5 * √κ₀ ≤ 7 / 500 * √κ₀ := by nlinarith
  have h3 : κ₀ + 7 / 500 * √κ₀ ≤ Cvs.L2a.FullSpanFrameFloor.aJAfull (10 ^ 16) c J ρ σ₀ θ := by
    refine le_trans ?_ hA
    linarith
  unfold Cvs.L2a.FullSpanFrameFloor.kappaFfull
  refine floor_of_margin hκ₀ (le_trans ?_ h3)
  linarith

/-! ### The floor `κ₀ = 1/38` -/

/-- `κ⋆^F = max(2, 76Ē_full)`, so that `Ē_full/(κ⋆^F κ_F) ≤ ½` once `κ_F ≥ 1/38`. -/
def kapStarF : ℝ := max 2 (76 * Cvs.L2a.FullSpanLowConstant.EbarFull)

/-- `B₀^F = 57/4 + ½log π − ½a(0) + 58 + log 2 + 4√(24C̄²/π)√(38/16) + (63/40)(Λ̄₀ + κ̄)·38`,
`C̄ = Cbar 80 r̄_F`: the constant with `bBarFull ≥ ½log(T/2) − B₀^F` at `κ_F ≥ 1/38`. -/
def B0F : ℝ :=
  57 / 4 + Real.log π / 2 - archSymbol 0 / 2 + 58 + Real.log 2
    + 4 * √(24 * Cbar 80 rBarF ^ 2 / π) * √(38 / 16)
    + 63 / 40 * (Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar) * 38

/-- **The full-span threshold** `c₀^F = max(10¹⁶, 16(κ⋆^F)²e^{4B₀^F+4})`. -/
def c0F : ℝ := max (10 ^ 16) (16 * kapStarF ^ 2 * exp (4 * B0F + 4))

theorem kapStarF_eq : kapStarF = kapStarAt (1 / 38) := by
  unfold kapStarF kapStarAt
  congr 1
  ring

theorem B0F_eq : B0F = B0At (1 / 38) := by
  unfold B0F B0At
  rw [show (1 : ℝ) / (16 * (1 / 38)) = 38 / 16 by norm_num]
  ring

theorem c0F_eq : c0F = c0At (1 / 38) := by
  unfold c0F c0At
  rw [← kapStarF_eq, ← B0F_eq, max_eq_left (show (49 : ℝ) / (1 / 38) ≤ 10 ^ 16 by norm_num)]

/-- **The full-span bracket against `T`**: for `κ ≥ max(2, 76Ē_full)`, `c ≥ 10¹⁶`, `J ≤ c/4 + 1`,
`κ_F ≥ 1/38` and `T = TL c κ ≥ 2`, `½log(T/2) − B₀^F ≤ bBarFull c κ J κ_F`. -/
theorem bBarFull_ge_log {c κ J κF : ℝ} (hc : 10 ^ 16 ≤ c) (hκ2 : 2 ≤ κ)
    (hκE : 76 * Cvs.L2a.FullSpanLowConstant.EbarFull ≤ κ) (hJ : J ≤ c / 4 + 1) (hκF : 1 / 38 ≤ κF)
    (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ) :
    Real.log (Cvs.L2a.FullTailDeepSpan.TL c κ / 2) / 2 - B0F ≤ Cvs.L2a.FullSpanWiring.bBarFull c κ J κF := by
  rw [B0F_eq]
  refine bBarFull_ge_log_at (by norm_num) hc (le_trans (by norm_num) hc) hκ2 ?_ hJ hκF hT
  have e : 2 * Cvs.L2a.FullSpanLowConstant.EbarFull / (1 / 38) = 76 * Cvs.L2a.FullSpanLowConstant.EbarFull := by ring
  rw [e]; exact hκE

/-- **`bBarFull ≥ 1` past `c₀^F`**: for `c ≥ c₀^F`, `0 ≤ J ≤ c/4 + 1` and `κ_F ≥ 1/38`, `T = TL c κ⋆^F ≥ 2` and
`bBarFull(c, κ⋆^F, J, κ_F) ≥ 1`: `bBarFull_ge_one_at` at `κ₀ = 1/38`. -/
theorem bBarFull_ge_one {c J κF : ℝ} (hc : c0F ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hκF : 1 / 38 ≤ κF) :
    2 ≤ Cvs.L2a.FullTailDeepSpan.TL c kapStarF ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull c kapStarF J κF := by
  rw [c0F_eq] at hc
  rw [kapStarF_eq]
  exact bBarFull_ge_one_at (by norm_num) hc hJ0 hJ hκF

/-! ### `c₀^F` in numbers -/

/-- `C̄(80, r̄_f) ≥ 422/27`. -/
theorem Cbar_ge : (422 / 27 : ℝ) ≤ Cbar 80 rBarF := by
  have hr0 := rBarF_mem.1
  have hr1 := rBarF_mem.2
  have h1r : 0 < 1 - rBarF := by linarith
  have hb : 16 / 9 ≤ betaSq 80 rBarF := by
    unfold betaSq
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hrho : 1024 / 81 ≤ rhoSq 80 rBarF := by
    unfold rhoSq
    have h4 : (1 - rBarF) ^ 4 ≤ 1 := pow_le_one₀ h1r.le (by linarith)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have sb : (4 / 3 : ℝ) ≤ √(betaSq 80 rBarF) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have sr : (32 / 9 : ℝ) ≤ √(rhoSq 80 rBarF) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  unfold Cbar
  linarith

/-- **`B₀^F ≤ 1916`**. -/
theorem B0F_le : B0F ≤ 1916 := by
  have hC := Cbar_le_sharp
  have hL := Cvs.L2a.ConstantBoundsSbarLambda.LambdaBar0_le
  have hk := Cvs.L2a.ConstantBoundsKappa.kappaBar_le
  have hC0 : 0 ≤ Cbar 80 rBarF := (Cbar_le (le_refl (80 : ℝ)) (le_refl _)).1
  have hπ := Real.pi_gt_d4
  have hsq : √(24 * Cbar 80 rBarF ^ 2 / π) ≤ 4395 / 100 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ Real.pi_pos]
    have : Cbar 80 rBarF ^ 2 ≤ (159 / 10) ^ 2 := pow_le_pow_left₀ hC0 hC 2
    nlinarith
  have h38 : √(38 / 16 : ℝ) ≤ 15412 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hprod := mul_le_mul hsq h38 (Real.sqrt_nonneg _) (by norm_num)
  have ha := Cvs.WeilForm.Archimedean.ArchConstantRationalBounds.archSymbol_zero_bounds.1
  have hlp := Cvs.Moments.log_pi_bounds.2
  have hl2 := Real.log_two_lt_d9
  unfold B0F
  norm_num at ha hlp hl2 hprod ⊢
  nlinarith

/-- **`B₀^F ≥ 341`**: the terms other than `(63/40)(Λ̄₀ + κ̄)·38 ≥ 0`. -/
theorem B0F_ge : 341 ≤ B0F := by
  have hC := Cbar_ge
  have hL := Cvs.L2a.RampCutSumsUniform.LambdaBar0_nonneg
  have hk := Cvs.L2a.KappaUniformInX.kappaBar_nonneg
  have hπ := Real.pi_lt_d4
  have hsq : (431 / 10 : ℝ) ≤ √(24 * Cbar 80 rBarF ^ 2 / π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ Real.pi_pos]
    have : (422 / 27 : ℝ) ^ 2 ≤ Cbar 80 rBarF ^ 2 := pow_le_pow_left₀ (by norm_num) hC 2
    nlinarith
  have h38 : (1541 / 1000 : ℝ) ≤ √(38 / 16 : ℝ) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hprod := mul_le_mul hsq h38 (by norm_num) (Real.sqrt_nonneg _)
  have ha := Cvs.StepA.DirichletCosineTrial.archSymbol_zero_upper
  have hlp := Cvs.Moments.log_pi_bounds.1
  have hl2 := Real.log_two_gt_d9
  unfold B0F
  norm_num at ha hlp hl2 hprod ⊢
  nlinarith

/-- `κ⋆^F ≤ 1216`. -/
theorem kapStarF_le : kapStarF ≤ 1216 :=
  max_le (by norm_num) (by linarith [EbarFull_le])

/-- **`e^{1360} ≤ c₀^F ≤ e^{7700}`**. -/
theorem c0F_bounds : exp 1360 ≤ c0F ∧ c0F ≤ exp 7700 := by
  have hB := B0F_le
  have hB' := B0F_ge
  have hκ := kapStarF_le
  have h2 : (2 : ℝ) ≤ kapStarF := le_max_left _ _
  have he := Real.exp_one_gt_d9
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    have h1 : exp 1360 ≤ exp (4 * B0F + 4) := Real.exp_le_exp.2 (by linarith)
    have h16 : 1 ≤ 16 * kapStarF ^ 2 := by nlinarith
    have := mul_le_mul h16 h1 (Real.exp_pos _).le (by positivity)
    linarith
  · have h17 : exp 1 ^ 17 = exp 17 := by rw [← Real.exp_nat_mul]; norm_num
    have hp : (2.7182818283 : ℝ) ^ 17 ≤ exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) he.le 17
    have hk : 16 * kapStarF ^ 2 ≤ exp 17 := by
      rw [← h17]
      have : kapStarF ^ 2 ≤ 1216 ^ 2 := pow_le_pow_left₀ (by linarith) hκ 2
      norm_num at hp this ⊢
      linarith
    have he1 : exp (4 * B0F + 4) ≤ exp 7668 := Real.exp_le_exp.2 (by linarith)
    have h3 : 16 * kapStarF ^ 2 * exp (4 * B0F + 4) ≤ exp 17 * exp 7668 :=
      mul_le_mul hk he1 (Real.exp_pos _).le (Real.exp_pos _).le
    rw [← Real.exp_add] at h3
    have h4 : exp (17 + 7668) ≤ exp 7700 := Real.exp_le_exp.2 (by norm_num)
    refine max_le ?_ (h3.trans h4)
    have h40 : exp 1 ^ 40 = exp 40 := by rw [← Real.exp_nat_mul]; norm_num
    have hp40 : (2.7182818283 : ℝ) ^ 40 ≤ exp 1 ^ 40 := pow_le_pow_left₀ (by norm_num) he.le 40
    have h5 : exp 40 ≤ exp 7700 := Real.exp_le_exp.2 (by norm_num)
    norm_num at hp40
    linarith

end Cvs.L2a.FullSpanThreshold
