import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandRungData
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.ScaledBandTransfer
import Cvs.L2a.TopCutBandMultiplier
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungOrthogonalityAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-! The top cut of the E-coupling: `|topE| ≤ (κ_A√c·N0top + τ̂·√(6J/(M² − 1)))·√P` for `c ≥ 80`, and
for `c ≥ 10⁶`, `|topE| ≤ T_top·√P` with `T_top = (65|ψ_j(1)| + 750F/√c + 6‖g_j‖₁/√c)/c`, uniformly in
every integer `M ≥ 3`; with `F = K_A|ψ_j(1)|` this is at most `10⁶K_A|ψ_j(1)|c^{−3/4}`. -/

noncomputable section
open Real Set Filter Topology MeasureTheory Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts
open Cvs.L2a.TopCutBandMultiplier
open scoped Interval

namespace Cvs.L2a.TopCutCouplingBound

/-! ### The transfer constant at `x₀ = M` -/

section tau
open Cvs.L2a.BandTransferBandForm

/-- `j!8^j`. -/
noncomputable def N8 (j : ℕ) : ℝ := (j.factorial : ℝ) / (1 / 8) ^ j

theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h := Real.add_one_le_exp (-x)
  rw [Real.exp_neg] at h
  have hpos : 0 < 1 - x := by linarith
  rw [le_div_iff₀ hpos]
  have he := Real.exp_pos x
  have : (1 - x) ≤ (Real.exp x)⁻¹ := by linarith
  calc Real.exp x * (1 - x) ≤ Real.exp x * (Real.exp x)⁻¹ := mul_le_mul_of_nonneg_left this he.le
    _ = 1 := mul_inv_cancel₀ he.ne'

theorem betaW_top_le {M : ℝ} (hM : 3 ≤ M) : Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) ≤ 10 / 21 := by
  have := Cvs.L2a.BandRungOutgoingWave.div_sq_sub_one_anti (u₀ := 5 / 2) (u := M - 1 / 2) (by norm_num) (by linarith)
  unfold Cvs.L2a.BandTransferKernelForm.betaW
  norm_num at this ⊢
  linarith

theorem chirpW_top_le {M : ℝ} (hM : 3 ≤ M) : Cvs.L2a.BandTransferKernelForm.chirpW M (1 / 2) ≤ 704 / 11025 := by
  unfold Cvs.L2a.BandTransferKernelForm.chirpW
  set v := M - 1 / 2 / 2
  have h : 11 / 4 ≤ v := by simp only [v]; linarith
  have a2 : 0 < v ^ 2 - 1 := by nlinarith
  have k1 := Cvs.L2a.BandRungOutgoingWave.div_sq_sub_one_anti (u₀ := 11 / 4) (u := v) (by norm_num) h
  have k2 : 1 / (v ^ 2 - 1) ≤ 1 / ((11 / 4 : ℝ) ^ 2 - 1) := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  calc v / (v ^ 2 - 1) ^ 2 = v / (v ^ 2 - 1) * (1 / (v ^ 2 - 1)) := by field_simp
    _ ≤ (11 / 4) / ((11 / 4 : ℝ) ^ 2 - 1) * (1 / ((11 / 4 : ℝ) ^ 2 - 1)) :=
        mul_le_mul k1 k2 (by positivity) (by norm_num)
    _ = 704 / 11025 := by norm_num

theorem varsig_le : varsig 0 ≤ 2 / 3 ∧ varsig 1 ≤ 6 / 5 ∧ varsig 2 ≤ 21 / 5 ∧ varsig 3 ≤ 27 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [varsig] <;> rw [Real.sqrt_le_left (by norm_num)] <;> norm_num

theorem sigmaB_N8_le {dY : ℝ} (_hdY0 : 0 ≤ dY) (hdY : dY ≤ 1 / 16) :
    sigmaB dY (1 / 4) N8 1 ≤ 976 / 75 ∧ sigmaB dY (1 / 4) N8 2 ≤ 20656 / 75 ∧ sigmaB dY (1 / 4) N8 3 ≤ 208448 / 25 := by
  have hs : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hr : √(2 * dY) ≤ 9 / 25 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hr0 : 0 ≤ √(2 * dY) := Real.sqrt_nonneg _
  obtain ⟨v0, v1, v2, v3⟩ := varsig_le
  have w0 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 0
  have w1 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 1
  have w2 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 2
  have w3 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 3
  have hr' : √2 * √dY ≤ 9 / 25 := by rw [← Real.sqrt_mul (by norm_num)]; exact hr
  have hr0' : 0 ≤ √2 * √dY := by positivity
  simp only [sigmaB, N8, Finset.sum_range_succ, Finset.sum_range_zero, hs]
  norm_num [Nat.choose, Nat.factorial]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- **The transfer constant at the top cut**: `τ̂(c, M, ½, ¼; N) ≤ 125U/c` when `N_j ≤ U·j!8^j`, `c ≥ 10⁶`, `M ≥ 3`. -/
theorem tauHat_top_le {c M U : ℝ} (hc : 10 ^ 6 ≤ c) (hM : 3 ≤ M) (hU : 0 ≤ U) {N : ℕ → ℝ}
    (h0 : ∀ j ≤ 3, 0 ≤ N j) (hN : ∀ j ≤ 3, N j ≤ U * ((j.factorial : ℝ) / (1 / 8) ^ j)) :
    tauHat c M (1 / 2) (1 / 4) N ≤ 125 * U / c := by
  have hc0 : 0 < c := by linarith
  have hxd : 1 < M - 1 / 2 := by linarith
  refine (Cvs.L2a.ScaledBandTransfer.tauHat_le_scaled hc0.le (by norm_num) hxd (by norm_num) h0 hN).trans ?_
  rw [show 125 * U / c = U * (125 / c) by ring]
  apply mul_le_mul_of_nonneg_left _ hU
  have hβ := betaW_top_le hM
  have hβ0 := Cvs.L2a.BandTransferKernelForm.betaW_nonneg hxd
  have hch := chirpW_top_le hM
  have hch0 := Cvs.L2a.BandTransferKernelForm.chirpW_nonneg (by norm_num) hxd
  have hY0 : 0 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax M - 1 := by
    linarith [Cvs.L2a.BandTransferBandForm.one_le_Ymax (show 1 < M by linarith)]
  have hY : Cvs.L2a.OrbitGapIntegerM.Ymax M - 1 ≤ 1 / 16 := by
    refine (Cvs.L2a.BandRungOutgoingWave.Ymax_sub_one_le (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
  obtain ⟨s1, s2, s3⟩ := sigmaB_N8_le hY0 hY
  have hN8 : (fun j => (j.factorial : ℝ) / (1 / 8) ^ j) = N8 := rfl
  have n0 : ∀ j ≤ 3, 0 ≤ N8 j := fun j _ => by unfold N8; positivity
  have p1 := Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (dY := Cvs.L2a.OrbitGapIntegerM.Ymax M - 1) (δ := 1 / 4)
    (by norm_num) (j := 1) fun i hi => n0 i (by omega)
  have p2 := Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (dY := Cvs.L2a.OrbitGapIntegerM.Ymax M - 1) (δ := 1 / 4)
    (by norm_num) (j := 2) fun i hi => n0 i (by omega)
  have p3 := Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (dY := Cvs.L2a.OrbitGapIntegerM.Ymax M - 1) (δ := 1 / 4)
    (by norm_num) (j := 3) fun i hi => n0 i (by omega)
  set σ1 := sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax M - 1) (1 / 4) N8 1
  set σ2 := sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax M - 1) (1 / 4) N8 2
  set σ3 := sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax M - 1) (1 / 4) N8 3
  have q12 : √(σ1 * σ2) ≤ 60 := by
    rw [Real.sqrt_le_left (by norm_num)]
    calc σ1 * σ2 ≤ 976 / 75 * (20656 / 75) := mul_le_mul s1 s2 p2 (by norm_num)
      _ ≤ 60 ^ 2 := by norm_num
  have q23 : √(σ2 * σ3) ≤ 1520 := by
    rw [Real.sqrt_le_left (by norm_num)]
    calc σ2 * σ3 ≤ 20656 / 75 * (208448 / 25) := mul_le_mul s2 s3 p3 (by norm_num)
      _ ≤ 1520 ^ 2 := by norm_num
  have e1 : Real.exp (Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2)) ≤ 21 / 16 :=
    (Real.exp_le_exp.2 (by linarith : Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2) ≤ 5 / 21)).trans
      ((exp_le_inv_one_sub (by norm_num)).trans (by norm_num))
  have e2 : Real.exp (2 * Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2)) ≤ 21 / 11 :=
    (Real.exp_le_exp.2 (by linarith : 2 * Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2) ≤ 10 / 21)).trans
      ((exp_le_inv_one_sub (by norm_num)).trans (by norm_num))
  have h5π : 3 ≤ √(5 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hc4 : (c / 4) ^ 2 ≤ √((c * (1 / 2) / 2) ^ 5) := by
    rw [Real.le_sqrt (by positivity) (by positivity), show c * (1 / 2) / 2 = c / 4 by ring]
    have h1 : 1 ≤ c / 4 := by linarith
    calc ((c / 4) ^ 2) ^ 2 = (c / 4) ^ 4 := by ring
      _ ≤ (c / 4) ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  unfold tauHat
  rw [hN8]
  have t1 : 2 * Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * Real.exp (Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2))
      * √(σ1 * σ2) / c ≤ 2 * (10 / 21) * (21 / 16) * 60 / c := by
    gcongr
  have t2 : Cvs.L2a.BandTransferKernelForm.chirpW M (1 / 2) * √(σ2 * σ3) / (2 * c) ≤ 704 / 11025 * 1520 / (2 * c) := by
    gcongr
  have t3 : (Real.exp (2 * Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2)) + 1) * σ3
      / (√(5 * π) * √((c * (1 / 2) / 2) ^ 5)) ≤ 1 / c := by
    have hden : 3 * (c / 4) ^ 2 ≤ √(5 * π) * √((c * (1 / 2) / 2) ^ 5) :=
      mul_le_mul h5π hc4 (by positivity) (by positivity)
    calc (Real.exp (2 * Cvs.L2a.BandTransferKernelForm.betaW M (1 / 2) * (1 / 2)) + 1) * σ3
          / (√(5 * π) * √((c * (1 / 2) / 2) ^ 5))
        ≤ (21 / 11 + 1) * (208448 / 25) / (3 * (c / 4) ^ 2) := by
          apply div_le_div₀ (by positivity) _ (by positivity) hden
          exact mul_le_mul (by linarith) s3 p3 (by norm_num)
      _ ≤ 1 / c := by
          rw [div_le_div_iff₀ (by positivity) hc0]
          nlinarith
  have : 2 * (10 / 21) * (21 / 16) * 60 / c + 704 / 11025 * 1520 / (2 * c) + 1 / c ≤ 125 / c := by
    rw [show 2 * (10 / 21) * (21 / 16) * 60 / c + 704 / 11025 * 1520 / (2 * c) + 1 / c
      = (2 * (10 / 21) * (21 / 16) * 60 + 704 / 11025 * 1520 / 2 + 1) / c by field_simp]
    apply div_le_div_of_nonneg_right _ hc0.le
    norm_num
  linarith

end tau

/-! ### `topE_le` -/

/-- `T_top = (65|ψ(1)| + 750F/√c + 6‖g‖₁/√c)/c`. -/
def Ttop (c : ℝ) (g : ℝ → ℝ) (F : ℝ) : ℝ :=
  (65 * |psi c g 1| + 750 * F / √c + 6 * Cvs.L2a.BandRungOutgoingWave.gL1 g / √c) / c

theorem harmM_ge {M : ℕ} (hM : 3 ≤ M) : 1 / 2 ≤ harmM M := by
  unfold harmM
  have h2 : (2 : ℕ) ∈ Finset.Ico 2 M := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  have := Finset.single_le_sum (f := fun m : ℕ => 1 / (m : ℝ)) (fun m _ => by positivity) h2
  norm_num at this ⊢
  linarith

/-- `κ_A = √((1/16 + 181/924)/π)`: the collar-and-window factor of LBT-h at a top cut with `δ = 1/4`, `M ≥ 3`. -/
noncomputable def kappaA : ℝ := √((1 / 16 + 181 / 924) / π)

/-- **The square-root algebra of LBT-h at the top cut**. -/
theorem top_alg {S IB W PM P c N0 τ G Y M2 : ℝ} (hc : 0 < c) (_hS : 0 ≤ S) (hN0 : 0 ≤ N0) (hτ : 0 ≤ τ)
    (hG : 0 ≤ G) (hW0 : 0 ≤ W) (hPM0 : 0 ≤ PM) (hWP : W ≤ P) (hPMP : PM ≤ P) (hM2 : 8 ≤ M2)
    (hY0 : 0 ≤ Y - 1) (hY : Y - 1 ≤ 1 / (2 * M2)) (hIB : IB ≤ 2 * c * (Y - 1) * N0 ^ 2)
    (hL : S ^ 2 ≤ (2 * π)⁻¹ * IB * W
      + c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W
        + 2 * N0 * τ * √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) * √(W * PM) + τ ^ 2 * G * PM)) :
    S ≤ (kappaA * √c * N0 + τ * √(c * G)) * √P := by
  have hP0 : 0 ≤ P := hW0.trans hWP
  have hpi0 := Real.pi_pos
  set κ : ℝ := kappaA with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ, kappaA]; exact Real.sqrt_nonneg _
  -- `(Y − 1 + 2κ_Sδ)/π ≤ κ²`, exactly
  have hK : (Y - 1 + 2 * (181 / 462) * (1 / 4)) / π ≤ κ ^ 2 := by
    have h1 : Y - 1 ≤ 1 / 16 := hY.trans (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    rw [hκ, kappaA, Real.sq_sqrt (by positivity)]
    apply div_le_div_of_nonneg_right _ hpi0.le
    linarith
  have hA : (2 * π)⁻¹ * IB * W + c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W) ≤ (κ * √c * N0) ^ 2 * P := by
    have h1 : (2 * π)⁻¹ * IB ≤ c * N0 ^ 2 * ((Y - 1) / π) := by
      calc (2 * π)⁻¹ * IB ≤ (2 * π)⁻¹ * (2 * c * (Y - 1) * N0 ^ 2) := mul_le_mul_of_nonneg_left hIB (by positivity)
        _ = c * N0 ^ 2 * ((Y - 1) / π) := by field_simp
    have h2 : (κ * √c * N0) ^ 2 = c * N0 ^ 2 * κ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc.le]; ring
    rw [h2]
    have h3 : (2 * π)⁻¹ * IB * W + c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W)
        ≤ c * N0 ^ 2 * ((Y - 1 + 2 * (181 / 462) * (1 / 4)) / π) * W := by
      have : c * N0 ^ 2 * ((Y - 1 + 2 * (181 / 462) * (1 / 4)) / π) * W
          = c * N0 ^ 2 * ((Y - 1) / π) * W + c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W) := by ring
      rw [this]; nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
    refine h3.trans ?_
    have hcN : 0 ≤ c * N0 ^ 2 := by positivity
    calc c * N0 ^ 2 * ((Y - 1 + 2 * (181 / 462) * (1 / 4)) / π) * W ≤ c * N0 ^ 2 * κ ^ 2 * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hcN) hW0
      _ ≤ c * N0 ^ 2 * κ ^ 2 * P := mul_le_mul_of_nonneg_left hWP (by positivity)
  have hB : c * (2 * N0 * τ * √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) * √(W * PM))
      ≤ 2 * (κ * √c * N0) * (τ * √(c * G)) * P := by
    have hWPM : √(W * PM) ≤ P := by
      calc √(W * PM) ≤ √(P * P) := Real.sqrt_le_sqrt (mul_le_mul hWP hPMP hPM0 hP0)
        _ = P := Real.sqrt_mul_self hP0
    have hs : √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) ≤ κ * √G := by
      rw [show (Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π = (Y - 1 + 2 * (181 / 462) * (1 / 4)) / π * G by ring,
        Real.sqrt_mul (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [show κ = √(κ ^ 2) from (Real.sqrt_sq (by rw [hκ, kappaA]; positivity)).symm]
      exact Real.sqrt_le_sqrt hK
    have e : 2 * (κ * √c * N0) * (τ * √(c * G)) * P = c * (2 * N0 * τ * (κ * √G) * P) := by
      rw [Real.sqrt_mul hc.le]
      have : √c * √c = c := Real.mul_self_sqrt hc.le
      linear_combination (2 * κ * N0 * τ * √G * P) * this
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hc.le
    have h0 : 0 ≤ 2 * N0 * τ := by positivity
    calc 2 * N0 * τ * √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) * √(W * PM)
        ≤ 2 * N0 * τ * (κ * √G) * P :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs h0) hWPM (Real.sqrt_nonneg _)
            (mul_nonneg h0 (mul_nonneg hκ0 (Real.sqrt_nonneg _)))
      _ = 2 * N0 * τ * (κ * √G) * P := rfl
  have hC : c * (τ ^ 2 * G * PM) ≤ (τ * √(c * G)) ^ 2 * P := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : c * (τ ^ 2 * G * PM) = τ ^ 2 * (c * G) * PM := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hPMP (by positivity)
  have hsq : S ^ 2 ≤ ((κ * √c * N0 + τ * √(c * G)) * √P) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hP0]
    have e : (κ * √c * N0 + τ * √(c * G)) ^ 2 * P = (κ * √c * N0) ^ 2 * P
        + 2 * (κ * √c * N0) * (τ * √(c * G)) * P + (τ * √(c * G)) ^ 2 * P := by ring
    have e2 : c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W
        + 2 * N0 * τ * √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) * √(W * PM) + τ ^ 2 * G * PM)
        = c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W)
          + c * (2 * N0 * τ * √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) * √(W * PM))
          + c * (τ ^ 2 * G * PM) := by ring
    rw [e]
    rw [e2] at hL
    calc S ^ 2 ≤ _ := hL
      _ = ((2 * π)⁻¹ * IB * W + c * (2 * (181 / 462) / π * (1 / 4) * N0 ^ 2 * W))
          + c * (2 * N0 * τ * √((Y - 1 + 2 * (181 / 462) * (1 / 4)) * G / π) * √(W * PM))
          + c * (τ ^ 2 * G * PM) := by ring
      _ ≤ _ := add_le_add (add_le_add hA hB) hC
  have hR : 0 ≤ (κ * √c * N0 + τ * √(c * G)) * √P :=
    mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hκ0 (Real.sqrt_nonneg _)) hN0)
      (mul_nonneg hτ (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  exact le_of_pow_le_pow_left₀ two_ne_zero hR hsq

/-- `|A| ≤ 2√(c/π)|ψ(1)|` for an even rung with `ψ = μg` and `λ ≥ ½`. -/
theorem abs_ampl_le {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hlam : 1 / 2 ≤ (μ * √(c / (2 * π))) ^ 2) :
    |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| ≤ 2 * √(c / π) * |psi c g 1| := by
  obtain ⟨hμ0, hinv⟩ := Cvs.L2a.BandRungData.inv_abs_le_of_half hc hlam
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hA : Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g = 2 * g 1 := by
    unfold Cvs.Prolate.RungOrthogonalityAtInfinity.ampl; rw [heven 1 h1]; ring
  have hg1 : |g 1| = |psi c g 1| * (1 / |μ|) := by
    rw [hμ 1 h1, abs_mul]; field_simp
  rw [hA, abs_mul, abs_two, hg1]
  have := mul_le_mul_of_nonneg_left hinv (abs_nonneg (psi c g 1))
  nlinarith [abs_nonneg (psi c g 1)]

/-- The `A`-part arithmetic: `0.287·r·N₀ ≤ (64.8ψ + 9.2F/r + 5.2G/r)/c` for `c = r²`. -/
theorem partA_le {c r ψ F G1 A : ℝ} (hc : 0 < c) (hr : r * r = c) (hr0 : 0 < r) (hspi : 1772 / 1000 ≤ √π)
    (hA : |A| ≤ 2 * r / √π * ψ) (hψ : 0 ≤ ψ) (hF : 0 ≤ F) (hG : 0 ≤ G1) :
    287 / 1000 * r * (200 * |A| / c ^ 2 + 32 * F / c ^ 2 + 18 * G1 / c ^ 2)
      ≤ (648 / 10 * ψ + 92 / 10 * F / r + 52 / 10 * G1 / r) / c := by
  have hpi : 0 < √π := by positivity
  have hkey : 287 / 1000 * 200 * |A| ≤ 648 / 10 * ψ * r := by
    have h1 : 2 * r / √π * ψ ≤ 2 * r / (1772 / 1000) * ψ := by gcongr
    nlinarith [hA.trans h1]
  have e1 : 287 / 1000 * r * (200 * |A| / c ^ 2 + 32 * F / c ^ 2 + 18 * G1 / c ^ 2)
      = (287 / 1000 * 200 * |A| + 287 / 1000 * 32 * F + 287 / 1000 * 18 * G1) / (r * c) := by
    rw [← hr]; field_simp
  have e2 : (648 / 10 * ψ + 92 / 10 * F / r + 52 / 10 * G1 / r) / c
      = (648 / 10 * ψ * r + 92 / 10 * F + 52 / 10 * G1) / (r * c) := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-- The transfer-part arithmetic: `125U/c·√(6J/(M²−1)) ≤ (708F/r + G/(100r))/c`. -/
theorem partT_le {c r F G1 H J Mr τ : ℝ} (hc : 10 ^ 6 ≤ c) (hr : r * r = c) (hr0 : 0 < r) (hM : 3 ≤ Mr)
    (hF : 0 ≤ F) (hG : 0 ≤ G1) (hH0 : 0 ≤ H) (hH : H ≤ (Mr - 2) / 2) (_hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1)
    (hτ : τ ≤ 125 * (8 * H * F / c + 97 * G1 / c ^ 2) / c) (_hτ0 : 0 ≤ τ) :
    τ * √(6 * J / (Mr ^ 2 - 1)) ≤ (708 * F / r + 1 / 100 * G1 / r) / c := by
  have hc0 : 0 < c := by linarith
  have hp : 0 < Mr ^ 2 - 1 := by nlinarith
  have hs8 : √8 ≤ √(Mr ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have hs8' : 2828 / 1000 ≤ √8 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsp : 0 < √(Mr ^ 2 - 1) := Real.sqrt_pos.2 hp
  have hHs : H ≤ √(Mr ^ 2 - 1) / 2 := by
    refine hH.trans ?_
    have : Mr - 2 ≤ √(Mr ^ 2 - 1) := by
      rw [Real.le_sqrt (by linarith) hp.le]; nlinarith
    linarith
  have h6J : 6 * J ≤ 2 * c := by linarith
  have hsq : √(6 * J / (Mr ^ 2 - 1)) ≤ √2 * r / √(Mr ^ 2 - 1) := by
    rw [Real.sqrt_div' _ hp.le]
    apply div_le_div_of_nonneg_right _ hsp.le
    have e2 : √2 * r = √(2 * c) := by
      rw [Real.sqrt_mul (by norm_num), ← hr, Real.sqrt_mul_self hr0.le]
    rw [e2]
    exact Real.sqrt_le_sqrt h6J
  have hs2 : √2 ≤ 1415 / 1000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hU0 : 0 ≤ 8 * H * F / c + 97 * G1 / c ^ 2 := by positivity
  calc τ * √(6 * J / (Mr ^ 2 - 1)) ≤ 125 * (8 * H * F / c + 97 * G1 / c ^ 2) / c * (√2 * r / √(Mr ^ 2 - 1)) :=
        mul_le_mul hτ hsq (Real.sqrt_nonneg _) (by positivity)
    _ = 125 * √2 * r * (8 * (H / √(Mr ^ 2 - 1)) * F / c + 97 * G1 / (c ^ 2 * √(Mr ^ 2 - 1))) / c := by
        field_simp
    _ ≤ 125 * (1415 / 1000) * r * (8 * (1 / 2) * F / c + 97 * G1 / (c ^ 2 * (2828 / 1000))) / c := by
        have h1 : H / √(Mr ^ 2 - 1) ≤ 1 / 2 := by rw [div_le_iff₀ hsp]; linarith
        have h2 : 97 * G1 / (c ^ 2 * √(Mr ^ 2 - 1)) ≤ 97 * G1 / (c ^ 2 * (2828 / 1000)) := by
          gcongr; linarith
        gcongr
    _ ≤ (708 * F / r + 1 / 100 * G1 / r) / c := by
        apply div_le_div_of_nonneg_right _ hc0.le
        have e : 125 * (1415 / 1000) * r * (8 * (1 / 2) * F / c + 97 * G1 / (c ^ 2 * (2828 / 1000)))
            = 7075 / 10 * F / r + (125 * (1415 / 1000) * 97 / (2828 / 1000)) * G1 / (r * c) := by
          rw [← hr]; field_simp; ring
        rw [e]
        have h3 : (125 * (1415 / 1000) * 97 / (2828 / 1000)) * G1 / (r * c) ≤ 1 / 100 * G1 / r := by
          rw [div_le_div_iff₀ (by positivity) hr0]
          have : 0 ≤ G1 * r := by positivity
          nlinarith
        have h4 : 7075 / 10 * F / r ≤ 708 * F / r := by gcongr; norm_num
        linarith

set_option maxHeartbeats 4000000 in
/-- **Exact form**: `|topE| ≤ (κ_A√c·N₀ + τ̂·√(6J/(M² − 1)))·√P` with `N₀ = N0top` (uniform in `M`) and
`τ̂ = τ̂(c, M, ½, ¼; N_top)`, for `c ≥ 80` and every integer `M ≥ 3`. -/
theorem topE_le_exact {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {gj gj₁ gj₂ : ℝ → ℝ} {χj F : ℝ} {M : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc80 : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2)
    (hσj : c ^ 2 - χj ≤ 10 * c) (hF : ∀ t : ℝ, |psi c gj t| ≤ F) (hM : 3 ≤ M) :
    |Cvs.L2a.BandRungOutgoingWave.topE c gj a χ g M|
      ≤ (kappaA * √c * N0top c gj F
          + Cvs.L2a.BandTransferBandForm.tauHat c (M : ℝ) (1 / 2) (1 / 4) (Ntop c gj F M)
            * √(6 * (Fintype.card ι : ℝ) / ((M : ℝ) ^ 2 - 1)))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have hψF : |psi c gj 1| ≤ F := hF 1
  have hG0 := Cvs.L2a.BandRungOutgoingWave.gL1_nonneg (g := gj)
  set Y := Cvs.L2a.OrbitGapIntegerM.Ymax (M : ℝ) with hYdef
  have hY1 : 1 ≤ Y := Cvs.L2a.BandRungOutgoingWave.one_le_Ymax hM1
  have hY : Y - 1 ≤ 1 / (2 * ((M : ℝ) ^ 2 - 1)) := Cvs.L2a.BandRungOutgoingWave.Ymax_sub_one_le hM1
  -- the band multiplier and LBT-h at the top cut
  have hμ := nuTop_isBandMult hgj hgj₁ hgj₂c hangj hevenj hc80 hχj0 hχjc hσj hF hM
  set μ : ℝ → ℂ := fun η => Cvs.L2a.BandRungOutgoingWave.nuTop c gj M (c * η) with hμdef
  have hmeasB : MeasurableSet (Cvs.L2a.BandRungOutgoingWave.bandB c Y) := measurableSet_Icc.union measurableSet_Icc
  have hBc : ∀ ξ, |ξ| ∈ Icc c (c * Y) → ξ ∈ Cvs.L2a.BandRungOutgoingWave.bandB c Y := by
    intro ξ hξ
    rcases le_or_gt 0 ξ with h | h
    · rw [abs_of_nonneg h] at hξ; exact Or.inr hξ
    · rw [abs_of_neg h] at hξ; exact Or.inl ⟨by linarith [hξ.2], by linarith [hξ.1]⟩
  have hmemB : ∀ ξ ∈ Cvs.L2a.BandRungOutgoingWave.bandB c Y, ξ / c ∈ Cvs.L2a.BandTransferBandForm.bandRg (1 / 4) Y := by
    intro ξ hξ
    have h := Cvs.L2a.BandRungOutgoingWave.mem_bandB_abs hc0 hξ
    refine ⟨?_, ?_⟩
    · rw [abs_div, abs_of_pos hc0, le_div_iff₀ hc0]; nlinarith [h.1]
    · rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]; nlinarith [h.2]
  have hcontB : ContinuousOn (fun ξ => ‖μ (ξ / c)‖ ^ 2) (Cvs.L2a.BandRungOutgoingWave.bandB c Y) := by
    intro ξ hξ
    have h1 := (hμ.d0 (ξ / c) (hmemB ξ hξ)).continuousAt
    have h2 : ContinuousAt (fun ξ : ℝ => ξ / c) ξ := continuousAt_id.div_const c
    exact (((ContinuousAt.comp (g := μ) (f := fun t : ℝ => t / c) h1 h2).norm).pow 2).continuousWithinAt
  have hBi : IntegrableOn (fun ξ => ‖μ (ξ / c)‖ ^ 2) (Cvs.L2a.BandRungOutgoingWave.bandB c Y) :=
    hcontB.integrableOn_compact (isCompact_Icc.union isCompact_Icc)
  have hL := Cvs.L2a.BandTransferBandForm.lbt_band_gen a hg hg₁ hg₂c hang hc80 hχ0 hχc (X := (M : ℝ)) (x₀ := (M : ℝ))
    (d := 1 / 2) (δ := 1 / 4) (by linarith) hmass ⟨by linarith, le_rfl⟩ (by norm_num) (by linarith)
    (by norm_num) (by norm_num) hμ hmeasB hBc hBi
  have hfun : (fun ξ => μ (ξ / c)) = Cvs.L2a.BandRungOutgoingWave.nuTop c gj M := by
    funext ξ; simp only [hμdef]; rw [mul_div_cancel₀ ξ hc0.ne']
  rw [hfun] at hL
  -- `|topE| ≤ ‖Σ aᵢ Sᵢ‖`
  have htop : |Cvs.L2a.BandRungOutgoingWave.topE c gj a χ g M|
      ≤ ‖∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuTop c gj M) c (χ i) (g i) M‖ :=
    Complex.abs_re_le_norm _
  -- the band integral of the multiplier
  have hN00 : 0 ≤ Ntop c gj F M 0 := (Cvs.L2a.BandTransferBandForm.N_nonneg (by norm_num) hY1 hμ).1
  have hIB : ∫ ξ in Cvs.L2a.BandRungOutgoingWave.bandB c Y, ‖μ (ξ / c)‖ ^ 2 ≤ 2 * c * (Y - 1) * Ntop c gj F M 0 ^ 2 := by
    obtain ⟨hk, hv⟩ := Cvs.L2a.BandRungOutgoingWave.integral_band_const (Ntop c gj F M 0 ^ 2) hc0 hY1
    rw [← hv]
    refine setIntegral_mono_on hBi hk hmeasB fun ξ hξ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (hμ.bd (ξ / c) (hmemB ξ hξ)).1 2
  -- the span masses
  set W := ∫ x in ((M : ℝ) - 1 / 2)..((M : ℝ) + 1 / 2), (∑ i, a i * psi c (g i) x) ^ 2 with hWdef
  set PM := ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2 with hPMdef
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hPdef
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hPM0 : 0 ≤ PM := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
    (intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _)
  have hψ2 : ∀ i, IntegrableOn (fun x => psi c (g i) x ^ 2) (Ioi 1) := fun i =>
    (memLp_two_iff_integrable_sq ((Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i)
      (hang i)).2.2.1.aestronglyMeasurable)).mp (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i)
      (hang i) hc0)
  have hΦ2 : IntegrableOn (fun x => (∑ i, a i * psi c (g i) x) ^ 2) (Ioi 1) := by
    have hm : MemLp (fun x => ∑ i, a i * psi c (g i) x) 2 (volume.restrict (Ioi 1)) := by
      have := memLp_finsetSum' Finset.univ fun i _ =>
        (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc0).const_mul (a i)
      refine this.ae_eq (ae_of_all _ fun x => ?_)
      simp [Finset.sum_apply]
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
  have hWP : W ≤ P := by
    rw [hWdef, intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set hΦ2 (ae_of_all _ fun x => sq_nonneg _)
      (ae_of_all _ fun x hx => show 1 < x by linarith [hx.1])
  have hPMP : PM ≤ P := by
    rw [hPdef, Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc0 hχi]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (hψ2 i) (ae_of_all _ fun x => sq_nonneg _)
      (ae_of_all _ fun x hx => show 1 < x from hx.1)
  -- the transfer constant
  set G := 6 * (Fintype.card ι : ℝ) / (c * ((M : ℝ) ^ 2 - 1)) with hGdef
  have hp : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  have hG : 0 ≤ G := by positivity
  have hN0 : ∀ j ≤ 3, 0 ≤ Ntop c gj F M j := fun j hj => by
    obtain ⟨n0, n1, n2, n3⟩ := Cvs.L2a.BandTransferBandForm.N_nonneg (by norm_num) hY1 hμ
    interval_cases j <;> assumption
  set τ := Cvs.L2a.BandTransferBandForm.tauHat c (M : ℝ) (1 / 2) (1 / 4) (Ntop c gj F M) with hτdef
  have hτ0 : 0 ≤ τ := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg hc0.le (by norm_num) (by linarith) (by norm_num) hN0
  -- the algebra
  have hS := top_alg (S := ‖∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.BandRungOutgoingWave.nuTop c gj M) c (χ i) (g i) M‖)
    (IB := ∫ ξ in Cvs.L2a.BandRungOutgoingWave.bandB c Y, ‖μ (ξ / c)‖ ^ 2)
    (W := W) (PM := PM) (P := P) (N0 := Ntop c gj F M 0) (τ := τ) (G := G) (Y := Y) (M2 := (M : ℝ) ^ 2 - 1)
    hc0 (norm_nonneg _) hN00 hτ0 hG hW0 hPM0 hWP hPMP (by nlinarith) (by linarith) hY hIB
    hL
  have hN0eq : Ntop c gj F M 0 = N0top c gj F := by simp [Ntop]
  have hcG : c * G = 6 * (Fintype.card ι : ℝ) / ((M : ℝ) ^ 2 - 1) := by rw [hGdef]; field_simp
  rw [hN0eq, hcG] at hS
  exact htop.trans hS

set_option maxHeartbeats 4000000 in
/-- **`topE_le`**: `|topE| ≤ T_top·√P`, `T_top = (65|ψ_j(1)| + 750F/√c + 6‖g_j‖₁/√c)/c`, uniformly in `M ≥ 3`,
for `c ≥ 10⁶`, a span of at most `c/4 + 1` rungs and Landau's `λ_j ≥ ½`. -/
theorem topE_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {gj gj₁ gj₂ : ℝ → ℝ} {χj μj F : ℝ} {M : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 6 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hχj0 : 0 ≤ χj) (hχjc : χj < c ^ 2)
    (hσj : c ^ 2 - χj ≤ 10 * c) (hμj : ∀ s ∈ Icc (-1 : ℝ) 1, psi c gj s = μj * gj s)
    (hlam : 1 / 2 ≤ (μj * √(c / (2 * π))) ^ 2) (hF : ∀ t : ℝ, |psi c gj t| ≤ F) (hM : 3 ≤ M) :
    |Cvs.L2a.BandRungOutgoingWave.topE c gj a χ g M|
      ≤ Ttop c gj F * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc80 : 80 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hE := topE_le_exact a hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hmass hgj hgj₁ hgj₂c hangj hevenj hχj0 hχjc
    hσj hF hM
  refine hE.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have hψF : |psi c gj 1| ≤ F := hF 1
  have hG0 := Cvs.L2a.BandRungOutgoingWave.gL1_nonneg (g := gj)
  have hY1 : 1 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax (M : ℝ) := Cvs.L2a.BandRungOutgoingWave.one_le_Ymax (by linarith)
  have hμ := nuTop_isBandMult hgj hgj₁ hgj₂c hangj hevenj hc80 hχj0 hχjc hσj hF hM
  set U := Utop c gj F M with hUdef
  have hH := harmM_le (by omega : 2 ≤ M)
  have hH2 := harmM_ge hM
  have hU0 : 0 ≤ U := by rw [hUdef]; unfold Utop; have := harmM_nonneg M; positivity
  have hsc : (1000 : ℝ) ≤ √c := by rw [Real.le_sqrt (by norm_num) hc0.le]; linarith
  have hA := abs_ampl_le hc0 hevenj hμj hlam
  have hspi : √(c / π) ≤ √c := Real.sqrt_le_sqrt (div_le_self hc0.le (by linarith [Real.pi_gt_three]))
  have hN0U : N0top c gj F ≤ U := by
    rw [hUdef]; unfold N0top Utop
    have h1 : |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl gj| ≤ 2 * √c * F := by
      calc |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl gj| ≤ 2 * √(c / π) * |psi c gj 1| := hA
        _ ≤ 2 * √c * F := by gcongr
    have h2 : 200 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl gj| / c ^ 2 + 32 * F / c ^ 2 ≤ 8 * harmM M * F / c := by
      have hsc2 : √c * √c = c := Real.mul_self_sqrt hc0.le
      rw [← add_div, div_le_div_iff₀ (by positivity) hc0]
      have h3 : 200 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl gj| + 32 * F ≤ (400 * √c + 32) * F := by nlinarith
      have h4 : (400 * √c + 32) * F * c ≤ 8 * harmM M * F * c ^ 2 := by
        have h5 : 400 * √c + 32 ≤ 4 * c := by nlinarith
        have h6 : 4 * c ≤ 8 * harmM M * c := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right (h5.trans h6) (mul_nonneg hF0 hc0.le)]
      nlinarith [mul_le_mul_of_nonneg_right h3 hc0.le]
    have h3 : 18 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / c ^ 2 ≤ 97 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / c ^ 2 := by
      gcongr; norm_num
    linarith
  have hN0 : ∀ j ≤ 3, 0 ≤ Ntop c gj F M j := fun j hj => by
    obtain ⟨n0, n1, n2, n3⟩ := Cvs.L2a.BandTransferBandForm.N_nonneg (by norm_num) hY1 hμ
    interval_cases j <;> assumption
  have hNU : ∀ j ≤ 3, Ntop c gj F M j ≤ U * ((j.factorial : ℝ) / (1 / 8) ^ j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp only [Ntop, ite_eq_left]; simpa using hN0U
    · simp only [Ntop, ite_eq_right h.ne', hUdef]
      rw [one_div, inv_pow, div_inv_eq_mul]; ring_nf; exact le_rfl
  have hτ := tauHat_top_le hc hM3 hU0 hN0 hNU
  set τ := Cvs.L2a.BandTransferBandForm.tauHat c (M : ℝ) (1 / 2) (1 / 4) (Ntop c gj F M) with hτdef
  have hτ0 : 0 ≤ τ := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg hc0.le (by norm_num) (by linarith) (by norm_num) hN0
  have hκ : kappaA ≤ 287 / 1000 := by
    unfold kappaA
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d2]
  set r := √c with hr
  have hr2 : r * r = c := Real.mul_self_sqrt hc0.le
  have hr0 : 0 < r := by linarith
  have hspi' : √π ≥ 1772 / 1000 := by
    rw [ge_iff_le, Real.le_sqrt (by norm_num) Real.pi_pos.le]; nlinarith [Real.pi_gt_d2]
  have hA' : |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl gj| ≤ 2 * r / √π * |psi c gj 1| := by
    refine hA.trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ Real.pi_pos.le, ← hr]; ring
  have hPA := partA_le hc0 hr2 hr0 hspi' hA' (abs_nonneg _) hF0 hG0
  have hτ' : τ ≤ 125 * (8 * harmM M * F / c + 97 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / c ^ 2) / c := by
    simpa [hUdef, Utop] using hτ
  have hPT := partT_le hc hr2 hr0 hM3 hF0 hG0 (harmM_nonneg M) hH (Nat.cast_nonneg _) hJ hτ' hτ0
  have hN00 : 0 ≤ N0top c gj F := by
    have := (Cvs.L2a.BandTransferBandForm.N_nonneg (by norm_num) hY1 hμ).1
    simpa [Ntop] using this
  have hκN : kappaA * r * N0top c gj F ≤ 287 / 1000 * r * N0top c gj F := by gcongr
  unfold N0top at hκN hN00 ⊢
  calc kappaA * r * (200 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl gj| / c ^ 2 + 32 * F / c ^ 2
          + 18 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / c ^ 2) + τ * √(6 * (Fintype.card ι : ℝ) / ((M : ℝ) ^ 2 - 1))
      ≤ (648 / 10 * |psi c gj 1| + 92 / 10 * F / r + 52 / 10 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / r) / c
        + (708 * F / r + 1 / 100 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / r) / c := add_le_add (hκN.trans hPA) hPT
    _ ≤ Ttop c gj F := by
        unfold Ttop
        rw [← hr, ← add_div]
        apply div_le_div_of_nonneg_right _ hc0.le
        have h1 : 92 / 10 * F / r + 708 * F / r ≤ 750 * F / r := by
          rw [← add_div]; gcongr; linarith
        have h2 : 52 / 10 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / r + 1 / 100 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / r
            ≤ 6 * Cvs.L2a.BandRungOutgoingWave.gL1 gj / r := by
          rw [← add_div]; gcongr; linarith
        have h3 : 648 / 10 * |psi c gj 1| ≤ 65 * |psi c gj 1| := by nlinarith [abs_nonneg (psi c gj 1)]
        linarith

/-- **The residual envelope**: with `F = K_A|ψ(1)|` and `‖g‖₁ ≤ 2K_A√(c/π)|ψ(1)|`,
`T_top ≤ 73K_A|ψ(1)|/c ≤ 10⁶K_A|ψ(1)|c^{−3/4}`. -/
theorem Ttop_le_band {c KA : ℝ} {g : ℝ → ℝ} (hc : 10 ^ 6 ≤ c) (hKA : 1 ≤ KA)
    (hG : Cvs.L2a.BandRungOutgoingWave.gL1 g ≤ 2 * KA * √(c / π) * |psi c g 1|) :
    Ttop c g (KA * |psi c g 1|) ≤ 10 ^ 6 * KA * |psi c g 1| * c ^ (-(3 / 4 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hψ := abs_nonneg (psi c g 1)
  have hsc : (1000 : ℝ) ≤ √c := by rw [Real.le_sqrt (by norm_num) hc0.le]; linarith
  have hs0 : 0 < √c := by linarith
  have hspi : 1772 / 1000 ≤ √π := by
    rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]; nlinarith [Real.pi_gt_d2]
  have h1 : 6 * Cvs.L2a.BandRungOutgoingWave.gL1 g / √c ≤ 12 / (1772 / 1000) * KA * |psi c g 1| := by
    have e : √(c / π) = √c / √π := Real.sqrt_div' _ Real.pi_pos.le
    rw [div_le_iff₀ hs0]
    calc 6 * Cvs.L2a.BandRungOutgoingWave.gL1 g ≤ 6 * (2 * KA * (√c / √π) * |psi c g 1|) := by rw [← e]; linarith
      _ = 12 * KA * |psi c g 1| * √c / √π := by ring
      _ ≤ 12 * KA * |psi c g 1| * √c / (1772 / 1000) := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hspi
      _ = 12 / (1772 / 1000) * KA * |psi c g 1| * √c := by ring
  have h2 : 750 * (KA * |psi c g 1|) / √c ≤ 750 / 1000 * KA * |psi c g 1| := by
    rw [div_le_iff₀ hs0]
    have : 0 ≤ 750 * (KA * |psi c g 1|) := by positivity
    nlinarith
  have h3 : 65 * |psi c g 1| ≤ 65 * KA * |psi c g 1| := by nlinarith
  have hT : Ttop c g (KA * |psi c g 1|) ≤ 73 * KA * |psi c g 1| / c := by
    unfold Ttop
    apply div_le_div_of_nonneg_right _ hc0.le
    have : 65 * KA * |psi c g 1| + 750 / 1000 * KA * |psi c g 1| + 12 / (1772 / 1000) * KA * |psi c g 1|
        ≤ 73 * KA * |psi c g 1| := by
      have : 0 ≤ KA * |psi c g 1| := by positivity
      nlinarith
    linarith
  refine hT.trans ?_
  have hr : c ^ (-(3 / 4 : ℝ)) = c ^ (1 / 4 : ℝ) / c := by
    rw [show (-(3 / 4 : ℝ)) = 1 / 4 - 1 by norm_num, Real.rpow_sub hc0, Real.rpow_one]
  have h14 : (1 : ℝ) ≤ c ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  rw [hr]
  have : 0 ≤ KA * |psi c g 1| := by positivity
  rw [div_le_iff₀ hc0]
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left h14 this]

end Cvs.L2a.TopCutCouplingBound

end
