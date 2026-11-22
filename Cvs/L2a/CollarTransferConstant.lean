import Mathlib
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.ScaledBandTransfer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The transfer constant on the collar schedule

With `δ = c^{−1/3}`, `d = 1/2` and `N_j = j!·4^j`, `σ_j ≤ C_jδ^{1/2−j}` (`C₁ ≤ 9.7`, `C₂ ≤ 85.3`, `C₃ ≤ 1077`),
`β_W = 6/5`, `Y'_W = 448/1089`, so `τ̄(c, 1/2, δ, 1/4) ≤ 64c^{−1/3}` for `c ≥ 10⁶`.
-/

namespace Cvs.L2a.CollarTransferConstant

open Real
open Cvs.L2a.BandTransferBandForm (sigmaB varsig tauHat)

/-- `√(2ΔY) ≤ 0.5564` for `ΔY = Y_max(2) − 1 = 2/√3 − 1`. -/
theorem sqrt_two_dY_le : √(2 * (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1)) ≤ 0.5564 := by
  have h3 : (1.732 : ℝ) ≤ √3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hY : Cvs.L2a.OrbitGapIntegerM.Ymax 2 = 2 / √3 := by
    unfold Cvs.L2a.OrbitGapIntegerM.Ymax; norm_num
  have hY' : Cvs.L2a.OrbitGapIntegerM.Ymax 2 ≤ 2 / 1.732 := by
    rw [hY]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
  refine (Real.sqrt_le_sqrt (?_ : _ ≤ (0.5564 : ℝ) ^ 2)).trans_eq (Real.sqrt_sq (by norm_num))
  norm_num at hY' ⊢
  linarith

/-- `ς₀ ≤ 0.626`, `ς₁ ≤ 1.1953`, `ς₂ ≤ 4.1404`, `ς₃ ≤ 26.833`. -/
theorem varsig_le : varsig 0 ≤ 0.626 ∧ varsig 1 ≤ 1.1953 ∧ varsig 2 ≤ 4.1404 ∧ varsig 3 ≤ 26.833 := by
  have k : ∀ {x y : ℝ}, 0 ≤ y → x ≤ y ^ 2 → √x ≤ y := fun hy h =>
    (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hy)
  simp only [varsig]
  exact ⟨k (by norm_num) (by norm_num), k (by norm_num) (by norm_num), k (by norm_num) (by norm_num),
    k (by norm_num) (by norm_num)⟩

section sigma

variable {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)

include hp0 in
/-- `σ_jδ^{j−1/2}` at `δ = p²`, `N_j = j!·4^j`, as a polynomial in `p`. -/
theorem sigma_eq (dY : ℝ) :
    sigmaB dY (p ^ 2) (fun j => (j.factorial : ℝ) / (1 / 4) ^ j) 1 * p
      = 4 * √(2 * dY) * p + 8 * varsig 0 * p ^ 2 + 2 * varsig 1 ∧
    sigmaB dY (p ^ 2) (fun j => (j.factorial : ℝ) / (1 / 4) ^ j) 2 * p ^ 3
      = 32 * √(2 * dY) * p ^ 3 + 64 * varsig 0 * p ^ 4 + 16 * varsig 1 * p ^ 2 + 2 * varsig 2 ∧
    sigmaB dY (p ^ 2) (fun j => (j.factorial : ℝ) / (1 / 4) ^ j) 3 * p ^ 5
      = 384 * √(2 * dY) * p ^ 5 + 768 * varsig 0 * p ^ 6 + 192 * varsig 1 * p ^ 4
        + 24 * varsig 2 * p ^ 2 + 2 * varsig 3 := by
  simp only [sigmaB, Finset.sum_range_succ, Finset.sum_range_zero, Real.sqrt_sq hp0.le]
  generalize √(2 * dY) = a
  norm_num [Nat.factorial, Nat.choose]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

include hp0 hp1 in
/-- `σ₁δ^{1/2} ≤ 9.7`, `σ₂δ^{3/2} ≤ 85.3`, `σ₃δ^{5/2} ≤ 1077` at `ΔY = Y_max(2) − 1`, `δ = p²`, `N_j = j!·4^j`. -/
theorem sigma_le :
    sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1) (p ^ 2) (fun j => (j.factorial : ℝ) / (1 / 4) ^ j) 1 * p ≤ 9.7 ∧
    sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1) (p ^ 2) (fun j => (j.factorial : ℝ) / (1 / 4) ^ j) 2 * p ^ 3
      ≤ 85.3 ∧
    sigmaB (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1) (p ^ 2) (fun j => (j.factorial : ℝ) / (1 / 4) ^ j) 3 * p ^ 5
      ≤ 1077 := by
  obtain ⟨e1, e2, e3⟩ := sigma_eq hp0 (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1)
  rw [e1, e2, e3]
  have ha := sqrt_two_dY_le
  have ha0 := Real.sqrt_nonneg (2 * (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1))
  generalize √(2 * (Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1)) = a at *
  obtain ⟨v0, v1, v2, v3⟩ := varsig_le
  have w0 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 0
  have w1 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 1
  have w2 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 2
  have k : ∀ {x B : ℝ} (n : ℕ), 0 ≤ x → x ≤ B → x * p ^ n ≤ B := fun n hx hB =>
    (mul_le_of_le_one_right hx (pow_le_one₀ hp0.le hp1)).trans hB
  have a1 := k 1 ha0 ha
  have a3 := k 3 ha0 ha
  have a5 := k 5 ha0 ha
  have b2 := k 2 w0 v0
  have b4 := k 4 w0 v0
  have b6 := k 6 w0 v0
  have c2 := k 2 w1 v1
  have c4 := k 4 w1 v1
  have d2 := k 2 w2 v2
  simp only [pow_one] at a1
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end sigma

/-- `β_W(2, 1/2) = 6/5`. -/
theorem betaW_two_half : Cvs.L2a.BandTransferKernelForm.betaW 2 (1 / 2) = 6 / 5 := by
  unfold Cvs.L2a.BandTransferKernelForm.betaW; norm_num

/-- `Y'_W(2, 1/2) = 448/1089`. -/
theorem chirpW_two_half : Cvs.L2a.BandTransferKernelForm.chirpW 2 (1 / 2) = 448 / 1089 := by
  unfold Cvs.L2a.BandTransferKernelForm.chirpW; norm_num

/-- `e^{n/10} ≤ (10/9)^n`. -/
theorem exp_le_pow (n : ℕ) : Real.exp (n / 10) ≤ (10 / 9) ^ n := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 10) (by norm_num) (by norm_num)
  have e : Real.exp (n / 10) = Real.exp (1 / 10) ^ n := by rw [← Real.exp_nat_mul]; ring_nf
  rw [e]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (h.le.trans_eq (by norm_num)) n

/-- **The transfer constant on the schedule**: `τ̄(c, 1/2, c^{−1/3}, 1/4) ≤ 64c^{−1/3}` for `c ≥ 10⁶`. -/
theorem tauBar_schedule_le {c : ℝ} (hc : 10 ^ 6 ≤ c) :
    Cvs.L2a.BandRungOutgoingWave.tauBar c (1 / 2) (Cvs.L2a.BandECouplingCollar.deltaS c) (1 / 4)
      ≤ 64 * c ^ (-(1 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  set p := √(Cvs.L2a.BandECouplingCollar.deltaS c)
  have hd0 := Cvs.L2a.BandECouplingCollar.deltaS_pos hc0
  have hd1 := Cvs.L2a.BandECouplingCollar.deltaS_lt_one (show 1 < c by linarith)
  have hp0 : 0 < p := Real.sqrt_pos.mpr hd0
  have hδ : Cvs.L2a.BandECouplingCollar.deltaS c = p ^ 2 := (Real.sq_sqrt hd0.le).symm
  have hp1 : p ≤ 1 := by nlinarith
  have hcp : c * p ^ 6 = 1 := by
    have : p ^ 6 = c ^ (-1 : ℝ) := by
      rw [show p ^ 6 = (p ^ 2) ^ (3 : ℕ) by ring, ← hδ, Cvs.L2a.BandECouplingCollar.deltaS,
        ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      norm_num
    rw [this, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
  have hp2 : p ^ 2 ≤ 1 / 100 := by
    have h6 : (p ^ 2) ^ 3 ≤ (1 / 100) ^ 3 := by nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h6
  have hinv : 1 / c = p ^ 6 := by field_simp; linarith
  rw [show c ^ (-(1 / 3 : ℝ)) = Cvs.L2a.BandECouplingCollar.deltaS c from rfl, hδ]
  unfold Cvs.L2a.BandRungOutgoingWave.tauBar tauHat
  rw [betaW_two_half, chirpW_two_half]
  obtain ⟨s1, s2, s3⟩ := sigma_le hp0 hp1
  set N : ℕ → ℝ := fun j => (j.factorial : ℝ) / (1 / 4) ^ j
  have hN : ∀ i ≤ 3, 0 ≤ N i := fun i _ => by positivity
  set dY := Cvs.L2a.OrbitGapIntegerM.Ymax 2 - 1
  have g1 : 0 ≤ sigmaB dY (p ^ 2) N 1 := Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (by positivity) fun i hi => hN i (by omega)
  have g2 : 0 ≤ sigmaB dY (p ^ 2) N 2 := Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (by positivity) fun i hi => hN i (by omega)
  have g3 : 0 ≤ sigmaB dY (p ^ 2) N 3 := Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (by positivity) fun i hi => hN i (by omega)
  set σ1 := sigmaB dY (p ^ 2) N 1
  set σ2 := sigmaB dY (p ^ 2) N 2
  set σ3 := sigmaB dY (p ^ 2) N 3
  -- the two geometric means
  have hX : √(σ1 * σ2) * p ^ 2 ≤ 28.77 := by
    have hX0 := Real.sqrt_nonneg (σ1 * σ2)
    have hXs := Real.sq_sqrt (mul_nonneg g1 g2)
    have : (√(σ1 * σ2) * p ^ 2) ^ 2 ≤ 28.77 ^ 2 := by
      have hm : (σ1 * p) * (σ2 * p ^ 3) ≤ 9.7 * 85.3 :=
        mul_le_mul s1 s2 (by positivity) (by norm_num)
      calc (√(σ1 * σ2) * p ^ 2) ^ 2 = (σ1 * p) * (σ2 * p ^ 3) := by rw [mul_pow, hXs]; ring
        _ ≤ 9.7 * 85.3 := hm
        _ ≤ 28.77 ^ 2 := by norm_num
    exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) this
  have hY : √(σ2 * σ3) * p ^ 4 ≤ 303.1 := by
    have hY0 := Real.sqrt_nonneg (σ2 * σ3)
    have hYs := Real.sq_sqrt (mul_nonneg g2 g3)
    have : (√(σ2 * σ3) * p ^ 4) ^ 2 ≤ 303.1 ^ 2 := by
      have hm : (σ2 * p ^ 3) * (σ3 * p ^ 5) ≤ 85.3 * 1077 :=
        mul_le_mul s2 s3 (by positivity) (by norm_num)
      calc (√(σ2 * σ3) * p ^ 4) ^ 2 = (σ2 * p ^ 3) * (σ3 * p ^ 5) := by rw [mul_pow, hYs]; ring
        _ ≤ 85.3 * 1077 := hm
        _ ≤ 303.1 ^ 2 := by norm_num
    exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) this
  -- the far-tail denominator
  have hZ : √((c * (1 / 2) / 2) ^ 5) * (32 * p ^ 15) = 1 := by
    have hZs := Real.sq_sqrt (show 0 ≤ (c * (1 / 2) / 2) ^ 5 by positivity)
    have hsq : (√((c * (1 / 2) / 2) ^ 5) * (32 * p ^ 15)) ^ 2 = 1 := by
      rw [mul_pow, hZs]
      calc (c * (1 / 2) / 2) ^ 5 * (32 * p ^ 15) ^ 2 = (c * p ^ 6) ^ 5 := by ring
        _ = 1 := by rw [hcp, one_pow]
    have h0 : 0 ≤ √((c * (1 / 2) / 2) ^ 5) * (32 * p ^ 15) := by positivity
    nlinarith [sq_nonneg (√((c * (1 / 2) / 2) ^ 5) * (32 * p ^ 15) - 1)]
  have h5π : (3.9 : ℝ) ≤ √(5 * π) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_d2])
  have hE1 : Real.exp (6 / 5 * (1 / 2)) ≤ (10 / 9) ^ 6 := by
    have := exp_le_pow 6; norm_num at this ⊢; exact this
  have hE2 : Real.exp (2 * (6 / 5) * (1 / 2)) ≤ (10 / 9) ^ 12 := by
    have := exp_le_pow 12; norm_num at this ⊢; exact this
  have hE10 := (Real.exp_pos (6 / 5 * (1 / 2))).le
  have hE20 := (Real.exp_pos (2 * (6 / 5) * (1 / 2))).le
  -- term by term
  have t1 : 2 * (6 / 5) * Real.exp (6 / 5 * (1 / 2)) * √(σ1 * σ2) / c ≤ 1.3 * p ^ 2 := by
    rw [div_eq_mul_one_div, hinv]
    have hX0 := Real.sqrt_nonneg (σ1 * σ2)
    calc 2 * (6 / 5) * Real.exp (6 / 5 * (1 / 2)) * √(σ1 * σ2) * p ^ 6
        = 2 * (6 / 5) * Real.exp (6 / 5 * (1 / 2)) * (√(σ1 * σ2) * p ^ 2) * p ^ 4 := by ring
      _ ≤ 2 * (6 / 5) * (10 / 9) ^ 6 * 28.77 * p ^ 4 := by gcongr
      _ ≤ 1.3 * p ^ 2 := by nlinarith [pow_pos hp0 2]
  have t2 : 448 / 1089 * √(σ2 * σ3) / (2 * c) ≤ 62.35 * p ^ 2 := by
    rw [show 448 / 1089 * √(σ2 * σ3) / (2 * c) = 224 / 1089 * √(σ2 * σ3) * (1 / c) by ring, hinv,
      show 224 / 1089 * √(σ2 * σ3) * p ^ 6 = 224 / 1089 * (√(σ2 * σ3) * p ^ 4) * p ^ 2 by ring]
    have : 224 / 1089 * (√(σ2 * σ3) * p ^ 4) ≤ 62.35 := by nlinarith
    nlinarith [pow_pos hp0 2]
  have t3 : (Real.exp (2 * (6 / 5) * (1 / 2)) + 1) * σ3 / (√(5 * π) * √((c * (1 / 2) / 2) ^ 5))
      ≤ 0.001 * p ^ 2 := by
    have hZ0 : 0 < √((c * (1 / 2) / 2) ^ 5) := Real.sqrt_pos.mpr (by positivity)
    have h5 : 0 < √(5 * π) := by linarith
    have hZe : √((c * (1 / 2) / 2) ^ 5) = 1 / (32 * p ^ 15) := by
      rw [eq_div_iff (by positivity)]; exact hZ
    have hσ : (Real.exp (2 * (6 / 5) * (1 / 2)) + 1) * (σ3 * p ^ 5) ≤ ((10 / 9) ^ 12 + 1) * 1077 :=
      mul_le_mul (by linarith) s3 (by positivity) (by positivity)
    have hp8 : p ^ 8 ≤ 1 / 100 ^ 4 := by
      calc p ^ 8 = (p ^ 2) ^ 4 := by ring
        _ ≤ (1 / 100) ^ 4 := pow_le_pow_left₀ (by positivity) hp2 4
        _ = 1 / 100 ^ 4 := by norm_num
    rw [hZe, show (Real.exp (2 * (6 / 5) * (1 / 2)) + 1) * σ3 / (√(5 * π) * (1 / (32 * p ^ 15)))
        = 32 * ((Real.exp (2 * (6 / 5) * (1 / 2)) + 1) * (σ3 * p ^ 5)) * p ^ 8 * p ^ 2 / √(5 * π) by
      field_simp, div_le_iff₀ h5]
    calc 32 * ((Real.exp (2 * (6 / 5) * (1 / 2)) + 1) * (σ3 * p ^ 5)) * p ^ 8 * p ^ 2
        ≤ 32 * (((10 / 9) ^ 12 + 1) * 1077) * (1 / 100 ^ 4) * p ^ 2 := by gcongr
      _ ≤ 0.001 * p ^ 2 * 3.9 := by nlinarith [pow_pos hp0 2]
      _ ≤ 0.001 * p ^ 2 * √(5 * π) := by gcongr
  linarith

end Cvs.L2a.CollarTransferConstant
