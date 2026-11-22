import Mathlib
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.CornerSuprema
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.RampTopQuadratic
import Cvs.L2a.ScaledBandTransfer
import Cvs.L2a.TopCornerConstants
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Zeta.Digamma.WeierstrassGammaSeq

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `resLoc ≤ 7/100` for `c ≥ 10¹⁶`

With `p = c^{1/8}`, `δ = d = 1/p²`, `c = p⁸`, each piece of `FrameFloorIntegerM`'s `resLoc` (the `T` envelope `τ̂ ≤ Ť/p³`, shells,
collars, chirps) is a closed form in `p`, `1/m`, bounded at `p = 100` uniformly in `M ≥ 3`, `0 ≤ J ≤ c/4 + 1`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.LocalResidualBound

open Cvs.L2a.OrbitGapIntegerM Cvs.L2a.BandTransferKernelForm Cvs.L2a.BandTransferBandForm

/-! ### The scale `p = c^{1/8}` -/

/-- `c ≥ 10¹⁶` gives `p ≥ 100` with `δ(c) = 1/p²` and `c = p⁸`. -/
theorem scale_p {c : ℝ} (hc : 10 ^ 16 ≤ c) :
    ∃ p : ℝ, 100 ≤ p ∧ Cvs.L2a.TopCornerSum.deltaS c = 1 / p ^ 2 ∧ c = p ^ 8 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  refine ⟨c ^ (1 / 8 : ℝ), ?_, ?_, ?_⟩
  · have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 10 ^ 16) hc (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have e : ((10 : ℝ) ^ 16) ^ (1 / 8 : ℝ) = 100 := by
      rw [show ((10 : ℝ) ^ 16) = 100 ^ 8 by norm_num, show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    rwa [e] at h
  · unfold Cvs.L2a.TopCornerSum.deltaS
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, Real.rpow_neg hc0.le, one_div]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num

theorem pi_bounds : (31415 / 10000 : ℝ) ≤ π ∧ π ≤ 31416 / 10000 := by
  have h1 := Real.pi_gt_d4
  have h2 := Real.pi_lt_d4
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-! ### The `T` envelope -/

/-- `√(xy) ≤ (μA + B/μ)/2` for `0 ≤ x ≤ A`, `0 ≤ y ≤ B`, `μ > 0`. -/
theorem sqrt_mul_le_amgm {x y A B μ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : x ≤ A) (hB : y ≤ B) (hμ : 0 < μ) :
    √(x * y) ≤ (μ * A + B / μ) / 2 := by
  have hA0 : 0 ≤ A := hx.trans hA
  have hB0 : 0 ≤ B := hy.trans hB
  have hxy : x * y ≤ A * B := mul_le_mul hA hB hy hA0
  have e : μ * A * (B / μ) = A * B := by field_simp
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (μ * A - B / μ)]

/-- **The `τ̂` envelope**: `σ₁ ≤ p²S₁`, `σ₂ ≤ p⁴S₂`, `σ₃ ≤ p⁶S₃`, `β_W ≤ B ≤ 1`, `Y'_W ≤ X` at `d = 1/p²`, `c = p⁸`,
`p ≥ 100` give `τ̂ ≤ (X(3S₂ + S₃/3)/4 + 3B(2S₁ + S₂/2)/10⁴ + 9S₃/10¹²)/10⁶`. -/
theorem tauHat_le {c x₀ δ p S₁ S₂ S₃ B X : ℝ} {N : ℕ → ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8)
    (hx : 2 ≤ x₀) (hδ : 0 ≤ δ) (hN : ∀ j ≤ 3, 0 ≤ N j)
    (h1 : sigmaB (Ymax x₀ - 1) δ N 1 ≤ p ^ 2 * S₁) (h2 : sigmaB (Ymax x₀ - 1) δ N 2 ≤ p ^ 4 * S₂)
    (h3 : sigmaB (Ymax x₀ - 1) δ N 3 ≤ p ^ 6 * S₃)
    (hβ : betaW x₀ (1 / p ^ 2) ≤ B) (hB1 : B ≤ 1) (hχ : chirpW x₀ (1 / p ^ 2) ≤ X) :
    tauHat c x₀ (1 / p ^ 2) δ N
      ≤ (X * (3 * S₂ + S₃ / 3) / 4 + 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 + 9 * S₃ / 10 ^ 12) / 10 ^ 6 := by
  have hp0 : 0 < p := by linarith
  set d := 1 / p ^ 2 with hd
  have hd0 : 0 < d := by positivity
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hdle : d ≤ 1 / 10 ^ 4 := by rw [hd]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hxd : 1 < x₀ - d := by linarith
  have hs : ∀ j ≤ 3, 0 ≤ sigmaB (Ymax x₀ - 1) δ N j := fun j hj =>
    Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg hδ fun i hi => hN i (hi.trans hj)
  have s1 := hs 1 (by norm_num)
  have s2 := hs 2 (by norm_num)
  have s3 := hs 3 le_rfl
  have hS₁ : 0 ≤ S₁ := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < p ^ 2)).1 (s1.trans h1)
  have hS₂ : 0 ≤ S₂ := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < p ^ 4)).1 (s2.trans h2)
  have hS₃ : 0 ≤ S₃ := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < p ^ 6)).1 (s3.trans h3)
  have hβ0 := betaW_nonneg hxd
  have hχ0 := chirpW_nonneg hd0.le hxd
  have hX0 : 0 ≤ X := hχ0.trans hχ
  have hB0 : 0 ≤ B := hβ0.trans hβ
  have hβd : betaW x₀ d * d ≤ 1 / 2 := by
    have : betaW x₀ d * d ≤ 1 * (1 / 10 ^ 4) := mul_le_mul (hβ.trans hB1) hdle hd0.le (by norm_num)
    linarith
  have he1 : Real.exp (betaW x₀ d * d) ≤ 3 := by
    have := Real.exp_one_lt_d9
    have := Real.exp_le_exp.2 (show betaW x₀ d * d ≤ 1 by linarith)
    linarith
  have he2 : Real.exp (2 * betaW x₀ d * d) + 1 ≤ 4 := by
    have := Real.exp_one_lt_d9
    have := Real.exp_le_exp.2 (show 2 * betaW x₀ d * d ≤ 1 by linarith)
    linarith
  have hq1 : √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) ≤ p ^ 3 * (2 * S₁ + S₂ / 2) / 2 := by
    refine (sqrt_mul_le_amgm s1 s2 h1 h2 (by positivity : (0 : ℝ) < 2 * p)).trans (le_of_eq ?_)
    field_simp
  have hq2 : √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) ≤ p ^ 5 * (3 * S₂ + S₃ / 3) / 2 := by
    refine (sqrt_mul_le_amgm s2 s3 h2 h3 (by positivity : (0 : ℝ) < 3 * p)).trans (le_of_eq ?_)
    field_simp
  have h5π : 39 / 10 ≤ √(5 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_d2]
  have hcd : p ^ 15 / 8 ≤ √((c * d / 2) ^ 5) := by
    have e : c * d / 2 = p ^ 6 / 2 := by rw [hc, hd]; field_simp
    rw [e, Real.le_sqrt (by positivity) (by positivity)]
    have : (p ^ 15 / 8) ^ 2 = p ^ 30 / 64 := by ring
    have : (p ^ 6 / 2) ^ 5 = p ^ 30 / 32 := by ring
    have : 0 < p ^ 30 := by positivity
    nlinarith
  have T1 : 2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
      * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) / c
      ≤ 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 / 10 ^ 6 := by
    have hA : 2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
        * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2)
        ≤ 2 * B * 3 * (p ^ 3 * (2 * S₁ + S₂ / 2) / 2) := by
      have := Real.exp_pos (betaW x₀ d * d)
      gcongr
    have hpow : 10 ^ 10 ≤ p ^ 5 := by
      calc (10 : ℝ) ^ 10 = 100 ^ 5 := by norm_num
        _ ≤ p ^ 5 := by gcongr
    calc 2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
          * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) / c
        ≤ 2 * B * 3 * (p ^ 3 * (2 * S₁ + S₂ / 2) / 2) / p ^ 8 := by
          rw [hc]; exact div_le_div_of_nonneg_right hA (by positivity)
      _ = 3 * B * (2 * S₁ + S₂ / 2) / p ^ 5 := by field_simp
      _ ≤ 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 10 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 / 10 ^ 6 := by ring
  have T2 : chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) / (2 * c)
      ≤ X * (3 * S₂ + S₃ / 3) / 4 / 10 ^ 6 := by
    have hA : chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3)
        ≤ X * (p ^ 5 * (3 * S₂ + S₃ / 3) / 2) := by gcongr
    have hpow : 10 ^ 6 ≤ p ^ 3 := by
      calc (10 : ℝ) ^ 6 = 100 ^ 3 := by norm_num
        _ ≤ p ^ 3 := by gcongr
    calc chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) / (2 * c)
        ≤ X * (p ^ 5 * (3 * S₂ + S₃ / 3) / 2) / (2 * p ^ 8) := by
          rw [hc]; exact div_le_div_of_nonneg_right hA (by positivity)
      _ = X * (3 * S₂ + S₃ / 3) / 4 / p ^ 3 := by field_simp; ring
      _ ≤ X * (3 * S₂ + S₃ / 3) / 4 / 10 ^ 6 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  have T3 : (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 / (√(5 * π) * √((c * d / 2) ^ 5))
      ≤ 9 * S₃ / 10 ^ 12 / 10 ^ 6 := by
    have hA : (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 ≤ 4 * (p ^ 6 * S₃) := by
      have := Real.exp_pos (2 * betaW x₀ d * d)
      gcongr
    have hD : 39 / 10 * (p ^ 15 / 8) ≤ √(5 * π) * √((c * d / 2) ^ 5) :=
      mul_le_mul h5π hcd (by positivity) (by positivity)
    have hpow : 10 ^ 18 ≤ p ^ 9 := by
      calc (10 : ℝ) ^ 18 = 100 ^ 9 := by norm_num
        _ ≤ p ^ 9 := by gcongr
    calc (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 / (√(5 * π) * √((c * d / 2) ^ 5))
        ≤ 4 * (p ^ 6 * S₃) / (39 / 10 * (p ^ 15 / 8)) := by
          refine div_le_div₀ (by positivity) hA (by positivity) hD
      _ = 320 / 39 * S₃ / p ^ 9 := by field_simp; ring
      _ ≤ 9 * S₃ / p ^ 9 := by gcongr; norm_num
      _ ≤ 9 * S₃ / 10 ^ 18 := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = 9 * S₃ / 10 ^ 12 / 10 ^ 6 := by ring
  unfold tauHat
  have e : (X * (3 * S₂ + S₃ / 3) / 4 + 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 + 9 * S₃ / 10 ^ 12) / 10 ^ 6
      = 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 / 10 ^ 6 + X * (3 * S₂ + S₃ / 3) / 4 / 10 ^ 6
        + 9 * S₃ / 10 ^ 12 / 10 ^ 6 := by ring
  rw [e]
  linarith

/-- `T ≤ 2ŤY/10⁶ + Ť²G/10¹²` from `τ̂ ≤ Ť/10⁶`, `√((ΔY + 2κ_Sδ)G/π) ≤ Y` and `G ≤ Ḡ`. -/
theorem tT_le_env {c x₀ d δ r J T Y Gb : ℝ}
    (hτ0 : 0 ≤ tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j))
    (hτ : tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) ≤ T / 10 ^ 6)
    (hY : √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1))) / π) ≤ Y)
    (hG0 : 0 ≤ 6 * J / (c * (x₀ ^ 2 - 1))) (hG : 6 * J / (c * (x₀ ^ 2 - 1)) ≤ Gb) :
    Cvs.L2a.LocalisedBottomCorners.tT c x₀ d δ r J ≤ 2 * T * Y / 10 ^ 6 + T ^ 2 * Gb / 10 ^ 12 := by
  unfold Cvs.L2a.LocalisedBottomCorners.tT
  set τ := tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j)
  have hT0 : 0 ≤ T / 10 ^ 6 := hτ0.trans hτ
  have hs := Real.sqrt_nonneg ((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1))) / π)
  have a : 2 * τ * √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1))) / π)
      ≤ 2 * (T / 10 ^ 6) * Y := by gcongr
  have b : τ ^ 2 * (6 * J / (c * (x₀ ^ 2 - 1))) ≤ (T / 10 ^ 6) ^ 2 * Gb := by gcongr
  have e : 2 * T * Y / 10 ^ 6 + T ^ 2 * Gb / 10 ^ 12 = 2 * (T / 10 ^ 6) * Y + (T / 10 ^ 6) ^ 2 * Gb := by ring
  rw [e]; linarith

theorem varsig_le : varsig 0 ≤ 626 / 1000 ∧ varsig 1 ≤ 11953 / 10000 ∧ varsig 2 ≤ 41404 / 10000
    ∧ varsig 3 ≤ 26834 / 1000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [varsig]; rw [Real.sqrt_le_left (by norm_num)]; norm_num)

/-- `σ₁, σ₂, σ₃` at collar `t²`, multipliers `j!/r^j`. -/
theorem sigmaB_t {dY t r : ℝ} (ht : 0 < t) :
    sigmaB dY (t ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 1
        = √(2 * dY) * (1 / r) + 2 * (varsig 0 * t * (1 / r) + varsig 1 * (1 / t))
      ∧ sigmaB dY (t ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 2
        = √(2 * dY) * (2 * (1 / r) ^ 2) + 2 * (varsig 0 * t * (2 * (1 / r) ^ 2)
          + 2 * varsig 1 * (1 / t) * (1 / r) + varsig 2 * (1 / t) ^ 3)
      ∧ sigmaB dY (t ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 3
        = √(2 * dY) * (6 * (1 / r) ^ 3) + 2 * (varsig 0 * t * (6 * (1 / r) ^ 3)
          + 3 * varsig 1 * (1 / t) * (2 * (1 / r) ^ 2) + 3 * varsig 2 * (1 / t) ^ 3 * (1 / r)
          + varsig 3 * (1 / t) ^ 5) := by
  have e1 : t / (t ^ 2) ^ 1 = 1 / t := by field_simp
  have e2 : t / (t ^ 2) ^ 2 = (1 / t) ^ 3 := by field_simp
  have e3 : t / (t ^ 2) ^ 3 = (1 / t) ^ 5 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [sigmaB, Finset.sum_range_succ, Finset.sum_range_zero, Real.sqrt_sq ht.le, e1]
    norm_num [Nat.choose, Nat.factorial]
  · simp only [sigmaB, Finset.sum_range_succ, Finset.sum_range_zero, Real.sqrt_sq ht.le, e1, e2]
    norm_num [Nat.choose, Nat.factorial]
    ring
  · simp only [sigmaB, Finset.sum_range_succ, Finset.sum_range_zero, Real.sqrt_sq ht.le, e1, e2, e3]
    norm_num [Nat.choose, Nat.factorial]
    ring

/-- `p³F ≤ p⁴F/100` for `p ≥ 100`, `F ≥ 0`, and its shifts. -/
theorem pow_step {p F : ℝ} (hp : 100 ≤ p) (hF : 0 ≤ F) (k : ℕ) : p ^ k * F ≤ p ^ (k + 1) * F / 100 := by
  have h0 : 0 ≤ p ^ k * F := by have : 0 ≤ p := by linarith
                                positivity
  have e : p ^ (k + 1) * F / 100 = p ^ k * F * (p / 100) := by ring
  rw [e]
  nlinarith

/-- **The `σ` envelope**: `ε ≤ E`, `t ≤ 1/p`, `1/t ≤ kp`, `1/r ≤ np²`, `p ≥ 100` give `σ₁ ≤ p²S₁`, `σ₂ ≤ p⁴S₂`,
`σ₃ ≤ p⁶S₃` at collar `t²`, with `S_j` linear in `E` and polynomial in `k`, `n`. -/
theorem sigma_env {dY t p E k n r : ℝ} (hp : 100 ≤ p) (hε : √(2 * dY) ≤ E) (ht : 0 < t) (ht1 : t ≤ 1 / p)
    (htk : 1 / t ≤ k * p) (hr : 0 < r) (hrn : 1 / r ≤ n * p ^ 2) :
    sigmaB dY (t ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 1
        ≤ p ^ 2 * (n * E + 2 * (626 / 1000 * n + 11953 / 10000 * k) / 100)
      ∧ sigmaB dY (t ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 2
        ≤ p ^ 4 * (2 * n ^ 2 * E + 2 * (626 / 1000 * (2 * n ^ 2) + 2 * (11953 / 10000) * (k * n)
          + 41404 / 10000 * k ^ 3) / 100)
      ∧ sigmaB dY (t ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 3
        ≤ p ^ 6 * (6 * n ^ 3 * E + 2 * (626 / 1000 * (6 * n ^ 3) + 3 * (11953 / 10000) * (2 * k * n ^ 2)
          + 3 * (41404 / 10000) * (k ^ 3 * n) + 26834 / 1000 * k ^ 5) / 100) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨e1, e2, e3⟩ := sigmaB_t (dY := dY) (r := r) ht
  obtain ⟨v0, v1, v2, v3⟩ := varsig_le
  have w0 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 0
  have w1 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 1
  have w2 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 2
  have w3 := Cvs.L2a.ScaledBandTransfer.varsig_nonneg 3
  set ρ := 1 / r with hρ
  set τ := 1 / t with hτ
  have hρ0 : 0 < ρ := by positivity
  have hτ0 : 0 < τ := by positivity
  have hn : 0 ≤ n := by
    have : 0 ≤ n * p ^ 2 := hρ0.le.trans hrn
    exact (mul_nonneg_iff_of_pos_right (by positivity)).1 this
  have hk : 0 ≤ k := by
    have : 0 ≤ k * p := hτ0.le.trans htk
    exact (mul_nonneg_iff_of_pos_right hp0).1 this
  have hE : 0 ≤ E := (Real.sqrt_nonneg _).trans hε
  have htp : t * p ≤ 1 := by rw [le_div_iff₀ hp0] at ht1; exact ht1
  -- the monomials
  have m1 : t * ρ ≤ n * p := by
    calc t * ρ ≤ t * (n * p ^ 2) := by gcongr
      _ = (t * p) * (n * p) := by ring
      _ ≤ 1 * (n * p) := by gcongr
      _ = n * p := one_mul _
  have m2 : t * (2 * ρ ^ 2) ≤ 2 * (n ^ 2 * p ^ 3) := by
    calc t * (2 * ρ ^ 2) ≤ t * (2 * (n * p ^ 2) ^ 2) := by gcongr
      _ = (t * p) * (2 * (n ^ 2 * p ^ 3)) := by ring
      _ ≤ 1 * (2 * (n ^ 2 * p ^ 3)) := by gcongr
      _ = 2 * (n ^ 2 * p ^ 3) := one_mul _
  have m3 : t * (6 * ρ ^ 3) ≤ 6 * (n ^ 3 * p ^ 5) := by
    calc t * (6 * ρ ^ 3) ≤ t * (6 * (n * p ^ 2) ^ 3) := by gcongr
      _ = (t * p) * (6 * (n ^ 3 * p ^ 5)) := by ring
      _ ≤ 1 * (6 * (n ^ 3 * p ^ 5)) := by gcongr
      _ = 6 * (n ^ 3 * p ^ 5) := one_mul _
  have q1 : τ * ρ ≤ k * n * p ^ 3 := by
    calc τ * ρ ≤ (k * p) * (n * p ^ 2) := by gcongr
      _ = k * n * p ^ 3 := by ring
  have q2 : τ * (2 * ρ ^ 2) ≤ 2 * k * n ^ 2 * p ^ 5 := by
    calc τ * (2 * ρ ^ 2) ≤ (k * p) * (2 * (n * p ^ 2) ^ 2) := by gcongr
      _ = 2 * k * n ^ 2 * p ^ 5 := by ring
  have q3 : τ ^ 3 ≤ k ^ 3 * p ^ 3 := by
    calc τ ^ 3 ≤ (k * p) ^ 3 := by gcongr
      _ = k ^ 3 * p ^ 3 := by ring
  have q4 : τ ^ 3 * ρ ≤ k ^ 3 * n * p ^ 5 := by
    calc τ ^ 3 * ρ ≤ (k * p) ^ 3 * (n * p ^ 2) := by gcongr
      _ = k ^ 3 * n * p ^ 5 := by ring
  have q5 : τ ^ 5 ≤ k ^ 5 * p ^ 5 := by
    calc τ ^ 5 ≤ (k * p) ^ 5 := by gcongr
      _ = k ^ 5 * p ^ 5 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    have hF : 0 ≤ 626 / 1000 * n + 11953 / 10000 * k := by positivity
    have st := pow_step hp hF 1
    have a1 : √(2 * dY) * ρ ≤ E * (n * p ^ 2) := by gcongr
    have a2 : varsig 0 * t * ρ ≤ 626 / 1000 * (n * p) := by
      rw [mul_assoc]; exact mul_le_mul v0 m1 (by positivity) (by norm_num)
    have a3 : varsig 1 * τ ≤ 11953 / 10000 * (k * p) := mul_le_mul v1 htk hτ0.le (by norm_num)
    have : p ^ 2 * (n * E + 2 * (626 / 1000 * n + 11953 / 10000 * k) / 100)
        = E * (n * p ^ 2) + 2 * (p ^ (1 + 1) * (626 / 1000 * n + 11953 / 10000 * k) / 100) := by ring
    rw [this]
    have : p ^ 1 * (626 / 1000 * n + 11953 / 10000 * k) = 626 / 1000 * (n * p) + 11953 / 10000 * (k * p) := by
      ring
    linarith
  · rw [e2]
    have hF : 0 ≤ 626 / 1000 * (2 * n ^ 2) + 2 * (11953 / 10000) * (k * n) + 41404 / 10000 * k ^ 3 := by
      positivity
    have st := pow_step hp hF 3
    have a1 : √(2 * dY) * (2 * ρ ^ 2) ≤ E * (2 * (n * p ^ 2) ^ 2) := by gcongr
    have a2 : varsig 0 * t * (2 * ρ ^ 2) ≤ 626 / 1000 * (2 * (n ^ 2 * p ^ 3)) := by
      rw [mul_assoc]; exact mul_le_mul v0 m2 (by positivity) (by norm_num)
    have a3 : 2 * varsig 1 * τ * ρ ≤ 2 * (11953 / 10000) * (k * n * p ^ 3) := by
      rw [mul_assoc]; exact mul_le_mul (by linarith) q1 (by positivity) (by norm_num)
    have a4 : varsig 2 * τ ^ 3 ≤ 41404 / 10000 * (k ^ 3 * p ^ 3) := mul_le_mul v2 q3 (by positivity) (by norm_num)
    have : p ^ 4 * (2 * n ^ 2 * E + 2 * (626 / 1000 * (2 * n ^ 2) + 2 * (11953 / 10000) * (k * n)
          + 41404 / 10000 * k ^ 3) / 100)
        = E * (2 * (n * p ^ 2) ^ 2) + 2 * (p ^ (3 + 1) * (626 / 1000 * (2 * n ^ 2) + 2 * (11953 / 10000) * (k * n)
          + 41404 / 10000 * k ^ 3) / 100) := by ring
    rw [this]
    have : p ^ 3 * (626 / 1000 * (2 * n ^ 2) + 2 * (11953 / 10000) * (k * n) + 41404 / 10000 * k ^ 3)
        = 626 / 1000 * (2 * (n ^ 2 * p ^ 3)) + 2 * (11953 / 10000) * (k * n * p ^ 3)
          + 41404 / 10000 * (k ^ 3 * p ^ 3) := by ring
    linarith
  · rw [e3]
    have hF : 0 ≤ 626 / 1000 * (6 * n ^ 3) + 3 * (11953 / 10000) * (2 * k * n ^ 2)
        + 3 * (41404 / 10000) * (k ^ 3 * n) + 26834 / 1000 * k ^ 5 := by positivity
    have st := pow_step hp hF 5
    have a1 : √(2 * dY) * (6 * ρ ^ 3) ≤ E * (6 * (n * p ^ 2) ^ 3) := by gcongr
    have a2 : varsig 0 * t * (6 * ρ ^ 3) ≤ 626 / 1000 * (6 * (n ^ 3 * p ^ 5)) := by
      rw [mul_assoc]; exact mul_le_mul v0 m3 (by positivity) (by norm_num)
    have a3 : 3 * varsig 1 * τ * (2 * ρ ^ 2) ≤ 3 * (11953 / 10000) * (2 * k * n ^ 2 * p ^ 5) := by
      rw [mul_assoc]; exact mul_le_mul (by linarith) q2 (by positivity) (by norm_num)
    have a4 : 3 * varsig 2 * τ ^ 3 * ρ ≤ 3 * (41404 / 10000) * (k ^ 3 * n * p ^ 5) := by
      rw [mul_assoc]; exact mul_le_mul (by linarith) q4 (by positivity) (by norm_num)
    have a5 : varsig 3 * τ ^ 5 ≤ 26834 / 1000 * (k ^ 5 * p ^ 5) := mul_le_mul v3 q5 (by positivity) (by norm_num)
    have : p ^ 6 * (6 * n ^ 3 * E + 2 * (626 / 1000 * (6 * n ^ 3) + 3 * (11953 / 10000) * (2 * k * n ^ 2)
          + 3 * (41404 / 10000) * (k ^ 3 * n) + 26834 / 1000 * k ^ 5) / 100)
        = E * (6 * (n * p ^ 2) ^ 3) + 2 * (p ^ (5 + 1) * (626 / 1000 * (6 * n ^ 3)
          + 3 * (11953 / 10000) * (2 * k * n ^ 2) + 3 * (41404 / 10000) * (k ^ 3 * n) + 26834 / 1000 * k ^ 5)
          / 100) := by ring
    rw [this]
    have : p ^ 5 * (626 / 1000 * (6 * n ^ 3) + 3 * (11953 / 10000) * (2 * k * n ^ 2)
          + 3 * (41404 / 10000) * (k ^ 3 * n) + 26834 / 1000 * k ^ 5)
        = 626 / 1000 * (6 * (n ^ 3 * p ^ 5)) + 3 * (11953 / 10000) * (2 * k * n ^ 2 * p ^ 5)
          + 3 * (41404 / 10000) * (k ^ 3 * n * p ^ 5) + 26834 / 1000 * (k ^ 5 * p ^ 5) := by ring
    linarith

/-! ### The `x₀` factors at `u = 1/x₀ ≤ 1/2` -/

theorem Ymax_sub_lt {x₀ : ℝ} (hx : 2 ≤ x₀) : Ymax x₀ - 1 < 2 / 3 * (1 / x₀) ^ 2 := by
  have h := Cvs.L2a.TopCornerConstants.dY_lt (x := x₀) (by linarith)
  unfold Cvs.L2a.TopCornerConstants.dY at h
  refine h.trans_le ?_
  have hx1 : 0 < x₀ ^ 2 - 1 := by nlinarith
  rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem one_le_Ymax' {x₀ : ℝ} (hx : 2 ≤ x₀) : 0 ≤ Ymax x₀ - 1 := by
  have := one_le_Ymax (x := x₀) (by linarith); linarith

/-- `ε = √(2ΔY) ≤ 1.155u`, `β_W ≤ 1.4u`, `Y'_W ≤ 1.9u³` at `d = 1/p²`, `x₀ ≥ 2`. -/
theorem x0_facts {x₀ p : ℝ} (hp : 100 ≤ p) (hx : 2 ≤ x₀) :
    √(2 * (Ymax x₀ - 1)) ≤ 1155 / 1000 * (1 / x₀) ∧ betaW x₀ (1 / p ^ 2) ≤ 14 / 10 * (1 / x₀)
      ∧ chirpW x₀ (1 / p ^ 2) ≤ 19 / 10 * (1 / x₀) ^ 3 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x₀ := by linarith
  set d := 1 / p ^ 2 with hd
  have hd0 : 0 < d := by positivity
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hdle : d ≤ 1 / 10 ^ 4 := by rw [hd]; exact one_div_le_one_div_of_le (by norm_num) hp2
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sqrt_le_left (by positivity)]
    have := Ymax_sub_lt hx
    have e : (1155 / 1000 * (1 / x₀)) ^ 2 = 1334025 / 1000000 * (1 / x₀) ^ 2 := by ring
    rw [e]
    have : 0 ≤ (1 / x₀) ^ 2 := by positivity
    linarith
  · unfold betaW
    set y := x₀ - d with hy
    have hy2 : 19999 / 10000 ≤ y := by linarith
    have hyy : 0 < y ^ 2 - 1 := by nlinarith
    rw [div_le_iff₀ hyy]
    have e : 14 / 10 * (1 / x₀) * (y ^ 2 - 1) = (14 / 10 * (y ^ 2 - 1)) / x₀ := by ring
    rw [e, le_div_iff₀ hx0]
    have hxy : x₀ = y + d := by rw [hy]; ring
    rw [hxy]
    nlinarith [mul_le_mul_of_nonneg_left hdle (by linarith : (0 : ℝ) ≤ y)]
  · unfold chirpW
    set y := x₀ - d / 2 with hy
    have hy2 : 19999 / 10000 ≤ y := by linarith
    have hyy : 0 < y ^ 2 - 1 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : 19 / 10 * (1 / x₀) ^ 3 * (y ^ 2 - 1) ^ 2 = (19 / 10 * (y ^ 2 - 1) ^ 2) / x₀ ^ 3 := by ring
    rw [e, le_div_iff₀ (by positivity)]
    have hxy : x₀ ≤ (1 + 1 / 39000) * y := by
      have : d / 2 ≤ 1 / 20000 := by linarith
      have e : x₀ = y + d / 2 := by rw [hy]; ring
      rw [e]; nlinarith
    have h3 : x₀ ^ 3 ≤ ((1 + 1 / 39000) * y) ^ 3 := pow_le_pow_left₀ hx0.le hxy 3
    have hz : 39996 / 10000 ≤ y ^ 2 := by nlinarith
    have key : (1 + 1 / 39000) ^ 3 * y ^ 4 ≤ 19 / 10 * (y ^ 2 - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hz) (sub_nonneg.2 hz)]
    calc y * x₀ ^ 3 ≤ y * ((1 + 1 / 39000) * y) ^ 3 := by gcongr
      _ = (1 + 1 / 39000) ^ 3 * y ^ 4 := by ring
      _ ≤ _ := key

/-- `G = 6J/(c(x₀² − 1)) ≤ 2.01u²` for `c = p⁸`, `p ≥ 100`, `0 ≤ J ≤ c/4 + 1`. -/
theorem G_le {c x₀ J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hx : 2 ≤ x₀) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    0 ≤ 6 * J / (c * (x₀ ^ 2 - 1)) ∧ 6 * J / (c * (x₀ ^ 2 - 1)) ≤ 201 / 100 * (1 / x₀) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hc8 : 800 ≤ c := by
    rw [hc]; calc (800 : ℝ) ≤ 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc0 : 0 < c := by linarith
  have hx1 : 0 < x₀ ^ 2 - 1 := by nlinarith
  refine ⟨by positivity, ?_⟩
  have h1 : 6 * J / c ≤ 15075 / 10000 := by rw [div_le_iff₀ hc0]; nlinarith
  have h2 : 1 / (x₀ ^ 2 - 1) ≤ 4 / 3 * (1 / x₀) ^ 2 := by
    rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ hx1 (by positivity)]; nlinarith
  calc 6 * J / (c * (x₀ ^ 2 - 1)) = 6 * J / c * (1 / (x₀ ^ 2 - 1)) := by field_simp
    _ ≤ 15075 / 10000 * (4 / 3 * (1 / x₀) ^ 2) := by gcongr
    _ = 201 / 100 * (1 / x₀) ^ 2 := by ring

/-- `√((ΔY + 2κ_Sδ′)G/π) ≤ 0.66u² + 0.0072u` for `0 ≤ δ′ ≤ 1/p²`. -/
theorem Y_le {c x₀ J p δ : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hx : 2 ≤ x₀) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / p ^ 2) :
    √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1))) / π)
      ≤ 66 / 100 * (1 / x₀) ^ 2 + 72 / 10000 * (1 / x₀) := by
  have hx0 : 0 < x₀ := by linarith
  obtain ⟨hG0, hG⟩ := G_le hp hc hx hJ0 hJ
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hδ4 : δ ≤ 1 / 10 ^ 4 := hδ.trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hY := Ymax_sub_lt hx
  have hY0 := one_le_Ymax' hx
  set u := 1 / x₀ with hu
  have hu0 : 0 < u := by positivity
  have hW : Ymax x₀ - 1 + 2 * (181 / 462) * δ ≤ 2 / 3 * u ^ 2 + 2 * (181 / 462) / 10 ^ 4 := by linarith
  have hW0 : 0 ≤ Ymax x₀ - 1 + 2 * (181 / 462) * δ := by positivity
  have hπ : 31415 / 10000 ≤ π := by linarith [Real.pi_gt_d4]
  rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
  calc (Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1)))
      ≤ (2 / 3 * u ^ 2 + 2 * (181 / 462) / 10 ^ 4) * (201 / 100 * u ^ 2) := by gcongr
    _ ≤ (66 / 100 * u ^ 2 + 72 / 10000 * u) ^ 2 * (31415 / 10000) := by
        nlinarith [pow_pos hu0 4, pow_pos hu0 3, pow_pos hu0 2]
    _ ≤ (66 / 100 * u ^ 2 + 72 / 10000 * u) ^ 2 * π := by gcongr

/-! ### The two regimes -/

/-- The regime-II polynomial: `S₁ ≤ 0.8663u + 0.0333`, `S₂ ≤ 1.2994u + 0.1328`, `S₃ ≤ 2.9236u + 0.8354` give
`2ŤY/10⁶ + Ť²G/10¹² ≤ (11·10⁻⁴)²u⁴ + (21·10⁻⁶)²u²` on `1/549 ≤ u ≤ 1/2`. -/
theorem poly_regII {u S₁ S₂ S₃ : ℝ} (hu0 : 0 < u) (hu2 : u ≤ 1 / 2) (hu549 : 1 / 549 ≤ u)
    (h1 : S₁ ≤ 8663 / 10 ^ 4 * u + 333 / 10 ^ 4) (h2 : S₂ ≤ 12994 / 10 ^ 4 * u + 1328 / 10 ^ 4)
    (h3 : S₃ ≤ 29236 / 10 ^ 4 * u + 8354 / 10 ^ 4) (h10 : 0 ≤ S₁) (h20 : 0 ≤ S₂) (h30 : 0 ≤ S₃) :
    2 * (19 / 10 * u ^ 3 * (3 * S₂ + S₃ / 3) / 4 + 3 * (14 / 10 * u) * (2 * S₁ + S₂ / 2) / 10 ^ 4
        + 9 * S₃ / 10 ^ 12) * (66 / 100 * u ^ 2 + 72 / 10000 * u) / 10 ^ 6
      + (19 / 10 * u ^ 3 * (3 * S₂ + S₃ / 3) / 4 + 3 * (14 / 10 * u) * (2 * S₁ + S₂ / 2) / 10 ^ 4
        + 9 * S₃ / 10 ^ 12) ^ 2 * (201 / 100 * u ^ 2) / 10 ^ 12
      ≤ (11 / 10 ^ 4) ^ 2 * u ^ 4 + (21 / 10 ^ 6) ^ 2 * u ^ 2 := by
  set T := 19 / 10 * u ^ 3 * (3 * S₂ + S₃ / 3) / 4 + 3 * (14 / 10 * u) * (2 * S₁ + S₂ / 2) / 10 ^ 4
    + 9 * S₃ / 10 ^ 12 with hT
  have h43 : u ^ 4 ≤ u ^ 3 / 2 := by nlinarith [pow_pos hu0 3]
  have h21 : u ^ 2 ≤ u / 2 := by nlinarith
  have a : 19 / 10 * u ^ 3 * (3 * S₂ + S₃ / 3) / 4
      ≤ 19 / 10 * u ^ 3 * (3 * (12994 / 10 ^ 4 * u + 1328 / 10 ^ 4)
        + (29236 / 10 ^ 4 * u + 8354 / 10 ^ 4) / 3) / 4 := by
    gcongr
  have b : 3 * (14 / 10 * u) * (2 * S₁ + S₂ / 2) / 10 ^ 4
      ≤ 3 * (14 / 10 * u) * (2 * (8663 / 10 ^ 4 * u + 333 / 10 ^ 4) + (12994 / 10 ^ 4 * u + 1328 / 10 ^ 4) / 2)
        / 10 ^ 4 := by gcongr
  have c : 9 * S₃ / 10 ^ 12 ≤ 9 * (29236 / 10 ^ 4 * u + 8354 / 10 ^ 4) / 10 ^ 12 := by gcongr
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hTb : T ≤ 148 / 100 * u ^ 3 + 56 / 10 ^ 5 * u + 21 / 10 ^ 12 := by
    rw [hT]; linarith
  have hTb' : 148 / 100 * u ^ 3 + 56 / 10 ^ 5 * u + 21 / 10 ^ 12 ≤ 19 / 100 := by
    have := pow_le_pow_left₀ hu0.le hu2 3
    norm_num at this ⊢; linarith
  have hY0 : 0 ≤ 66 / 100 * u ^ 2 + 72 / 10000 * u := by positivity
  have hT2 : T ^ 2 ≤ (19 / 100) ^ 2 := pow_le_pow_left₀ hT0 (hTb.trans hTb') 2
  have s1 : 2 * T * (66 / 100 * u ^ 2 + 72 / 10000 * u) / 10 ^ 6
      ≤ 2 * (148 / 100 * u ^ 3 + 56 / 10 ^ 5 * u + 21 / 10 ^ 12) * (66 / 100 * u ^ 2 + 72 / 10000 * u) / 10 ^ 6 := by
    gcongr
  have s2 : T ^ 2 * (201 / 100 * u ^ 2) / 10 ^ 12 ≤ (19 / 100) ^ 2 * (201 / 100 * u ^ 2) / 10 ^ 12 := by gcongr
  have h54 : u ^ 5 ≤ u ^ 4 / 2 := by nlinarith [pow_pos hu0 4]
  have h32 : u ^ 3 ≤ u ^ 2 / 2 := by nlinarith [pow_pos hu0 2]
  have h12 : u ≤ 549 * u ^ 2 := by nlinarith
  linarith [pow_pos hu0 4, pow_pos hu0 2, pow_pos hu0 3]

/-- **Regime II** (`δ′ = δ`, `r ≥ 4δ/3`): `T(c, x₀, δ, δ, r, J) ≤ (11·10⁻⁴)²u⁴ + (21·10⁻⁶)²u²`, `u = 1/x₀`,
for `2 ≤ x₀ ≤ 549`. -/
theorem tT_regII {c x₀ r J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hx : 2 ≤ x₀) (hx' : x₀ ≤ 549)
    (hr : 4 / 3 / p ^ 2 ≤ r) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.tT c x₀ (1 / p ^ 2) (1 / p ^ 2) r J
      ≤ (11 / 10 ^ 4) ^ 2 * (1 / x₀) ^ 4 + (21 / 10 ^ 6) ^ 2 * (1 / x₀) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x₀ := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hd : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  obtain ⟨hε, hβ, hχ⟩ := x0_facts hp hx
  have hrn : 1 / r ≤ 3 / 4 * p ^ 2 := by
    rw [div_le_iff₀ hr0]
    have : 4 / 3 / p ^ 2 * (3 / 4 * p ^ 2) = 1 := by field_simp
    nlinarith
  have hu0 : 0 < 1 / x₀ := by positivity
  have hu2 : 1 / x₀ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hx
  have hu549 : 1 / 549 ≤ 1 / x₀ := one_div_le_one_div_of_le hx0 hx'
  obtain ⟨h1, h2, h3⟩ := sigma_env (dY := Ymax x₀ - 1) (t := 1 / p) (k := 1) (n := 3 / 4) hp hε
    (by positivity) le_rfl (by rw [one_div_one_div, one_mul]) hr0 hrn
  rw [show (1 / p) ^ 2 = 1 / p ^ 2 by ring] at h1 h2 h3
  have hN : ∀ j ≤ 3, 0 ≤ (fun j : ℕ => (j.factorial : ℝ) / r ^ j) j := fun j _ => by positivity
  have hs := fun j (hj : j ≤ 3) => Cvs.L2a.ScaledBandTransfer.sigmaB_nonneg (dY := Ymax x₀ - 1) (δ := 1 / p ^ 2)
    (by positivity) (j := j) fun i hi => hN i (hi.trans hj)
  obtain ⟨S₁, hS₁, h1⟩ : ∃ S, S ≤ 8663 / 10 ^ 4 * (1 / x₀) + 333 / 10 ^ 4
      ∧ sigmaB (Ymax x₀ - 1) (1 / p ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 1 ≤ p ^ 2 * S :=
    ⟨_, by linarith, h1⟩
  obtain ⟨S₂, hS₂, h2⟩ : ∃ S, S ≤ 12994 / 10 ^ 4 * (1 / x₀) + 1328 / 10 ^ 4
      ∧ sigmaB (Ymax x₀ - 1) (1 / p ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 2 ≤ p ^ 4 * S :=
    ⟨_, by linarith, h2⟩
  obtain ⟨S₃, hS₃, h3⟩ : ∃ S, S ≤ 29236 / 10 ^ 4 * (1 / x₀) + 8354 / 10 ^ 4
      ∧ sigmaB (Ymax x₀ - 1) (1 / p ^ 2) (fun j => (j.factorial : ℝ) / r ^ j) 3 ≤ p ^ 6 * S :=
    ⟨_, by linarith, h3⟩
  have h10 : 0 ≤ S₁ := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < p ^ 2)).1 ((hs 1 (by norm_num)).trans h1)
  have h20 : 0 ≤ S₂ := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < p ^ 4)).1 ((hs 2 (by norm_num)).trans h2)
  have h30 : 0 ≤ S₃ := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < p ^ 6)).1 ((hs 3 le_rfl).trans h3)
  have hτ := tauHat_le hp hc hx (by positivity) hN h1 h2 h3 hβ (by linarith) hχ
  have hτ0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg (c := c) (x₀ := x₀) (d := 1 / p ^ 2) (δ := 1 / p ^ 2)
    (by rw [hc]; positivity) (by positivity) (by linarith [hd]) (by positivity) hN
  obtain ⟨hG0, hG⟩ := G_le hp hc hx hJ0 hJ
  have hY := Y_le hp hc hx hJ0 hJ (δ := 1 / p ^ 2) (by positivity) le_rfl
  exact (tT_le_env hτ0 hτ hY hG0 hG).trans (poly_regII hu0 hu2 hu549 hS₁ hS₂ hS₃ h10 h20 h30)

/-- **Regime I** (`δ/3 ≤ δ′ ≤ δ`, `r ≥ δ/3`): `T(c, x₀, δ, δ′, r, J) ≤ 1.5·10⁻⁶` for `x₀ ≥ 2`. -/
theorem tT_regI {c x₀ δ r J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hx : 2 ≤ x₀)
    (hδlo : 1 / 3 / p ^ 2 ≤ δ) (hδhi : δ ≤ 1 / p ^ 2) (hr : 1 / 3 / p ^ 2 ≤ r) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.tT c x₀ (1 / p ^ 2) δ r J ≤ 15 / 10 ^ 7 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x₀ := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδlo
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  obtain ⟨hε, hβ, hχ⟩ := x0_facts hp hx
  set u := 1 / x₀ with hu
  have hu0 : 0 < u := by positivity
  have hu2 : u ≤ 1 / 2 := by rw [hu]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hrn : 1 / r ≤ 3 * p ^ 2 := by
    rw [div_le_iff₀ hr0]
    have : 1 / 3 / p ^ 2 * (3 * p ^ 2) = 1 := by field_simp
    nlinarith
  obtain ⟨t, ht0, rfl⟩ : ∃ t, 0 < t ∧ δ = t ^ 2 := ⟨√δ, Real.sqrt_pos.2 hδ0, (Real.sq_sqrt hδ0.le).symm⟩
  have ht1 : t ≤ 1 / p := by
    rw [← Real.sqrt_sq ht0.le, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / p)]
    exact Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact hδhi)
  have htk : 1 / t ≤ 17321 / 10000 * p := by
    have h3 : 1 / (3 * p ^ 2) ≤ t ^ 2 := by rw [show 1 / (3 * p ^ 2) = 1 / 3 / p ^ 2 by ring]; exact hδlo
    rw [div_le_iff₀ ht0]
    have hk : (1 : ℝ) ≤ (17321 / 10000) ^ 2 / 3 := by norm_num
    have : 1 ≤ (17321 / 10000 * p * t) ^ 2 := by
      calc (1 : ℝ) ≤ (17321 / 10000) ^ 2 / 3 := hk
        _ = (17321 / 10000) ^ 2 * p ^ 2 * (1 / (3 * p ^ 2)) := by field_simp
        _ ≤ (17321 / 10000) ^ 2 * p ^ 2 * t ^ 2 := by gcongr
        _ = (17321 / 10000 * p * t) ^ 2 := by ring
    nlinarith [sq_nonneg (17321 / 10000 * p * t - 1), mul_pos (mul_pos (by norm_num : (0 : ℝ) < 17321 / 10000) hp0) ht0]
  have hεc : √(2 * (Ymax x₀ - 1)) ≤ 1155 / 1000 * (1 / 2) := hε.trans (by gcongr)
  obtain ⟨h1, h2, h3⟩ := sigma_env (dY := Ymax x₀ - 1) (k := 17321 / 10000) (n := 3) hp hεc ht0 ht1 htk hr0 hrn
  have hN : ∀ j ≤ 3, 0 ≤ (fun j : ℕ => (j.factorial : ℝ) / r ^ j) j := fun j _ => by positivity
  have hτ := tauHat_le hp hc hx (by positivity) hN h1 h2 h3 (hβ.trans (by gcongr : 14 / 10 * u ≤ 14 / 10 * (1 / 2)))
    (by norm_num) (hχ.trans (by gcongr : 19 / 10 * u ^ 3 ≤ 19 / 10 * (1 / 2) ^ 3))
  have hτ0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg (c := c) (x₀ := x₀) (d := 1 / p ^ 2) (δ := t ^ 2)
    (by rw [hc]; positivity) (by positivity) (by linarith) (by positivity) hN
  obtain ⟨hG0, hG⟩ := G_le hp hc hx hJ0 hJ
  have hY := Y_le hp hc hx hJ0 hJ (δ := t ^ 2) (by positivity) hδhi
  have hYc : 66 / 100 * u ^ 2 + 72 / 10000 * u ≤ 66 / 100 * (1 / 2) ^ 2 + 72 / 10000 * (1 / 2) := by gcongr
  have hGc : 201 / 100 * u ^ 2 ≤ 201 / 100 * (1 / 2) ^ 2 := by gcongr
  refine (tT_le_env hτ0 hτ (hY.trans hYc) hG0 (hG.trans hGc)).trans ?_
  norm_num

/-! ### The bottom main excess `Σ lamX` -/

section lam

open Cvs.L2a.LocalisedBottomCorners (gT collF bP eSh dSh nSh iSh)
open Cvs.L2a.FarIntegrationByParts (wF)

theorem iSh_integrand_le (x : ℝ) : ‖4 * (1 - wF x) / (2 - x) ^ 2‖ ≤ 4 * π ^ 2 := by
  have h0 : 0 ≤ 1 - wF x := by linarith [(Cvs.L2a.FarFarBound.wF_bounds x).2.1]
  have h1 := Cvs.L2a.RampTopQuadratic.one_sub_wF_le x
  rw [Real.norm_of_nonneg (by positivity)]
  rcases eq_or_ne (2 - x) 0 with h | h
  · rw [h]; simp; positivity
  · rw [div_le_iff₀ (by positivity)]; nlinarith

theorem eSh_mono {s : ℝ} (hs : 0 ≤ s) : Monotone (eSh s) := fun k l hkl =>
  min_le_min le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hkl) hs)

theorem eSh_pos {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < eSh s k := lt_min one_pos (by positivity)

theorem eSh_le_one (s : ℝ) (k : ℕ) : eSh s k ≤ 1 := min_le_left _ _

theorem eSh_zero {s : ℝ} (hs1 : s ≤ 1) : eSh s 0 = s := by
  unfold eSh; rw [pow_zero, mul_one]; exact min_eq_right hs1

/-- `I_k ≤ 4π²(e_{k+1} − e_k)`, from `1 − wF ≤ π²(2 − t)²`. -/
theorem iSh_le {s : ℝ} (hs : 0 < s) (k : ℕ) : iSh s k ≤ 4 * π ^ 2 * (eSh s (k + 1) - eSh s k) := by
  have hm := eSh_mono hs.le (Nat.le_succ k)
  unfold iSh
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => iSh_integrand_le x).trans (le_of_eq ?_)
  rw [show 2 - eSh s k - (2 - eSh s (k + 1)) = eSh s (k + 1) - eSh s k by ring, abs_of_nonneg (by linarith)]

/-- **The `m = 2` shells**: `Σ_k (4κ_S/π²)δ_k I_k ≤ 16κ_Sδ`. -/
theorem sum_shells_le {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 < s) (n : ℕ) :
    ∑ k ∈ Finset.range n, 4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k ≤ 16 * (181 / 462) * δ := by
  have hπ : 0 < π ^ 2 := by positivity
  have hterm : ∀ k ∈ Finset.range n, 4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k
      ≤ 16 * (181 / 462) * δ * (eSh s (k + 1) - eSh s k) := fun k _ => by
    have hd0 : 0 ≤ dSh δ s k := le_min hδ (by have := eSh_pos hs k; positivity)
    have hdδ : dSh δ s k ≤ δ := min_le_left _ _
    have hm := eSh_mono hs.le (Nat.le_succ k)
    have hi := iSh_le hs k
    have h1 : dSh δ s k * iSh s k ≤ δ * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) :=
      (mul_le_mul_of_nonneg_left hi hd0).trans (mul_le_mul_of_nonneg_right hdδ (by nlinarith))
    calc 4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k = 4 * (181 / 462) / π ^ 2 * (dSh δ s k * iSh s k) := by
          ring
      _ ≤ 4 * (181 / 462) / π ^ 2 * (δ * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k))) := by gcongr
      _ = 16 * (181 / 462) * δ * (eSh s (k + 1) - eSh s k) := by field_simp; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub (eSh s)]
  have h1 := eSh_le_one s n
  have h0 := eSh_pos hs 0
  have : 0 ≤ 16 * (181 / 462) * δ := by positivity
  nlinarith

/-- `|g₂(2 − s)| ≤ 1/s` for `0 < s ≤ 1`. -/
theorem abs_gT_two_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : |gT 2 (2 - s)| ≤ 1 / s := by
  rw [Cvs.L2a.LocalisedBottomCorners.gT_eq_integral (by norm_num) (by linarith)
    (Cvs.L2a.LocalisedBottomCorners.off_near (by norm_num) (by linarith))]
  have hY := one_le_Ymax (x := (2 : ℝ)) (by norm_num)
  have hY2 := Ymax_sub_lt (x₀ := 2) le_rfl
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1 / (3 * s)) fun v hv => ?_).trans ?_
  · rw [Set.uIoc_of_le hY] at hv
    have hv1 : 1 < v := hv.1
    have hq : 3 * s ≤ 2 ^ 2 * v ^ 2 - (2 - s) ^ 2 := by nlinarith
    have hq0 : 0 < 2 ^ 2 * v ^ 2 - (2 - s) ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_neg (by linarith), neg_sub]
    exact one_div_le_one_div_of_le (by positivity) hq
  · rw [abs_of_nonneg (by linarith)]
    have : Ymax 2 - 1 ≤ 1 / 6 := by norm_num at hY2; linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hs]
    nlinarith

/-- `|g_m(2)| ≤ 1` for `m ≥ 3`. -/
theorem abs_gT_m_two_le {m : ℝ} (hm : 3 ≤ m) : |gT m 2| ≤ 1 := by
  rw [Cvs.L2a.LocalisedBottomCorners.gT_eq_integral (by linarith) (by norm_num)
    (Cvs.L2a.LocalisedBottomCorners.off_near (by linarith) (by linarith))]
  have h := Cvs.L2a.LocalisedConstants.abs_gm_two_le (m := m) (by linarith)
  unfold Cvs.L2a.LocalisedConstants.gm at h
  refine h.trans ?_
  have h8 : 8 ≤ m ^ 2 - 1 := by nlinarith
  have h5 : 5 ≤ m ^ 2 - 4 := by nlinarith
  have := mul_le_mul h8 h5 (by norm_num) (by linarith)
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- `0 ≤ g_m(M) ≤ 1` for `2 ≤ m ≤ M − 1`. -/
theorem gT_M_le {m M : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) : 0 ≤ gT m M ∧ gT m M ≤ 1 := by
  have hg := Cvs.L2a.LocalisedConstants.g0_le_sub_bm hm hM
  have hg0 := Cvs.L2a.LocalisedConstants.g0_bounds.1
  have hb := Cvs.L2a.CornerSuprema.lt_bm (m := m) (by linarith)
  have hbM : Cvs.L2a.CornerSuprema.bm m < M := by linarith
  obtain ⟨h0, h1⟩ := (Cvs.L2a.LocalisedBottomCorners.gT_far (m := m) (by linarith)).1 M hbM
  refine ⟨h0, h1.trans ?_⟩
  have hY := Ymax_sub_lt hm
  have hY' : Ymax m - 1 ≤ 1 / 6 := by
    have : (1 / m) ^ 2 ≤ (1 / 2) ^ 2 := by gcongr
    linarith
  have hden : 1 / 6 ≤ M ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2 := by nlinarith
  rw [div_le_one (by linarith)]
  linarith

/-- `collF(β, M) ≤ 1/(M − β)` for `0 < β < M`, from `log x ≤ x − 1`. -/
theorem collF_le {β M : ℝ} (hβ : 0 < β) (hM : β < M) : collF β M ≤ 1 / (M - β) := by
  unfold collF
  have hMβ : 0 < M - β := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < M + β) hMβ)
  have e : (M + β) / (M - β) - 1 = 2 * β / (M - β) := by field_simp; ring
  rw [e] at hl
  have h2 : 1 / (4 * β) * Real.log ((M + β) / (M - β)) ≤ 1 / (2 * (M - β)) := by
    calc 1 / (4 * β) * Real.log ((M + β) / (M - β)) ≤ 1 / (4 * β) * (2 * β / (M - β)) := by gcongr
      _ = 1 / (2 * (M - β)) := by field_simp; ring
  have h1 : M / (2 * (M ^ 2 - β ^ 2)) ≤ 1 / (2 * (M - β)) := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]; nlinarith
  have : 1 / (2 * (M - β)) + 1 / (2 * (M - β)) = 1 / (M - β) := by field_simp; ring
  linarith

/-- The near collar for `m ≥ 3`: `(4κ_S/π²)δ(3/4)a²/(a² − 4)² ≤ (12κ_S/π²)δ/(1 − δ)²·(1/(m − 1) − 1/m)`. -/
theorem near_coll_le {δ m : ℝ} (hm : 3 ≤ m) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100) :
    4 * (181 / 462) / π ^ 2 * δ * (3 / 4) * ((m * (1 - δ)) ^ 2 / ((m * (1 - δ)) ^ 2 - 4) ^ 2)
      ≤ 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / (m - 1) - 1 / m) := by
  set a := m * (1 - δ) with ha
  have ha3 : 297 / 100 ≤ a := by rw [ha]; nlinarith
  have ha8 : 8 ≤ a ^ 2 := by nlinarith
  have h1 : a ^ 2 / (a ^ 2 - 4) ^ 2 ≤ 4 / a ^ 2 := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * a ^ 2 - 8) (by linarith : (0 : ℝ) ≤ a ^ 2 - 8)]
  have hd : 0 < 1 - δ := by linarith
  have h2 : 4 / a ^ 2 ≤ 4 / (1 - δ) ^ 2 * (1 / (m - 1) - 1 / m) := by
    have hm1 : m - 1 ≠ 0 := by linarith
    have hm0 : m ≠ 0 := by linarith
    have e : 1 / (m - 1) - 1 / m = 1 / ((m - 1) * m) := by field_simp; ring
    rw [e, ha, mul_pow, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)
  calc 4 * (181 / 462) / π ^ 2 * δ * (3 / 4) * (a ^ 2 / (a ^ 2 - 4) ^ 2)
      ≤ 4 * (181 / 462) / π ^ 2 * δ * (3 / 4) * (4 / (1 - δ) ^ 2 * (1 / (m - 1) - 1 / m)) := by
        gcongr; exact h1.trans h2
    _ = 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / (m - 1) - 1 / m) := by ring

/-- The far collar at `m < K ≤ M`: `(4κ_S/π²)δ_m collF(b′, M) ≤ (4κ_S/π²)δ/((K − m) − β₀)`. -/
theorem far_coll_le {δ : ℝ} (hδ : 0 ≤ δ) {m K M : ℕ} (hm : 2 ≤ m) (hmK : m < K) (hKM : K ≤ M) :
    4 * (181 / 462) / π ^ 2 * Cvs.L2a.LocalisedBottomCorners.deltaM δ m
        * collF (bP m (Cvs.L2a.LocalisedBottomCorners.deltaM δ m)) M
      ≤ 4 * (181 / 462) / π ^ 2 * δ * (1 / (((K - m : ℕ) : ℝ) - Cvs.L2a.LocalisedConstants.beta0)) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((K - m : ℕ) : ℝ) = (K : ℝ) - m := by rw [Nat.cast_sub hmK.le]
  have hmK' : (m : ℝ) + 1 ≤ K := by exact_mod_cast hmK
  have hKM' : (K : ℝ) ≤ M := by exact_mod_cast hKM
  obtain ⟨b1, b2⟩ := Cvs.L2a.LocalisedConstants.beta0_bounds
  have hdm : Cvs.L2a.LocalisedBottomCorners.deltaM δ m = Cvs.L2a.LocalisedConstants.deltaM δ m := rfl
  have hd0 : 0 ≤ Cvs.L2a.LocalisedBottomCorners.deltaM δ m :=
    le_min hδ (div_nonneg Cvs.L2a.LocalisedBottomCorners.gZero_pos.le (by positivity))
  have hdδ : Cvs.L2a.LocalisedBottomCorners.deltaM δ m ≤ δ := min_le_left _ _
  have hbP : bP m (Cvs.L2a.LocalisedBottomCorners.deltaM δ m)
      = Cvs.L2a.CornerSuprema.bm m + m * Cvs.L2a.LocalisedConstants.deltaM δ m := by
    unfold bP; rw [mul_add, Cvs.L2a.LocalisedConstants.m_mul_Ymax, hdm]
  have hge := Cvs.L2a.LocalisedConstants.sub_bprime_ge (δ := δ) (M : ℝ) hm2
  have hb := Cvs.L2a.CornerSuprema.lt_bm (m := (m : ℝ)) (by linarith)
  have hβ0 : 0 < bP m (Cvs.L2a.LocalisedBottomCorners.deltaM δ m) := by
    rw [hbP, ← hdm]; nlinarith
  have hpos : 0 < (K : ℝ) - m - Cvs.L2a.LocalisedConstants.beta0 := by linarith
  have hβM : bP m (Cvs.L2a.LocalisedBottomCorners.deltaM δ m) < M := by rw [hbP]; linarith
  have hc := collF_le hβ0 hβM
  have hc0 := Cvs.L2a.LocalisedBottomCorners.collF_nonneg hβ0 hβM
  have h1 : collF (bP m (Cvs.L2a.LocalisedBottomCorners.deltaM δ m)) M
      ≤ 1 / (((K - m : ℕ) : ℝ) - Cvs.L2a.LocalisedConstants.beta0) := by
    rw [hcast]
    refine hc.trans (one_div_le_one_div_of_le hpos ?_)
    rw [hbP]; linarith
  calc 4 * (181 / 462) / π ^ 2 * Cvs.L2a.LocalisedBottomCorners.deltaM δ m * collF (bP m (Cvs.L2a.LocalisedBottomCorners.deltaM δ m)) M
      ≤ 4 * (181 / 462) / π ^ 2 * δ * (1 / (((K - m : ℕ) : ℝ) - Cvs.L2a.LocalisedConstants.beta0)) := by
        gcongr

/-- `F₅₅₀ = 2/g₀ + 1/(2 − β₀) + log((548 − β₀)/(2 − β₀)) ≤ 9.884`. -/
theorem F550_le : 2 / Cvs.L2a.LocalisedConstants.g0 + 1 / (2 - Cvs.L2a.LocalisedConstants.beta0)
    + Real.log ((((550 : ℕ) : ℝ) - 2 - Cvs.L2a.LocalisedConstants.beta0) / (2 - Cvs.L2a.LocalisedConstants.beta0))
    ≤ 9884 / 1000 := by
  obtain ⟨g1, g2⟩ := Cvs.L2a.LocalisedConstants.g0_bounds
  obtain ⟨b1, b2⟩ := Cvs.L2a.LocalisedConstants.beta0_bounds
  have h1 : 2 / Cvs.L2a.LocalisedConstants.g0 ≤ 2 / (69 / 100) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) g1
  have h2 : 1 / (2 - Cvs.L2a.LocalisedConstants.beta0) ≤ 1 / (134 / 100) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : Real.log ((((550 : ℕ) : ℝ) - 2 - Cvs.L2a.LocalisedConstants.beta0) / (2 - Cvs.L2a.LocalisedConstants.beta0))
      ≤ 9 * Real.log 2 := by
    rw [show 9 * Real.log 2 = Real.log (2 ^ 9) by rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (div_pos (by push_cast; linarith) (by linarith)) ?_
    rw [div_le_iff₀ (by linarith)]; push_cast; nlinarith
  have := Real.log_two_lt_d9
  norm_num at h1 h2 this ⊢
  linarith

/-- **The far collars**: `Σ_{2 ≤ m < K} (4κ_S/π²)δ/((K − m) − β₀) ≤ (4κ_S/π²)δ·9.884` for `K ≤ 550`. -/
theorem sum_far_coll_le {δ : ℝ} (hδ : 0 ≤ δ) {K : ℕ} (hK : K ≤ 550) :
    ∑ m ∈ Finset.Ico 2 K, 4 * (181 / 462) / π ^ 2 * δ * (1 / (((K - m : ℕ) : ℝ) - Cvs.L2a.LocalisedConstants.beta0))
      ≤ 4 * (181 / 462) / π ^ 2 * δ * (9884 / 1000) := by
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hr := Finset.sum_Ico_reflect (fun j : ℕ => 1 / ((j : ℝ) - Cvs.L2a.LocalisedConstants.beta0)) 2 (m := K) (n := K)
    (by omega)
  rw [hr, show K + 1 - K = 1 by omega, show K + 1 - 2 = K - 1 by omega]
  exact (Cvs.L2a.LocalisedConstants.sum_inv_beta0_full hK (by norm_num)).trans F550_le

/-- **`Σ lamX ≤ 8.12·10⁻⁴`** at `δ = 1/p²`, `s = 4δ/3`, `c = p⁸`, `p ≥ 100`, every `M ≥ 3`. -/
theorem sum_lamX_le {c δ s p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hδ : δ = 1 / p ^ 2) (hs : s = 4 / 3 * δ)
    {M : ℕ} (hM : 3 ≤ M) :
    ∑ m ∈ Finset.Ico 2 (min M 550), Cvs.L2a.FrameFloorIntegerM.lamX c δ s m M ≤ 812 / 10 ^ 6 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ4 : δ ≤ 1 / 10 ^ 4 := by rw [hδ]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hp6 : 10 ^ 12 ≤ p ^ 6 := by
    calc (10 : ℝ) ^ 12 = 100 ^ 6 := by norm_num
      _ ≤ p ^ 6 := by gcongr
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hπ2 : 9869 / 1000 ≤ π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hπ0 : 0 < π ^ 2 := by positivity
  have hic : 1 / (π ^ 2 * c) ≤ 1 / 10 ^ 16 := by
    rw [hc]; exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have his : 1 / s / (π ^ 2 * c) ≤ 1 / 10 ^ 12 := by
    have e : 1 / s / (π ^ 2 * c) = 3 / 4 / π ^ 2 * (1 / p ^ 6) := by rw [hs, hδ, hc]; field_simp
    rw [e]
    have h1 : 3 / 4 / π ^ 2 ≤ 1 := by rw [div_le_one hπ0]; linarith
    have h2 : 1 / p ^ 6 ≤ 1 / 10 ^ 12 := one_div_le_one_div_of_le (by norm_num) hp6
    calc 3 / 4 / π ^ 2 * (1 / p ^ 6) ≤ 1 * (1 / 10 ^ 12) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 1 / 10 ^ 12 := one_mul _
  set K := min M 550 with hK
  have hK3 : 3 ≤ K := le_min hM (by norm_num)
  have hKM : K ≤ M := min_le_left _ _
  have hK550 : K ≤ 550 := min_le_right _ _
  set farB : ℕ → ℝ := fun m => 4 * (181 / 462) / π ^ 2 * δ
    * (1 / (((K - m : ℕ) : ℝ) - Cvs.L2a.LocalisedConstants.beta0)) with hfarB
  set nearB : ℕ → ℝ := fun m => 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ))
    with hnearB
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have lam_two : Cvs.L2a.FrameFloorIntegerM.lamX c δ s ((2 : ℕ) : ℝ) M
      ≤ 1 / s / (π ^ 2 * c) + 16 * (181 / 462) * δ + 1 / (π ^ 2 * c) + farB 2 := by
    unfold Cvs.L2a.FrameFloorIntegerM.lamX
    rw [if_pos (by norm_num)]
    have a1 : |gT 2 (2 - s)| / (π ^ 2 * c) ≤ 1 / s / (π ^ 2 * c) :=
      div_le_div_of_nonneg_right (abs_gT_two_le hs0 hs1) (by positivity)
    have a2 := sum_shells_le hδ0.le hs0 (nSh s)
    have a3 : gT ((2 : ℕ) : ℝ) M / (π ^ 2 * c) ≤ 1 / (π ^ 2 * c) :=
      div_le_div_of_nonneg_right (gT_M_le (by norm_num) (by push_cast; linarith)).2 (by positivity)
    have a4 := far_coll_le hδ0.le (m := 2) (K := K) (M := M) le_rfl (by omega) hKM
    simp only [hfarB]
    push_cast at a3 a4 ⊢
    linarith
  have lam_m : ∀ m ∈ Finset.Ico 3 K, Cvs.L2a.FrameFloorIntegerM.lamX c δ s (m : ℝ) M
      ≤ 2 * (1 / (π ^ 2 * c)) + nearB m + farB m := fun m hm => by
    obtain ⟨hm3, hmK⟩ := Finset.mem_Ico.1 hm
    have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    unfold Cvs.L2a.FrameFloorIntegerM.lamX
    rw [if_neg (by linarith)]
    have a1 : |gT m 2| / (π ^ 2 * c) ≤ 1 / (π ^ 2 * c) :=
      div_le_div_of_nonneg_right (abs_gT_m_two_le hm3r) (by positivity)
    have a2 := near_coll_le hm3r hδ0.le (by linarith)
    have a3 : gT (m : ℝ) M / (π ^ 2 * c) ≤ 1 / (π ^ 2 * c) := by
      have hmM : (m : ℝ) + 1 ≤ M := by
        have : (m : ℝ) + 1 ≤ K := by exact_mod_cast hmK
        have : (K : ℝ) ≤ M := by exact_mod_cast hKM
        linarith
      exact div_le_div_of_nonneg_right (gT_M_le (by linarith) hmM).2 (by positivity)
    have a4 := far_coll_le hδ0.le (m := m) (K := K) (M := M) (by omega) hmK hKM
    simp only [hfarB, hnearB]
    linarith
  have hsplit := Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < K)
    (fun m : ℕ => Cvs.L2a.FrameFloorIntegerM.lamX c δ s (m : ℝ) M)
  have hfar := sum_far_coll_le hδ0.le (δ := δ) hK550
  have hfar' := Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < K) farB
  have hnear : ∑ m ∈ Finset.Ico 3 K, nearB m ≤ 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / 2) := by
    simp only [hnearB]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have ht := Cvs.L2a.CornerSuprema.sum_Ico_telescope (fun m : ℕ => 1 / ((m : ℝ) - 1)) hK3
    have e : ∀ m ∈ Finset.Ico 3 K, 1 / ((m : ℝ) - 1) - 1 / (m : ℝ)
        = (fun m : ℕ => 1 / ((m : ℝ) - 1)) m - (fun m : ℕ => 1 / ((m : ℝ) - 1)) (m + 1) := fun m _ => by
      simp only; push_cast; ring
    rw [Finset.sum_congr rfl e, ht]
    have hK3r : (3 : ℝ) ≤ K := by exact_mod_cast hK3
    have : 0 ≤ 1 / ((K : ℝ) - 1) := by apply div_nonneg zero_le_one; linarith
    norm_num at this ⊢; linarith
  have hconst : ∑ m ∈ Finset.Ico 3 K, 2 * (1 / (π ^ 2 * c)) ≤ 548 * (2 * (1 / (π ^ 2 * c))) := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    gcongr
    have : K - 3 ≤ 548 := by omega
    exact_mod_cast this
  have hsum_m := Finset.sum_le_sum lam_m
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_m
  rw [show (2 : ℕ) + 1 = 3 from rfl] at hfar' hsplit
  have hfarsum : farB 2 + ∑ m ∈ Finset.Ico 3 K, farB m
      ≤ 4 * (181 / 462) / π ^ 2 * δ * (9884 / 1000) := by
    rw [← hfar']; exact hfar
  -- numerics
  have t2 : 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / 2) ≤ 239 / 10 ^ 7 := by
    have h1 : 12 * (181 / 462) / π ^ 2 ≤ 12 * (181 / 462) / (9869 / 1000) := by gcongr
    have h2 : δ / (1 - δ) ^ 2 ≤ (1 / 10 ^ 4) / (1 - 1 / 10 ^ 4) ^ 2 := by
      gcongr
    calc 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / 2) = 12 * (181 / 462) / π ^ 2 * (δ / (1 - δ) ^ 2) / 2 := by
          ring
      _ ≤ 12 * (181 / 462) / (9869 / 1000) * ((1 / 10 ^ 4) / (1 - 1 / 10 ^ 4) ^ 2) / 2 := by gcongr
      _ ≤ 239 / 10 ^ 7 := by norm_num
  have t3 : 4 * (181 / 462) / π ^ 2 * δ * (9884 / 1000) ≤ 157 / 10 ^ 6 := by
    calc 4 * (181 / 462) / π ^ 2 * δ * (9884 / 1000)
        ≤ 4 * (181 / 462) / (9869 / 1000) * (1 / 10 ^ 4) * (9884 / 1000) := by
          gcongr
      _ ≤ 157 / 10 ^ 6 := by norm_num
  have t1 : 16 * (181 / 462) * δ ≤ 16 * (181 / 462) / 10 ^ 4 := by
    have := mul_le_mul_of_nonneg_left hδ4 (by norm_num : (0 : ℝ) ≤ 16 * (181 / 462)); linarith
  rw [hsplit]
  linarith

end lam

/-! ### The bottom chirp and correction factors -/

section chirp

open Cvs.L2a.LocalisedBottomCorners (tT eSh dSh nSh iSh bP)
open Cvs.L2a.FarIntegrationByParts (wF)

/-- A sum split at `k = 2`: `f_k ≤ A_k` for `k < 2`, `f_k ≤ B_k` beyond. -/
theorem sum_split_two {n : ℕ} {f A B : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    (hf : ∀ k < n, f k ≤ if k < 2 then A k else B k) :
    ∑ k ∈ Finset.range n, f k ≤ (A 0 + A 1) + ∑ k ∈ Finset.range n, B k := by
  have h1 : ∀ k ∈ Finset.range n, f k ≤ (if k < 2 then A k else 0) + B k := fun k hk => by
    have := hf k (Finset.mem_range.1 hk)
    split_ifs at this ⊢ with h
    · linarith [hB k]
    · linarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib]
  gcongr
  rw [← Finset.sum_filter]
  calc ∑ k ∈ Finset.filter (fun k => k < 2) (Finset.range n), A k ≤ ∑ k ∈ Finset.range 2, A k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => hA k)
        simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; exact hk.2
    _ = A 0 + A 1 := by simp [Finset.sum_range_succ]

/-- **The `m = 2` chirp**: `E₂ ≤ (1.387·10⁻³)²`, regime I on shells `k < 2` and regime II beyond. -/
theorem e2_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.e2 c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) J ≤ (1387 / 10 ^ 6) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hc0 : 0 < c := by rw [hc]; positivity
  set s := 4 / 3 * (1 / p ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s * 4 ≤ 1 := by rw [hs]; linarith
  have he0 : eSh s 0 = s := eSh_zero (by linarith)
  have he2 : eSh s 2 = s * 4 := by unfold eSh; norm_num; linarith
  have hπ : 0 < π := pi_pos
  set T₂ : ℝ := (11 / 10 ^ 4) ^ 2 * (1 / 2) ^ 4 + (21 / 10 ^ 6) ^ 2 * (1 / 2) ^ 2 with hT₂
  set A : ℕ → ℝ := fun k => 2 / π * (15 / 10 ^ 7) * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) with hA
  set B : ℕ → ℝ := fun k => 2 / π * T₂ * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) with hB
  have hΔ : ∀ k, 0 ≤ eSh s (k + 1) - eSh s k := fun k => sub_nonneg.2 (eSh_mono hs0.le (Nat.le_succ k))
  have hA0 : ∀ k, 0 ≤ A k := fun k => by simp only [hA]; have := hΔ k; positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => by simp only [hB]; have := hΔ k; positivity
  have hterm : ∀ k < nSh s, 2 / π * tT c 2 (1 / p ^ 2) (dSh (1 / p ^ 2) s k) (eSh s k / 4) J * iSh s k
      ≤ if k < 2 then A k else B k := fun k _ => by
    have hek : s ≤ eSh s k := by have := eSh_mono hs0.le (Nat.zero_le k); rwa [he0] at this
    have hr0 : 0 < eSh s k / 4 := by have := eSh_pos hs0 k; positivity
    have hdk0 : 0 ≤ dSh (1 / p ^ 2) s k := le_min (by positivity) hr0.le
    have hT0 := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := 2) (d := 1 / p ^ 2) (δ := dSh (1 / p ^ 2) s k)
      (r := eSh s k / 4) (J := J) hc0 (by positivity) (by linarith) hdk0 hJ0 hr0
    have hi := iSh_le hs0 k
    have base : ∀ T, tT c 2 (1 / p ^ 2) (dSh (1 / p ^ 2) s k) (eSh s k / 4) J ≤ T →
        2 / π * tT c 2 (1 / p ^ 2) (dSh (1 / p ^ 2) s k) (eSh s k / 4) J * iSh s k
          ≤ 2 / π * T * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) := fun T hT => by
      have := hΔ k
      calc 2 / π * tT c 2 (1 / p ^ 2) (dSh (1 / p ^ 2) s k) (eSh s k / 4) J * iSh s k
          ≤ 2 / π * tT c 2 (1 / p ^ 2) (dSh (1 / p ^ 2) s k) (eSh s k / 4) J
            * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) := by gcongr
        _ ≤ 2 / π * T * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) := by gcongr
    have hs3 : 1 / 3 / p ^ 2 = s / 4 := by rw [hs]; ring
    have hs43 : 4 / 3 / p ^ 2 = s := by rw [hs]; ring
    have hds : 1 / p ^ 2 ≤ s := by rw [hs]; linarith
    split_ifs with hk
    · refine base _ (tT_regI hp hc le_rfl ?_ (min_le_left _ _) ?_ hJ0 hJ)
      · refine le_min (by gcongr; norm_num) ?_
        rw [hs3]; linarith
      · rw [hs3]; linarith
    · have hek2 : s * 4 ≤ eSh s k := by
        have := eSh_mono hs0.le (by omega : 2 ≤ k); rwa [he2] at this
      have hdk : dSh (1 / p ^ 2) s k = 1 / p ^ 2 := min_eq_left (by linarith)
      refine base T₂ ?_
      rw [hdk]
      have := tT_regII (x₀ := 2) hp hc le_rfl (by norm_num) (r := eSh s k / 4) (by rw [hs43]; linarith) hJ0 hJ
      simpa [hT₂] using this
  unfold Cvs.L2a.LocalisedBottomCorners.e2
  refine (sum_split_two hA0 hB0 hterm).trans ?_
  have hAs : A 0 + A 1 = 8 * π * (15 / 10 ^ 7) * (eSh s 2 - eSh s 0) := by
    simp only [hA]; field_simp; ring
  have hBs : ∑ k ∈ Finset.range (nSh s), B k = 8 * π * T₂ * (eSh s (nSh s) - eSh s 0) := by
    simp only [hB]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub (eSh s)]
    field_simp; ring
  rw [hAs, hBs, he0, he2]
  have hn1 := eSh_le_one s (nSh s)
  have hπ4 : π ≤ 31416 / 10000 := pi_bounds.2
  have hsle : s ≤ 4 / 3 * (1 / 10 ^ 4) := by rw [hs]; linarith
  have hT₂0 : 0 ≤ T₂ := by positivity
  calc 8 * π * (15 / 10 ^ 7) * (s * 4 - s) + 8 * π * T₂ * (eSh s (nSh s) - s)
      ≤ 8 * π * (15 / 10 ^ 7) * (3 * (4 / 3 * (1 / 10 ^ 4))) + 8 * π * T₂ * 1 := by
        gcongr
        · linarith
        · linarith
    _ ≤ 8 * (31416 / 10000) * (15 / 10 ^ 7) * (3 * (4 / 3 * (1 / 10 ^ 4))) + 8 * (31416 / 10000) * T₂ * 1 := by
        gcongr
    _ ≤ (1387 / 10 ^ 6) ^ 2 := by rw [hT₂]; norm_num

/-- **The near chirps** `m ≥ 3`: `E^n_m ≤ (0.5644(11·10⁻⁴u² + 21·10⁻⁶u))²`, `u = 1/m`, for `m ≤ 549`. -/
theorem eN_le {c J p m : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hm3 : 3 ≤ m) (hm549 : m ≤ 549) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.eN c (1 / p ^ 2) (1 / p ^ 2) m J
      ≤ (5644 / 10 ^ 4 * (11 / 10 ^ 4 * (1 / m) ^ 2 + 21 / 10 ^ 6 * (1 / m))) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hm0 : 0 < m := by linarith
  set δ := 1 / p ^ 2 with hδ
  set a := m * (1 - δ) with ha
  have ha2 : 9997 / 10000 ≤ a - 2 := by rw [ha]; nlinarith
  have hr : 4 / 3 / p ^ 2 ≤ (a - 2) / m := by
    rw [le_div_iff₀ hm0]
    have : 4 / 3 / p ^ 2 = 4 / 3 * δ := by rw [hδ]; ring
    rw [this]; nlinarith
  have hT := tT_regII hp hc (by linarith) hm549 hr hJ0 hJ
  have hT0 := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := m) (d := δ) (δ := δ) (r := (a - 2) / m) (J := J) hc0
    hd0.le (by linarith) hd0.le hJ0 (by positivity)
  have hD : 1 / (a - 2) - 1 / (a - 1) ≤ 1 / 2 + 1 / 3000 := by
    have e : 1 / (a - 2) - 1 / (a - 1) = 1 / ((a - 2) * (a - 1)) := by
      have : a - 2 ≠ 0 := by linarith
      have : a - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    have : (9997 / 10000) * (19997 / 10000) ≤ (a - 2) * (a - 1) := by nlinarith
    calc 1 / ((a - 2) * (a - 1)) ≤ 1 / ((9997 / 10000) * (19997 / 10000)) :=
          one_div_le_one_div_of_le (by norm_num) this
      _ ≤ 1 / 2 + 1 / 3000 := by norm_num
  have hD0 : 0 ≤ 1 / (a - 2) - 1 / (a - 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hπ : 2 / π ≤ 2 / (31415 / 10000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_bounds.1
  set u := 1 / m with hu
  have hu0 : 0 < u := by positivity
  have hW : (11 / 10 ^ 4) ^ 2 * u ^ 4 + (21 / 10 ^ 6) ^ 2 * u ^ 2 ≤ (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2 := by
    nlinarith [pow_pos hu0 3]
  unfold Cvs.L2a.LocalisedBottomCorners.eN
  calc 2 / π * tT c m δ δ ((a - 2) / m) J * (1 / (a - 2) - 1 / (a - 1))
      ≤ 2 / (31415 / 10000) * ((11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) * (1 / 2 + 1 / 3000) := by
        gcongr
        exact hT.trans hW
    _ ≤ (5644 / 10 ^ 4 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u)) ^ 2 := by
        rw [mul_pow]
        have : 0 ≤ (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2 := sq_nonneg _
        nlinarith

/-- **The far chirps** `2 ≤ m ≤ 549`, `m < M`: `E^f_m ≤ (1.0302(11·10⁻⁴u² + 21·10⁻⁶u))²`, `u = 1/m`. -/
theorem eFar_le {c J p : ℝ} {m M : ℕ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hm2 : 2 ≤ m) (hm549 : m ≤ 549)
    (hmM : m + 1 ≤ M) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.eFar c (1 / p ^ 2) (Cvs.L2a.LocalisedBottomCorners.deltaM (1 / p ^ 2) m) m M J
      ≤ (10302 / 10 ^ 4 * (11 / 10 ^ 4 * (1 / (m : ℝ)) ^ 2 + 21 / 10 ^ 6 * (1 / (m : ℝ)))) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm549r : (m : ℝ) ≤ 549 := by exact_mod_cast hm549
  have hmMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨g1, -⟩ := Cvs.L2a.LocalisedConstants.g0_bounds
  have hgz : Cvs.L2a.LocalisedBottomCorners.gZero = Cvs.L2a.LocalisedConstants.g0 := rfl
  have hdm : Cvs.L2a.LocalisedBottomCorners.deltaM (1 / p ^ 2) m = 1 / p ^ 2 := by
    refine min_eq_left ?_
    rw [hgz, le_div_iff₀ (by positivity)]
    nlinarith
  rw [hdm]
  set δ := 1 / p ^ 2 with hδ
  have hbP : bP m δ = Cvs.L2a.CornerSuprema.bm m + m * δ := by
    unfold bP; rw [mul_add, Cvs.L2a.LocalisedConstants.m_mul_Ymax]
  have hg := Cvs.L2a.LocalisedConstants.g0_le_sub_bm hm2r hmMr
  have hmδ : (m : ℝ) * δ ≤ 549 / 10 ^ 4 := by
    calc (m : ℝ) * δ ≤ 549 * (1 / 10 ^ 4) := mul_le_mul hm549r hd4 hd0.le (by norm_num)
      _ = 549 / 10 ^ 4 := by ring
  have hgap : 6 / 10 ≤ (M : ℝ) - bP m δ := by rw [hbP]; linarith
  have hr : 4 / 3 / p ^ 2 ≤ ((M : ℝ) - bP m δ) / m := by
    rw [le_div_iff₀ hm0]
    have : 4 / 3 / p ^ 2 = 4 / 3 * δ := by rw [hδ]; ring
    rw [this]; nlinarith
  have hT := tT_regII hp hc hm2r hm549r hr hJ0 hJ
  have hT0 := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := m) (d := δ) (δ := δ) (r := ((M : ℝ) - bP m δ) / m)
    (J := J) hc0 hd0.le (by linarith) hd0.le hJ0 (by apply div_pos <;> linarith)
  have hπ : 2 / π ≤ 2 / (31415 / 10000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_bounds.1
  set u := 1 / (m : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hW : (11 / 10 ^ 4) ^ 2 * u ^ 4 + (21 / 10 ^ 6) ^ 2 * u ^ 2 ≤ (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2 := by
    nlinarith [pow_pos hu0 3]
  unfold Cvs.L2a.LocalisedBottomCorners.eFar
  calc 2 / π * tT c m δ δ (((M : ℝ) - bP m δ) / m) J / ((M : ℝ) - bP m δ)
      ≤ 2 / (31415 / 10000) * ((11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) / (6 / 10) := by
        gcongr
        exact hT.trans hW
    _ ≤ (10302 / 10 ^ 4 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u)) ^ 2 := by
        rw [mul_pow]
        have : 0 ≤ (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2 := sq_nonneg _
        nlinarith

end chirp

/-! ### The bottom correction factors and the assembled chirp sum -/

section corr

open Cvs.L2a.FarIntegrationByParts (wF)

theorem sqrt_le_of_le_sq {x X : ℝ} (hX : 0 ≤ X) (h : x ≤ X ^ 2) : √x ≤ X := by
  rw [Real.sqrt_le_left hX]; exact h

/-- The `m = 2` correction integrand: `(1 − wF)K_near²env_n ≤ 300/(2 − t)⁴` on `[1, 2)`, `c ≥ 1`. -/
theorem k2_integrand_le {c t : ℝ} (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    ‖(1 - wF t) * Cvs.L2a.CutKernelSimplified.kNear c 2 (t / 2) (Ymax 2) ^ 2 * Cvs.L2a.LocalisedBottomCorners.envN 2 t‖
      ≤ 300 / (2 - t) ^ 4 := by
  set v := 2 - t with hv
  have hv0 : 0 < v := by linarith
  have hv1 : v ≤ 1 := by linarith
  have hw0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hw : 1 - wF t ≤ 10 * v ^ 2 := by
    have := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
    have hπ : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith [sq_nonneg v]
  have hY1 := one_le_Ymax (x := (2 : ℝ)) (by norm_num)
  have hY2 : Ymax 2 ≤ 7 / 6 := by have := Ymax_sub_lt (x₀ := 2) le_rfl; norm_num at this; linarith
  set y := t / 2 with hy
  have hy0 : 1 / 2 ≤ y := by rw [hy]; linarith
  have hy1 : y ≤ 1 := by rw [hy]; linarith
  have h1y : 3 * v / 4 ≤ 1 - y ^ 2 := by rw [hy, hv]; nlinarith
  have hpP : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP 2 = 3 := by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; norm_num
  have hyc : y / c ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hyc0 : 0 ≤ y / c := by positivity
  have k1 : 2 * 2 * y / (3 * (1 - y ^ 2)) ≤ 16 / (9 * v) := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]; nlinarith
  have k2 : 2 * (2 + y / c) * (y + Ymax 2) / (3 * (1 - y ^ 2) ^ 2) ≤ 208 / (27 * v ^ 2) := by
    have hn : 2 * (2 + y / c) * (y + Ymax 2) ≤ 13 := by nlinarith
    have hd : 27 * v ^ 2 / 16 ≤ 3 * (1 - y ^ 2) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h1y 2; nlinarith
    calc 2 * (2 + y / c) * (y + Ymax 2) / (3 * (1 - y ^ 2) ^ 2) ≤ 13 / (27 * v ^ 2 / 16) :=
          div_le_div₀ (by norm_num) hn (by positivity) hd
      _ = 208 / (27 * v ^ 2) := by field_simp; ring
  have kN0 : 0 ≤ Cvs.L2a.CutKernelSimplified.kNear c 2 y (Ymax 2) := by
    unfold Cvs.L2a.CutKernelSimplified.kNear; rw [hpP]
    have : 0 < 1 - y ^ 2 := by nlinarith
    positivity
  have kNle : Cvs.L2a.CutKernelSimplified.kNear c 2 y (Ymax 2) ≤ 10 / v ^ 2 := by
    unfold Cvs.L2a.CutKernelSimplified.kNear; rw [hpP]
    have : 16 / (9 * v) ≤ 16 / (9 * v ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have e : 16 / (9 * v ^ 2) + 208 / (27 * v ^ 2) = 256 / 27 / v ^ 2 := by field_simp; ring
    have : 256 / 27 / v ^ 2 ≤ 10 / v ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have he0 : 0 ≤ Cvs.L2a.LocalisedBottomCorners.envN 2 t := by
    unfold Cvs.L2a.LocalisedBottomCorners.envN; positivity
  have he : Cvs.L2a.LocalisedBottomCorners.envN 2 t ≤ 8 / (27 * v ^ 2) := by
    unfold Cvs.L2a.LocalisedBottomCorners.envN
    have h4 : 3 * v ≤ 2 ^ 2 - t ^ 2 := by rw [hv]; nlinarith
    have h4' : 9 * v ^ 2 ≤ (2 ^ 2 - t ^ 2) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h4 2; nlinarith
    rw [div_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  rw [Real.norm_of_nonneg (by positivity)]
  have hk2 : Cvs.L2a.CutKernelSimplified.kNear c 2 y (Ymax 2) ^ 2 ≤ (10 / v ^ 2) ^ 2 := pow_le_pow_left₀ kN0 kNle 2
  calc (1 - wF t) * Cvs.L2a.CutKernelSimplified.kNear c 2 y (Ymax 2) ^ 2 * Cvs.L2a.LocalisedBottomCorners.envN 2 t
      ≤ 10 * v ^ 2 * (10 / v ^ 2) ^ 2 * (8 / (27 * v ^ 2)) := by gcongr
    _ = 8000 / 27 / v ^ 4 := by field_simp; ring
    _ ≤ 300 / v ^ 4 := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- `K₂ ≤ 10⁻¹³` at `s = (4/3)/p²`, `c = p⁸`. -/
theorem k2_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.k2 c (4 / 3 * (1 / p ^ 2)) J ≤ 1 / 10 ^ 13 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  set s := 4 / 3 * (1 / p ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hs1 : s ≤ 1 / 2 := by rw [hs]; linarith
  obtain ⟨hk0, hk1⟩ := Cvs.L2a.LocalisedConstants.kappaI_mem (J := J) (c := c) (by linarith) hJ0 hJ
  have hkap : Cvs.L2a.LocalisedBottomCorners.kapI c J = Cvs.L2a.LocalisedConstants.kappaI J c := rfl
  have hint : ∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * Cvs.L2a.CutKernelSimplified.kNear c 2 (t / 2) (Ymax 2) ^ 2
      * Cvs.L2a.LocalisedBottomCorners.envN 2 t ≤ 300 / s ^ 4 := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 300 / s ^ 4) fun x hx => ?_).trans ?_
    · rw [Set.uIoc_of_le (by linarith)] at hx
      refine (k2_integrand_le hc1 hx.1.le (by linarith [hx.2])).trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hs0.le (by linarith [hx.2]) 4)
    · rw [abs_of_nonneg (by linarith)]
      have : 0 ≤ 300 / s ^ 4 := by positivity
      nlinarith
  unfold Cvs.L2a.LocalisedBottomCorners.k2
  rw [hkap]
  have hc2 : 0 < c ^ 2 := by positivity
  calc Cvs.L2a.LocalisedConstants.kappaI J c / c ^ 2 * ∫ t in (1 : ℝ)..(2 - s), (1 - wF t)
        * Cvs.L2a.CutKernelSimplified.kNear c 2 (t / 2) (Ymax 2) ^ 2 * Cvs.L2a.LocalisedBottomCorners.envN 2 t
      ≤ Cvs.L2a.LocalisedConstants.kappaI J c / c ^ 2 * (300 / s ^ 4) := by gcongr
    _ ≤ 1 / c ^ 2 * (300 / s ^ 4) := by gcongr
    _ = 300 * 81 / 256 / p ^ 8 := by rw [hc, hs]; field_simp; ring
    _ ≤ 300 * 81 / 256 / 10 ^ 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp8
    _ ≤ 1 / 10 ^ 13 := by norm_num

theorem kFb_le {c : ℝ} (hc : 40 ≤ c) : Cvs.L2a.LocalisedBottomCorners.kFb c ≤ 8 := by
  unfold Cvs.L2a.LocalisedBottomCorners.kFb
  have : 40 / (11 * c) ≤ 40 / (11 * 40) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

/-- `K^n_m ≤ 64/c²` for `m ≥ 3`, `K^f_m ≤ 64/c²` for `2 ≤ m ≤ M − 1`. -/
theorem kN_kF_le {c J m M : ℝ} (hc : 85 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hm2 : 2 ≤ m) (hmM : m + 1 ≤ M) :
    (3 ≤ m → Cvs.L2a.LocalisedBottomCorners.kN c J m ≤ 64 / c ^ 2) ∧ Cvs.L2a.LocalisedBottomCorners.kF c J m M ≤ 64 / c ^ 2 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hk0, hk1⟩ := Cvs.L2a.LocalisedConstants.kappaI_mem (J := J) (c := c) hc hJ0 hJ
  have hkap : Cvs.L2a.LocalisedBottomCorners.kapI c J = Cvs.L2a.LocalisedConstants.kappaI J c := rfl
  have hF8 := kFb_le (c := c) (by linarith)
  have hN0 : 0 ≤ Cvs.L2a.LocalisedBottomCorners.kNb := by unfold Cvs.L2a.LocalisedBottomCorners.kNb; positivity
  have hN8 : Cvs.L2a.LocalisedBottomCorners.kNb ≤ 8 := (Cvs.L2a.LocalisedBottomCorners.kNb_le_kFb hc0).trans hF8
  have hF0 : 0 ≤ Cvs.L2a.LocalisedBottomCorners.kFb c := hN0.trans (Cvs.L2a.LocalisedBottomCorners.kNb_le_kFb hc0)
  have hm1 : 3 ≤ m ^ 2 - 1 := by nlinarith
  refine ⟨fun hm3 => ?_, ?_⟩
  · unfold Cvs.L2a.LocalisedBottomCorners.kN
    rw [hkap]
    have hn0 := Cvs.L2a.CornerSuprema.nearN_nonneg hm3
    have hn : Cvs.L2a.CornerSuprema.nearN m / (m ^ 2 - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      unfold Cvs.L2a.CornerSuprema.nearN
      have : 2 / (m ^ 2 - 4) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
      have : 0 ≤ 1 / (m ^ 2 - 1) := by positivity
      nlinarith
    calc (Cvs.L2a.LocalisedBottomCorners.kNb / c) ^ 2 * Cvs.L2a.LocalisedConstants.kappaI J c * Cvs.L2a.CornerSuprema.nearN m
          / (m ^ 2 - 1)
        = (Cvs.L2a.LocalisedBottomCorners.kNb / c) ^ 2 * Cvs.L2a.LocalisedConstants.kappaI J c
          * (Cvs.L2a.CornerSuprema.nearN m / (m ^ 2 - 1)) := by ring
      _ ≤ (8 / c) ^ 2 * 1 * 1 := by gcongr
      _ = 64 / c ^ 2 := by ring
  · unfold Cvs.L2a.LocalisedBottomCorners.kF
    rw [hkap]
    have hf0 := Cvs.L2a.CornerSuprema.farF_nonneg hm2 hmM
    have hg := Cvs.L2a.LocalisedConstants.g0_le_sub_bm hm2 hmM
    have hg0 := Cvs.L2a.LocalisedConstants.g0_bounds.1
    have hb := Cvs.L2a.CornerSuprema.lt_bm (m := m) (by linarith)
    have hf : Cvs.L2a.CornerSuprema.farF m M / (m ^ 2 - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      unfold Cvs.L2a.CornerSuprema.farF
      have hMb : 69 / 100 * (M + Cvs.L2a.CornerSuprema.bm m) ≤ M ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2 := by
        nlinarith
      have hpos : 0 < M ^ 2 - Cvs.L2a.CornerSuprema.bm m ^ 2 := by nlinarith
      rw [div_le_iff₀ hpos]
      nlinarith [mul_le_mul hm1 hMb (by nlinarith) (by linarith)]
    calc (Cvs.L2a.LocalisedBottomCorners.kFb c / c) ^ 2 * Cvs.L2a.LocalisedConstants.kappaI J c * Cvs.L2a.CornerSuprema.farF m M
          / (m ^ 2 - 1)
        = (Cvs.L2a.LocalisedBottomCorners.kFb c / c) ^ 2 * Cvs.L2a.LocalisedConstants.kappaI J c
          * (Cvs.L2a.CornerSuprema.farF m M / (m ^ 2 - 1)) := by ring
      _ ≤ (8 / c) ^ 2 * 1 * 1 := by gcongr
      _ = 64 / c ^ 2 := by ring

/-- `K_m ≤ (10⁻⁶)²` for `2 ≤ m ≤ M − 1`. -/
theorem kT_le {c J p : ℝ} {m M : ℕ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1)
    (hm2 : 2 ≤ m) (hmM : m + 1 ≤ M) :
    Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J ≤ (1 / 10 ^ 6) ^ 2 := by
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc16 : 10 ^ 16 ≤ c := by rw [hc]; exact hp8
  have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  obtain ⟨hN, hF⟩ := kN_kF_le (J := J) (by linarith) hJ0 hJ hm2r hmMr
  have hc2 : 64 / c ^ 2 ≤ 64 / 10 ^ 32 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  unfold Cvs.L2a.LocalisedBottomCorners.kT
  split_ifs with h
  · have := k2_le hp hc hJ0 hJ; norm_num at hc2 this ⊢; linarith
  · have hm3 : (3 : ℝ) ≤ m := by
      have : m ≠ 2 := fun h' => h (by rw [h']; norm_num)
      exact_mod_cast (show 3 ≤ m by omega)
    have := hN hm3; norm_num at hc2 ⊢; linarith

/-- `Σ_{3 ≤ m < K} 1/m² ≤ 1/2`. -/
theorem sum_inv_sq_le (K : ℕ) (hK : 3 ≤ K) : ∑ m ∈ Finset.Ico 3 K, (1 / (m : ℝ)) ^ 2 ≤ 1 / 2 := by
  have ht := Cvs.L2a.CornerSuprema.sum_Ico_telescope (fun m : ℕ => 1 / ((m : ℝ) - 1)) hK
  have hterm : ∀ m ∈ Finset.Ico 3 K, (1 / (m : ℝ)) ^ 2
      ≤ (fun m : ℕ => 1 / ((m : ℝ) - 1)) m - (fun m : ℕ => 1 / ((m : ℝ) - 1)) (m + 1) := fun m hm => by
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
    simp only; push_cast
    rw [show (m : ℝ) + 1 - 1 = m by ring]
    have e : 1 / ((m : ℝ) - 1) - 1 / m = 1 / ((m - 1) * m) := by
      have : (m : ℝ) - 1 ≠ 0 := by linarith
      have : (m : ℝ) ≠ 0 := by linarith
      field_simp; ring
    rw [e, div_pow, one_pow, sq]
    exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [ht]
  have hK3r : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have : 0 ≤ 1 / ((K : ℝ) - 1) := by apply div_nonneg zero_le_one; linarith
  push_cast; norm_num; linarith

/-- `Σ_{3 ≤ m < K} 1/m ≤ 7` for `K ≤ 550`, from `1/m ≤ log m − log(m − 1)`. -/
theorem sum_inv_le (K : ℕ) (hK3 : 3 ≤ K) (hK : K ≤ 550) : ∑ m ∈ Finset.Ico 3 K, 1 / (m : ℝ) ≤ 7 := by
  have ht := Cvs.L2a.CornerSuprema.sum_Ico_telescope (fun m : ℕ => -Real.log ((m : ℝ) - 1)) hK3
  have hterm : ∀ m ∈ Finset.Ico 3 K, 1 / (m : ℝ)
      ≤ (fun m : ℕ => -Real.log ((m : ℝ) - 1)) m - (fun m : ℕ => -Real.log ((m : ℝ) - 1)) (m + 1) :=
    fun m hm => by
      have h3 : (3 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
      have := Cvs.L2a.LocalisedConstants.inv_le_log_sub (x := (m : ℝ) - 1) (y := m) (by linarith) (by linarith)
      rw [show (m : ℝ) - ((m : ℝ) - 1) = 1 by ring, div_one] at this
      simp only; push_cast
      rw [show (m : ℝ) + 1 - 1 = m by ring]
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [ht]
  have hK3r : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  have hKr : (K : ℝ) ≤ 550 := by exact_mod_cast hK
  have h2 : 0 ≤ Real.log ((3 : ℕ) - 1 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : Real.log ((K : ℝ) - 1) ≤ 10 * Real.log 2 := by
    rw [show 10 * Real.log 2 = Real.log (2 ^ 10) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by linarith) (by norm_num; linarith)
  have := Real.log_two_lt_d9
  push_cast at h2 ⊢
  norm_num at this
  linarith

end corr

/-! ### `resB ≤ 41/1000` -/

section bottom

/-- **The chirp and correction sum**: `2Σ_{2 ≤ m < min(M, 550)}(√E_m + √K_m) ≤ 1/100`. -/
theorem sum_E_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {M : ℕ}
    (hM : 3 ≤ M) :
    2 * ∑ m ∈ Finset.Ico 2 (min M 550),
        (√(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M J)
          + √(Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J)) ≤ 1 / 100 := by
  set K := min M 550 with hK
  have hK3 : 3 ≤ K := le_min hM (by norm_num)
  have hKM : K ≤ M := min_le_left _ _
  have hK550 : K ≤ 550 := min_le_right _ _
  set W : ℕ → ℝ := fun m => 11 / 10 ^ 4 * (1 / (m : ℝ)) ^ 2 + 21 / 10 ^ 6 * (1 / (m : ℝ)) with hW
  have hW0 : ∀ m, 0 ≤ W m := fun m => by simp only [hW]; positivity
  have hk : ∀ m ∈ Finset.Ico 2 K, √(Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J) ≤ 1 / 10 ^ 6 :=
    fun m hm => by
      obtain ⟨hm2, hmK⟩ := Finset.mem_Ico.1 hm
      exact sqrt_le_of_le_sq (by norm_num) (kT_le hp hc hJ0 hJ hm2 (by omega))
  have he2 : √(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) ((2 : ℕ) : ℝ) M J)
      ≤ 1387 / 10 ^ 6 + 10302 / 10 ^ 4 * W 2 := by
    refine sqrt_le_of_le_sq (by have := hW0 2; positivity) ?_
    unfold Cvs.L2a.LocalisedBottomCorners.eT
    rw [if_pos (by norm_num)]
    have a := e2_le hp hc hJ0 hJ
    have b := eFar_le hp hc (m := 2) (M := M) le_rfl (by norm_num) (by omega) hJ0 hJ
    have : 0 ≤ 1387 / 10 ^ 6 * (10302 / 10 ^ 4 * W 2) := by have := hW0 2; positivity
    simp only [hW] at this ⊢
    nlinarith
  have hem : ∀ m ∈ Finset.Ico 3 K,
      √(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M J)
        ≤ (5644 / 10 ^ 4 + 10302 / 10 ^ 4) * W m := fun m hm => by
    obtain ⟨hm3, hmK⟩ := Finset.mem_Ico.1 hm
    have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hm549 : (m : ℝ) ≤ 549 := by exact_mod_cast (show m ≤ 549 by omega)
    refine sqrt_le_of_le_sq (by have := hW0 m; positivity) ?_
    unfold Cvs.L2a.LocalisedBottomCorners.eT
    rw [if_neg (by linarith)]
    have a := eN_le hp hc hm3r hm549 hJ0 hJ
    have b := eFar_le hp hc (m := m) (M := M) (by omega) (by omega) (by omega) hJ0 hJ
    have : 0 ≤ 5644 / 10 ^ 4 * W m * (10302 / 10 ^ 4 * W m) := by have := hW0 m; positivity
    simp only [hW] at this ⊢
    nlinarith
  have hsplit := Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < K)
    (fun m : ℕ => √(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M J))
  rw [show (2 : ℕ) + 1 = 3 from rfl] at hsplit
  have hsumW : ∑ m ∈ Finset.Ico 3 K, W m ≤ 11 / 10 ^ 4 * (1 / 2) + 21 / 10 ^ 6 * 7 := by
    simp only [hW]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_inv_sq_le K hK3
    have h2 := sum_inv_le K hK3 hK550
    gcongr
  have hEm := Finset.sum_le_sum hem
  rw [← Finset.mul_sum] at hEm
  have hKsum : ∑ m ∈ Finset.Ico 2 K, √(Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J)
      ≤ 548 * (1 / 10 ^ 6) := by
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    gcongr
    have : K - 2 ≤ 548 := by omega
    exact_mod_cast this
  have hW2 : W 2 = 11 / 10 ^ 4 * (1 / 2) ^ 2 + 21 / 10 ^ 6 * (1 / 2) := by simp only [hW]; norm_num
  rw [Finset.sum_add_distrib, hsplit]
  rw [hW2] at he2
  nlinarith

/-- `𝒮_b ≤ 10⁻⁴` at `s = (4/3)/p²`, `c = p⁸`, `0 ≤ J ≤ c/4 + 1`. -/
theorem stripB_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.stripB c (4 / 3 * (1 / p ^ 2)) J ≤ 1 / 10 ^ 4 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc0 : 0 < c := by rw [hc]; positivity
  set s := 4 / 3 * (1 / p ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 4 / 3 * (1 / 10 ^ 4) := by rw [hs]; linarith
  obtain ⟨hπ1, hπ2⟩ := pi_bounds
  have hJc : J / c ≤ 2501 / 10000 := by
    rw [div_le_iff₀ hc0]; rw [hc] at hJ ⊢; nlinarith
  have hX : π * J * s / c ≤ (103 / 10000) ^ 2 := by
    have e : π * J * s / c = π * (J / c) * s := by ring
    rw [e]
    calc π * (J / c) * s ≤ 31416 / 10000 * (2501 / 10000) * (4 / 3 * (1 / 10 ^ 4)) := by
          gcongr
      _ ≤ (103 / 10000) ^ 2 := by norm_num
  have hsq : √(π * J * s / c) ≤ 103 / 10000 := sqrt_le_of_le_sq (by norm_num) hX
  have hF : 8 / (4 - s) + 2 * s / (2 - s) ≤ 8 / 3 + 2 := by
    have h1 : 8 / (4 - s) ≤ 8 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h2 : 2 * s / (2 - s) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hF0 : 0 ≤ 8 / (4 - s) + 2 * s / (2 - s) := by
    have : 0 < 4 - s := by linarith
    have : 0 < 2 - s := by linarith
    positivity
  unfold Cvs.L2a.LocalisedBottomCorners.stripB
  calc 2 * π * s * √(π * J * s / c) * (8 / (4 - s) + 2 * s / (2 - s))
      ≤ 2 * (31416 / 10000) * (4 / 3 * (1 / 10 ^ 4)) * (103 / 10000) * (8 / 3 + 2) := by gcongr
    _ ≤ 1 / 10 ^ 4 := by norm_num

/-- The tail `[M > 550](k_f/c)T̄_bot(550) ≤ 10⁻¹⁰` for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1`. -/
theorem tail_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (M : ℕ) :
    (if 550 < M then Cvs.L2a.LocalisedBottomCorners.kFb c / c
        * Cvs.L2a.CornerSuprema.Tbar (Cvs.L2a.LocalisedBottomCorners.kapI c J) 550 else 0) ≤ 1 / 10 ^ 10 := by
  split_ifs
  · have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
    obtain ⟨-, hk1⟩ := Cvs.L2a.LocalisedConstants.kappaI_mem (J := J) (c := c) (by linarith) hJ0 hJ
    have hT := Cvs.L2a.LocalisedConstants.Tbar_le_one hk1 (m := 550) (by norm_num)
    have hT0 := Cvs.L2a.CornerSuprema.Tbar_nonneg (κ := Cvs.L2a.LocalisedConstants.kappaI J c) (m := 550) (by norm_num)
    have hT1 := Cvs.L2a.LocalisedConstants.Tbar_r1glob_550_le
    have hr0 : 0 ≤ Cvs.L2a.CornerSuprema.r1globBar 1 (Cvs.L2a.CornerSuprema.Theta 2) 551 := by
      unfold Cvs.L2a.CornerSuprema.r1globBar
      have := Cvs.L2a.CornerSuprema.Nbar_nonneg (θ := Cvs.L2a.CornerSuprema.Theta 2)
        (le_trans (by norm_num) Cvs.L2a.CornerSuprema.Theta_two_ge) 551 (by norm_num)
      positivity
    have hF := kFb_le (c := c) (by linarith)
    have hF0 : 0 ≤ Cvs.L2a.LocalisedBottomCorners.kFb c := by
      unfold Cvs.L2a.LocalisedBottomCorners.kFb; positivity
    have hkap : Cvs.L2a.LocalisedBottomCorners.kapI c J = Cvs.L2a.LocalisedConstants.kappaI J c := rfl
    rw [hkap]
    calc Cvs.L2a.LocalisedBottomCorners.kFb c / c * Cvs.L2a.CornerSuprema.Tbar (Cvs.L2a.LocalisedConstants.kappaI J c) 550
        ≤ 8 / 10 ^ 16 * (1238 / 10000) := by
          gcongr
          linarith
      _ ≤ 1 / 10 ^ 10 := by norm_num
  · norm_num

/-- **`resB ≤ 41/1000`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1` and every integer `M ≥ 3`. -/
theorem resB_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {M : ℕ} (hM : 3 ≤ M) :
    Cvs.L2a.FrameFloorIntegerM.resB c J M ≤ 41 / 1000 := by
  obtain ⟨p, hp, hδ, hcp⟩ := scale_p hc
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hs : Cvs.L2a.TopCornerSum.sS c = 4 / 3 * (1 / p ^ 2) := by unfold Cvs.L2a.TopCornerSum.sS; rw [hδ]
  have hW := Cvs.L2a.CornerSuprema.rbot_le M (min M 550) (min_le_left _ _)
  have hWs : √(∑ m ∈ Finset.Ico 2 (min M 550), (Cvs.L2a.CornerSuprema.Lnear (m : ℝ)
      + Cvs.L2a.CornerSuprema.Lfar (m : ℝ) (M : ℝ))) ≤ 20192 / 100000 :=
    (Real.sqrt_le_sqrt hW).trans Cvs.L2a.LocalisedConstants.sqrt_rbarBotSq_le
  have hL := sum_lamX_le hp hcp rfl rfl hM
  have hLs : √(∑ m ∈ Finset.Ico 2 (min M 550), Cvs.L2a.FrameFloorIntegerM.lamX c (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M)
      ≤ 285 / 10000 := sqrt_le_of_le_sq (by norm_num) (hL.trans (by norm_num))
  have hE := sum_E_le hp hcp hJ0 hJ hM
  have hS := stripB_le hp hcp hJ0 hJ
  have hT := tail_le hc hJ0 hJ M
  have hπ : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hd2 : (1 / p ^ 2) ^ 2 ≤ (1 / 10 ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) hd4 2
  have hpd : π ^ 2 * (1 / p ^ 2) ^ 2 ≤ 10 * (1 / 10 ^ 4) ^ 2 := by gcongr
  unfold Cvs.L2a.FrameFloorIntegerM.resB
  rw [hs, hδ]
  have a1 : π ^ 2 * (1 / p ^ 2) ^ 2 * √(∑ m ∈ Finset.Ico 2 (min M 550), (Cvs.L2a.CornerSuprema.Lnear (m : ℝ)
      + Cvs.L2a.CornerSuprema.Lfar (m : ℝ) (M : ℝ))) ≤ 10 * (1 / 10 ^ 4) ^ 2 * (20192 / 100000) := by
    gcongr
  have a2 : (1 + π ^ 2 * (1 / p ^ 2) ^ 2)
      * √(∑ m ∈ Finset.Ico 2 (min M 550), Cvs.L2a.FrameFloorIntegerM.lamX c (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M)
      ≤ (1 + 10 * (1 / 10 ^ 4) ^ 2) * (285 / 10000) := by gcongr
  norm_num at a1 a2 hE hS hT ⊢
  linarith

end bottom

/-! ### The top: shells against `Θ₂²` -/

section shells

open Cvs.L2a.TopCornerSum (shellSet dK collSh psiSh)
open Cvs.L2a.CornerSuprema (theta2Int)
open Cvs.L2a.FarIntegrationByParts (wF)

/-- **The shells tile `(1, 2 − u₀]`**: `Σ_{k<K} ∫_{shell_k} f ≤ ∫₁² f` for `f ≥ 0` integrable on `[1, 2]`,
`0 < u₀`, `u_K = 1`, `u` monotone. -/
theorem shells_sum_le {f : ℝ → ℝ} {u : ℕ → ℝ} {K : ℕ} (hf0 : ∀ t ∈ Icc (1 : ℝ) 2, 0 ≤ f t)
    (hfi : IntervalIntegrable f volume 1 2) (hu0 : 0 < u 0) (huK : u K = 1) (hmono : Monotone u) :
    ∑ k ∈ Finset.range K, ∫ t in shellSet u k, f t ≤ ∫ t in (1 : ℝ)..2, f t := by
  have hpos : ∀ k, 0 < u k := fun k => lt_of_lt_of_le hu0 (hmono (Nat.zero_le k))
  have hle1 : ∀ k ≤ K, u k ≤ 1 := fun k hk => huK ▸ hmono hk
  have hu01 : u 0 ≤ 1 := hle1 0 (Nat.zero_le K)
  have hsub : ∀ a b : ℝ, a ∈ Icc (1 : ℝ) 2 → b ∈ Icc (1 : ℝ) 2 → IntervalIntegrable f volume a b := fun a b ha hb =>
    hfi.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact Set.uIcc_subset_Icc ha hb)
  have hk : ∀ k ∈ Finset.range K, ∫ t in shellSet u k, f t
      = -∫ t in (2 - u k)..(2 - u (k + 1)), f t := fun k hk => by
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    unfold shellSet
    rw [intervalIntegral.integral_symm, neg_neg,
      intervalIntegral.integral_of_le (by linarith [hmono (Nat.le_succ k)])]
  rw [Finset.sum_congr rfl hk, Finset.sum_neg_distrib]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
    (a := fun k => 2 - u k) (n := K) fun k hk => hsub _ _
      ⟨by linarith [hle1 k hk.le], by linarith [hpos k]⟩ ⟨by linarith [hle1 (k + 1) hk], by linarith [hpos (k + 1)]⟩
  rw [hadj, huK, intervalIntegral.integral_symm, neg_neg]
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hsub 1 (2 - u 0) ⟨le_rfl, by norm_num⟩
    ⟨by linarith, by linarith⟩) (hsub (2 - u 0) 2 ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩)
  have h3 : 0 ≤ ∫ t in (2 - u 0)..2, f t :=
    intervalIntegral.integral_nonneg (by linarith) fun t ht => hf0 t ⟨by linarith [ht.1], ht.2⟩
  rw [show (2 : ℝ) - 1 = 1 by norm_num]
  linarith

theorem integrableOn_theta2Int_shell {u : ℕ → ℝ} {k : ℕ} (hu0 : 0 < u k) (hu1 : u (k + 1) ≤ 1) :
    IntegrableOn theta2Int (shellSet u k) := by
  have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)).1
    Cvs.L2a.CornerSuprema.intervalIntegrable_theta2Int
  exact h.mono_set fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- On a shell with `δ_k ≤ u_k/4`: the collar integrand is at most `4θ₂` and the chirp integrand at most `16θ₂`. -/
theorem shell_integrands_le {D t uk : ℝ} (hD0 : 0 ≤ D) (hDu : D ≤ uk / 4) (ht1 : 1 ≤ t) (htu : t ≤ 2 - uk)
    (hu0 : 0 < uk) :
    (1 - wF t) ^ 2 * ((1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2)) ^ 2 ≤ 4 * theta2Int t
      ∧ (1 - wF t) ^ 2 / (1 - D - t / 2) ^ 2 ≤ 16 * theta2Int t := by
  have hv : 0 < 2 - t := by linarith
  have ha : (2 - t) / 4 ≤ 1 - D - t / 2 := by linarith
  have ha0 : 0 < 1 - D - t / 2 := by linarith
  have hq : 0 < 1 - t ^ 2 / 2 ^ 2 := by nlinarith
  have hb : 0 < 1 - D + t / 2 := by linarith
  have hw := sq_nonneg (1 - wF t)
  unfold theta2Int
  constructor
  · have hden : (1 - D) ^ 2 - t ^ 2 / 2 ^ 2 = (1 - D - t / 2) * (1 - D + t / 2) := by ring
    have hr : (1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2) ≤ 2 / (1 - t ^ 2 / 2 ^ 2) := by
      rw [hden, div_le_div_iff₀ (by positivity) hq]
      have e1 : 1 - t ^ 2 / 2 ^ 2 = (1 - t / 2) * (1 + t / 2) := by ring
      rw [e1]
      have h1 : 1 - t / 2 ≤ 2 * (1 - D - t / 2) := by linarith
      have h2 : (1 - D) * (1 + t / 2) ≤ 1 - D + t / 2 := by nlinarith
      have h3 : 0 ≤ 1 - t / 2 := by linarith
      have h4 : 0 ≤ (1 - D) * (1 + t / 2) := by nlinarith
      nlinarith [mul_le_mul h1 h2 h4 (by linarith)]
    have hr0 : 0 ≤ (1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2) := by
      rw [hden]; apply div_nonneg (by linarith); positivity
    calc (1 - wF t) ^ 2 * ((1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2)) ^ 2
        ≤ (1 - wF t) ^ 2 * (2 / (1 - t ^ 2 / 2 ^ 2)) ^ 2 := by gcongr
      _ = 4 * ((1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2) := by field_simp; ring
  · rw [div_le_iff₀ (by positivity)]
    have h1 : 1 - t ^ 2 / 2 ^ 2 ≤ 4 * (1 - D - t / 2) := by nlinarith
    have h2 : (1 - t ^ 2 / 2 ^ 2) ^ 2 ≤ 16 * (1 - D - t / 2) ^ 2 := by
      have := pow_le_pow_left₀ hq.le h1 2; nlinarith
    have e : 16 * ((1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2) * (1 - D - t / 2) ^ 2
        = (1 - wF t) ^ 2 * (16 * (1 - D - t / 2) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2) := by field_simp
    rw [e]
    have : 1 ≤ 16 * (1 - D - t / 2) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith

/-- `collSh_k ≤ ∫_{shell} 4θ₂` and `psiSh_k ≤ ∫_{shell} 16θ₂` for `0 ≤ δ`, `0 < u_k`, `u_{k+1} ≤ 1`. -/
theorem collSh_psiSh_le {δ : ℝ} {u : ℕ → ℝ} {k : ℕ} (hδ : 0 ≤ δ) (hu0 : 0 < u k) (hu1 : u (k + 1) ≤ 1) :
    collSh δ u k ≤ ∫ t in shellSet u k, 4 * theta2Int t ∧ psiSh δ u k ≤ ∫ t in shellSet u k, 16 * theta2Int t := by
  have hD0 : 0 ≤ dK δ u k := le_min hδ (by positivity)
  have hDu : dK δ u k ≤ u k / 4 := min_le_right _ _
  have hI := integrableOn_theta2Int_shell hu0 hu1
  have hpt : ∀ t ∈ shellSet u k, 1 ≤ t ∧ t ≤ 2 - u k := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  constructor
  · refine integral_mono_of_nonneg (ae_of_all _ fun t => by positivity) (hI.const_mul 4) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
    obtain ⟨h1, h2⟩ := hpt t ht
    exact (shell_integrands_le hD0 hDu h1 h2 hu0).1
  · refine integral_mono_of_nonneg (ae_of_all _ fun t => by positivity) (hI.const_mul 16) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
    obtain ⟨h1, h2⟩ := hpt t ht
    exact (shell_integrands_le hD0 hDu h1 h2 hu0).2

/-- `Σ_k ∫_{shell_k} θ₂ ≤ Θ₂² ≤ 4.06344`. -/
theorem shells_theta_le {u : ℕ → ℝ} {K : ℕ} (hu0 : 0 < u 0) (huK : u K = 1) (hmono : Monotone u) :
    ∑ k ∈ Finset.range K, ∫ t in shellSet u k, theta2Int t ≤ 406344 / 100000 :=
  (shells_sum_le (fun t _ => Cvs.L2a.CornerSuprema.theta2Int_nonneg t)
    Cvs.L2a.CornerSuprema.intervalIntegrable_theta2Int hu0 huK hmono).trans
    (Cvs.L2a.CornerSuprema.theta2_sq_le.trans Cvs.L2a.CornerSuprema.thetaAB_le)

end shells

/-! ### The top remainder `remT` below `X_t = 68` -/

section top

open Cvs.L2a.LocalisedBottomCorners (eSh)
open Cvs.L2a.TopCornerSum (shellSet dK collSh psiSh collC chirpC Bloc Bloc2 tC)
open Cvs.L2a.CornerSuprema (theta2Int Theta)

theorem harmonic_le_of_le {m n : ℕ} (h : m ≤ n) : (harmonic m : ℝ) ≤ harmonic n := by
  have : harmonic m ≤ harmonic n := by
    unfold harmonic
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => by positivity
  exact_mod_cast this

/-- `Σ_{3 ≤ m < M} 1/(m − 2) = H_{M−3}`. -/
theorem sum_inv_sub_two (M : ℕ) : ∑ m ∈ Finset.Ico 3 M, 1 / ((m : ℝ) - 2) = harmonic (M - 3) := by
  rw [Finset.sum_Ico_eq_sum_range, harmonic]; push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div]; ring_nf

/-- `ΔY(M) ≥ 1/(2M²)` for `M ≥ 2`. -/
theorem dY_ge {M : ℝ} (hM : 2 ≤ M) : 1 / (2 * M ^ 2) ≤ Cvs.L2a.TopCornerConstants.dY M := by
  have hpos : 0 < M ^ 2 - 1 := by nlinarith
  set q := √(M ^ 2 - 1) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hpos
  have hq2 : q ^ 2 = M ^ 2 - 1 := Real.sq_sqrt hpos.le
  have hqM : q ≤ M - 1 / (2 * M) := by
    rw [Real.sqrt_le_left (by
      have : 1 / (2 * M) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith)]
    have : (M - 1 / (2 * M)) ^ 2 = M ^ 2 - 1 + 1 / (4 * M ^ 2) := by field_simp; ring
    rw [this]
    have : 0 ≤ 1 / (4 * M ^ 2) := by positivity
    linarith
  unfold Cvs.L2a.TopCornerConstants.dY Ymax
  rw [← hq, le_sub_iff_add_le, le_div_iff₀ hq0]
  have hM0 : 0 < M := by linarith
  calc (1 / (2 * M ^ 2) + 1) * q ≤ (1 / (2 * M ^ 2) + 1) * (M - 1 / (2 * M)) := by gcongr
    _ = M - 1 / (4 * M ^ 3) := by field_simp; ring
    _ ≤ M := by have : 0 ≤ 1 / (4 * M ^ 3) := by positivity
                linarith

/-- **The `m = 2` collar**: `C₂ = 2κ_S Σ_k δ_k collSh_k ≤ 0.0357²` at `δ = 1/p²`. -/
theorem collC_two_le {p : ℝ} (hp : 100 ≤ p) {K : ℕ} (hK : eSh (4 / 3 * (1 / p ^ 2)) K = 1) :
    collC (1 / p ^ 2) (eSh (4 / 3 * (1 / p ^ 2))) K 2 ≤ (357 / 10000) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  set s := 4 / 3 * (1 / p ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have hterm : ∀ k ∈ Finset.range K, dK (1 / p ^ 2) (eSh s) k * collSh (1 / p ^ 2) (eSh s) k
      ≤ 1 / p ^ 2 * (4 * ∫ t in shellSet (eSh s) k, theta2Int t) := fun k _ => by
    have hpos := eSh_pos hs0 k
    have h1 := eSh_le_one s (k + 1)
    obtain ⟨hc, -⟩ := collSh_psiSh_le (δ := 1 / p ^ 2) (by positivity) hpos h1
    rw [integral_const_mul] at hc
    have hD0 : 0 ≤ dK (1 / p ^ 2) (eSh s) k := le_min (by positivity) (by positivity)
    have hDδ : dK (1 / p ^ 2) (eSh s) k ≤ 1 / p ^ 2 := min_le_left _ _
    have hC0 : 0 ≤ collSh (1 / p ^ 2) (eSh s) k := setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
    calc dK (1 / p ^ 2) (eSh s) k * collSh (1 / p ^ 2) (eSh s) k
        ≤ 1 / p ^ 2 * collSh (1 / p ^ 2) (eSh s) k := by gcongr
      _ ≤ 1 / p ^ 2 * (4 * ∫ t in shellSet (eSh s) k, theta2Int t) := by gcongr
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hth := shells_theta_le (u := eSh s) (K := K) (eSh_pos hs0 0) hK (eSh_mono hs0.le)
  unfold collC
  rw [if_pos rfl]
  calc 2 * (181 / 462) * ∑ k ∈ Finset.range K, dK (1 / p ^ 2) (eSh s) k * collSh (1 / p ^ 2) (eSh s) k
      ≤ 2 * (181 / 462) * (1 / p ^ 2 * (4 * (406344 / 100000))) := by gcongr; exact hsum.trans (by gcongr)
    _ ≤ 2 * (181 / 462) * (1 / 10 ^ 4 * (4 * (406344 / 100000))) := by gcongr
    _ ≤ (357 / 10000) ^ 2 := by norm_num

/-- **The collars `m ≥ 3`** below `X_t`: `Σ_{3 ≤ m < M} min(√C_m, C_m/(2√ΔY Θ_m))/m ≤ 0.0116` for `M ≤ 67`. -/
theorem collar_three_le {p : ℝ} (hp : 100 ≤ p) {K M : ℕ} (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    ∑ m ∈ Finset.Ico 3 M, min (√(collC (1 / p ^ 2) (eSh (4 / 3 * (1 / p ^ 2))) K m))
        (collC (1 / p ^ 2) (eSh (4 / 3 * (1 / p ^ 2))) K m
          / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m ≤ 116 / 10000 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  set δ := 1 / p ^ 2 with hδ
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMr : (M : ℝ) ≤ 67 := by exact_mod_cast hM
  have hdY := dY_ge (M := (M : ℝ)) (by linarith)
  have hdY0 : 0 < Cvs.L2a.TopCornerConstants.dY M := lt_of_lt_of_le (by positivity) hdY
  have hinv : (√(Cvs.L2a.TopCornerConstants.dY M))⁻¹ ≤ 95 := by
    refine Cvs.L2a.LocalisedConstants.inv_sqrt_le (by norm_num) (le_trans ?_ hdY)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  set A := (181 / 462) * δ * (1 + 24 * δ / 5) ^ 2 * (√(Cvs.L2a.TopCornerConstants.dY M))⁻¹ with hA
  have hterm : ∀ m ∈ Finset.Ico 3 M, min (√(collC δ (eSh (4 / 3 * δ)) K m))
      (collC δ (eSh (4 / 3 * δ)) K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m
        ≤ A * (Theta m / m) := fun m hm => by
    have hm3 : 3 ≤ m := (Finset.mem_Ico.1 hm).1
    have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hΘ := Cvs.L2a.TopCornerSum.Theta_ge (m := (m : ℝ)) (by linarith)
    have hΘ0 : 0 < Theta m := lt_of_lt_of_le (by positivity) hΘ
    have hTD := Cvs.L2a.TopCornerSum.Theta_delta_le hm3r hd0.le (by linarith)
    have hTD0 : 0 ≤ Cvs.L2a.TopCornerSum.ThetaD δ m := Real.sqrt_nonneg _
    have hC : collC δ (eSh (4 / 3 * δ)) K m = 2 * (181 / 462) * δ * Cvs.L2a.TopCornerSum.ThetaD δ m ^ 2 := by
      unfold collC; rw [if_neg (by omega)]
    have hs := Real.sqrt_pos.2 hdY0
    refine (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)).trans ?_
    rw [hC]
    have h2 : Cvs.L2a.TopCornerSum.ThetaD δ m ^ 2 ≤ ((1 + 24 * δ / 5) * Theta m) ^ 2 :=
      pow_le_pow_left₀ hTD0 hTD 2
    calc 2 * (181 / 462) * δ * Cvs.L2a.TopCornerSum.ThetaD δ m ^ 2
          / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m)) / m
        ≤ 2 * (181 / 462) * δ * ((1 + 24 * δ / 5) * Theta m) ^ 2
          / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m)) / m := by gcongr
      _ = A * (Theta m / m) := by rw [hA]; field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hN := Cvs.L2a.CornerSuprema.sum_div_le_Nbar Theta (fun m hm => Cvs.L2a.CornerSuprema.Theta_le (by linarith))
    M hM3
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < M)] at hN
  unfold Cvs.L2a.CornerSuprema.Nbar at hN
  have h65 := harmonic_le_of_le (show M - 3 ≤ 65 by omega)
  have h69 := harmonic_le_of_le (show M + 1 ≤ 69 by omega)
  obtain ⟨H65, H69⟩ := Cvs.L2a.LocalisedConstants.harmonic_65_69
  have h11 : √11 ≤ 331663 / 100000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hS : ∑ m ∈ Finset.Ico 3 M, Theta m / m ≤ 331663 / 100000 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12) := by
    have hH : (harmonic (M - 3) : ℝ) + harmonic (M + 1) - 25 / 12 ≤ 47593 / 10000 + 48186 / 10000 - 25 / 12 := by
      linarith
    have hH0 : 0 ≤ 47593 / 10000 + 48186 / 10000 - 25 / 12 := by norm_num
    have : √11 / 8 * ((harmonic (M - 3) : ℝ) + harmonic (M + 1) - 25 / 12)
        ≤ 331663 / 100000 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12) := by
      calc √11 / 8 * ((harmonic (M - 3) : ℝ) + harmonic (M + 1) - 25 / 12)
          ≤ √11 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12) := by gcongr
        _ ≤ _ := by gcongr
    rw [show (2 : ℕ) + 1 = 3 from rfl] at hN
    simp only [Nat.cast_ofNat] at hN
    linarith
  have hS0 : 0 ≤ ∑ m ∈ Finset.Ico 3 M, Theta m / m := Finset.sum_nonneg fun m hm => by
    have := Cvs.L2a.TopCornerSum.Theta_ge (m := (m : ℝ)) (by
      have : (3 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
      linarith)
    have : 0 < Theta m := lt_of_lt_of_le (by positivity) this
    positivity
  have hA' : A ≤ (181 / 462) * (1 / 10 ^ 4) * (1 + 24 * (1 / 10 ^ 4) / 5) ^ 2 * 95 := by
    rw [hA]; gcongr
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  calc A * ∑ m ∈ Finset.Ico 3 M, Theta m / m
      ≤ (181 / 462) * (1 / 10 ^ 4) * (1 + 24 * (1 / 10 ^ 4) / 5) ^ 2 * 95
        * (331663 / 100000 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12)) := by gcongr
    _ ≤ 116 / 10000 := by norm_num

/-- **The `m = 2` chirp** below `X_t`: `(2κ/2)√B₂ ≤ 7.9·10⁻⁴` for `3 ≤ M ≤ 67`. -/
theorem chirp_two_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {K M : ℕ}
    (hK : eSh (4 / 3 * (1 / p ^ 2)) K = 1) (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    2 * √(2 * c / π) / ((2 : ℕ) : ℝ)
        * √(chirpC c J (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) (eSh (4 / 3 * (1 / p ^ 2))) K M 2)
      ≤ 79 / 10 ^ 5 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMr : (M : ℝ) ≤ 67 := by exact_mod_cast hM
  set δ := 1 / p ^ 2 with hδ
  set s := 4 / 3 * δ with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s * 4 ≤ 1 := by rw [hs]; linarith
  have he0 : eSh s 0 = s := eSh_zero (by linarith)
  have he2 : eSh s 2 = s * 4 := by unfold eSh; norm_num; linarith
  obtain ⟨hπ1, hπ2⟩ := pi_bounds
  set T₂ : ℝ := (11 / 10 ^ 4) ^ 2 * (1 / 3) ^ 4 + (21 / 10 ^ 6) ^ 2 * (1 / 3) ^ 2 with hT₂
  set A : ℕ → ℝ := fun k => 15 / 10 ^ 7 * (16 * π ^ 4 * ((eSh s (k + 1) ^ 3 - eSh s k ^ 3) / 3)) with hA
  set B : ℕ → ℝ := fun k => T₂ * (16 * ∫ t in shellSet (eSh s) k, theta2Int t) with hB
  have hcube : ∀ k, 0 ≤ eSh s (k + 1) ^ 3 - eSh s k ^ 3 := fun k => by
    have := eSh_mono hs0.le (Nat.le_succ k)
    have := (eSh_pos hs0 k).le
    nlinarith [pow_le_pow_left₀ this (eSh_mono hs0.le (Nat.le_succ k)) 3]
  have hA0 : ∀ k, 0 ≤ A k := fun k => by simp only [hA]; have := hcube k; positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    simp only [hB]
    have : 0 ≤ ∫ t in shellSet (eSh s) k, theta2Int t :=
      setIntegral_nonneg measurableSet_Ioc fun t _ => Cvs.L2a.CornerSuprema.theta2Int_nonneg t
    positivity
  have hM2 : (2 : ℝ) ≤ M := by linarith
  have hf : ∀ k < K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k
      ≤ if k < 2 then A k else B k := fun k _ => by
    have hek : s ≤ eSh s k := by have := eSh_mono hs0.le (Nat.zero_le k); rwa [he0] at this
    have hpos := eSh_pos hs0 k
    have h1 := eSh_le_one s (k + 1)
    have hr0 : 0 < eSh s k / 4 := by positivity
    have hdk0 : 0 ≤ dK δ (eSh s) k := le_min hd0.le hr0.le
    have hT0 := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := M) (d := δ) (δ := dK δ (eSh s) k)
      (r := eSh s k / 4) (J := J) hc0 hd0.le (by linarith) hdk0 hJ0 hr0
    have hP0 : 0 ≤ psiSh δ (eSh s) k := setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
    have htC : tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J
        = Cvs.L2a.LocalisedBottomCorners.tT c M δ (dK δ (eSh s) k) (eSh s k / 4) J := rfl
    rw [htC]
    have hs3 : 1 / 3 / p ^ 2 = s / 4 := by rw [hs, hδ]; ring
    have hs43 : 4 / 3 / p ^ 2 = s := by rw [hs, hδ]; ring
    split_ifs with hk
    · have hT := tT_regI hp hc hM2 (δ := dK δ (eSh s) k) (r := eSh s k / 4)
        (le_min (by rw [hδ]; gcongr; norm_num) (by rw [hs3]; linarith)) (min_le_left _ _) (by rw [hs3]; linarith)
        hJ0 hJ
      have hP := (Cvs.L2a.TopCornerSum.shell_le (δ := δ) (u := eSh s) (k := k) hd0 (by linarith) hpos
        (eSh_mono hs0.le (Nat.le_succ k)) h1).2
      simp only [hA]
      calc Cvs.L2a.LocalisedBottomCorners.tT c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k
          ≤ 15 / 10 ^ 7 * psiSh δ (eSh s) k := by gcongr
        _ ≤ _ := by gcongr
    · have hek2 : s * 4 ≤ eSh s k := by
        have := eSh_mono hs0.le (by omega : 2 ≤ k); rwa [he2] at this
      have hdk : dK δ (eSh s) k = δ := min_eq_left (by rw [hs] at hek2; linarith)
      rw [hdk]
      have hT := tT_regII hp hc hM2 (by linarith) (r := eSh s k / 4) (by rw [hs43]; linarith) hJ0 hJ
      have hu3 : 1 / (M : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hM3r
      have hT' : Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (eSh s k / 4) J ≤ T₂ := by
        refine hT.trans ?_
        rw [hT₂]; gcongr
      have hP := (collSh_psiSh_le (δ := δ) hd0.le hpos h1).2
      rw [integral_const_mul] at hP
      have hT0' := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := M) (d := δ) (δ := δ)
        (r := eSh s k / 4) (J := J) hc0 hd0.le (by linarith) hd0.le hJ0 hr0
      have hP0' : 0 ≤ psiSh δ (eSh s) k := setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
      simp only [hB]
      calc Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (eSh s k / 4) J * psiSh δ (eSh s) k
          ≤ T₂ * psiSh δ (eSh s) k := by gcongr
        _ ≤ _ := by gcongr
  have hsum := sum_split_two hA0 hB0 hf
  have hAs : A 0 + A 1 ≤ 15 / 10 ^ 7 * (16 * π ^ 4 * ((s * 4) ^ 3 / 3)) := by
    have e : A 0 + A 1 = 15 / 10 ^ 7 * (16 * π ^ 4 * ((eSh s 2 ^ 3 - eSh s 0 ^ 3) / 3)) := by
      simp only [hA]; ring
    rw [e, he2, he0]
    have h0 : 0 ≤ s ^ 3 := by positivity
    gcongr
    linarith
  have hBs : ∑ k ∈ Finset.range K, B k ≤ T₂ * (16 * (406344 / 100000)) := by
    simp only [hB]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := shells_theta_le (u := eSh s) (K := K) (eSh_pos hs0 0) hK (eSh_mono hs0.le)
    gcongr
  have hstrip : 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c ≤ 3 / 10 ^ 11 := by
    have hsI := Cvs.L2a.TopCornerSum.stripI_le hs0 (by linarith)
    have hJc : J / c ≤ 2501 / 10000 := by
      rw [div_le_iff₀ hc0]; rw [hc] at hJ ⊢
      have : (10 : ℝ) ^ 16 ≤ p ^ 8 := by
        calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
          _ ≤ p ^ 8 := by gcongr
      nlinarith
    have hM8 : 8 ≤ (M : ℝ) ^ 2 - 1 := by nlinarith
    have hsle : s ≤ 4 / 3 * (1 / 10 ^ 4) := by rw [hs]; linarith
    have e : 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c
        = 6 * (J / c) / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s := by ring
    rw [e]
    have hI0 : 0 ≤ Cvs.L2a.TopCornerSum.stripI s := setIntegral_nonneg measurableSet_Ioo fun t _ => by positivity
    calc 6 * (J / c) / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s
        ≤ 6 * (2501 / 10000) / 8 * (16 * π ^ 4 / 9 * (s ^ 3 / 3)) := by
          gcongr
      _ ≤ 6 * (2501 / 10000) / 8 * (16 * (31416 / 10000) ^ 4 / 9 * ((4 / 3 * (1 / 10 ^ 4)) ^ 3 / 3)) := by gcongr
      _ ≤ 3 / 10 ^ 11 := by norm_num
  unfold chirpC
  rw [if_pos rfl]
  rw [show 2 * √(2 * c / π) / ((2 : ℕ) : ℝ) = √(2 * c / π) by push_cast; ring,
    ← Real.sqrt_mul (by positivity)]
  refine sqrt_le_of_le_sq (by norm_num) ?_
  have e : 2 * c / π * Bloc2 c M δ δ J s (eSh s) K
      = 2 / π * (∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k)
        + 2 / π * (6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c) := by
    unfold Bloc2
    rw [← Finset.sum_div]
    field_simp
  rw [e]
  have h2π : 2 / π ≤ 2 / (31415 / 10000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ1
  have hπ4 : π ^ 4 ≤ (31416 / 10000) ^ 4 := by gcongr
  have hs4' : (s * 4) ^ 3 ≤ (4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 := by
    gcongr; rw [hs]; linarith
  have hA' : 15 / 10 ^ 7 * (16 * π ^ 4 * ((s * 4) ^ 3 / 3))
      ≤ 15 / 10 ^ 7 * (16 * (31416 / 10000) ^ 4 * ((4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 / 3)) := by gcongr
  have htot : ∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k
      ≤ 975 / 10 ^ 9 := by
    have : 15 / 10 ^ 7 * (16 * (31416 / 10000) ^ 4 * ((4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 / 3))
        + T₂ * (16 * (406344 / 100000)) ≤ 975 / 10 ^ 9 := by rw [hT₂]; norm_num
    linarith
  have hsum0 : 0 ≤ 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c := by
    have : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
    have hI0 : 0 ≤ Cvs.L2a.TopCornerSum.stripI s := setIntegral_nonneg measurableSet_Ioo fun t _ => by positivity
    positivity
  calc 2 / π * (∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k)
        + 2 / π * (6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c)
      = 2 / π * ((∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k)
        + 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c) := by ring
    _ ≤ 2 / π * (975 / 10 ^ 9 + 3 / 10 ^ 11) :=
        mul_le_mul_of_nonneg_left (add_le_add htot hstrip) (by positivity)
    _ ≤ 2 / (31415 / 10000) * (975 / 10 ^ 9 + 3 / 10 ^ 11) := mul_le_mul_of_nonneg_right h2π (by norm_num)
    _ ≤ (79 / 10 ^ 5) ^ 2 := by norm_num

/-- **The chirps `m ≥ 3`** below `X_t`: `Σ_{3 ≤ m < M}(2κ/m)√B_m ≤ 7.82·10⁻⁴` for `M ≤ 67`. -/
theorem chirp_three_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {K M : ℕ}
    (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    ∑ m ∈ Finset.Ico 3 M, 2 * √(2 * c / π) / m
        * √(chirpC c J (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) (eSh (4 / 3 * (1 / p ^ 2))) K M m)
      ≤ 782 / 10 ^ 6 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMr : (M : ℝ) ≤ 67 := by exact_mod_cast hM
  set δ := 1 / p ^ 2 with hδ
  obtain ⟨hπ1, hπ2⟩ := pi_bounds
  set T₂ : ℝ := (11 / 10 ^ 4) ^ 2 * (1 / 3) ^ 4 + (21 / 10 ^ 6) ^ 2 * (1 / 3) ^ 2 with hT₂
  have hu3 : 1 / (M : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hM3r
  have hterm : ∀ m ∈ Finset.Ico 3 M, 2 * √(2 * c / π) / m
      * √(chirpC c J δ δ (4 / 3 * δ) (eSh (4 / 3 * δ)) K M m)
      ≤ 2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4)) * (1 / ((m : ℝ) - 2)) := fun m hm => by
    have hm3 : 3 ≤ m := (Finset.mem_Ico.1 hm).1
    have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hm0 : (0 : ℝ) < m := by linarith
    unfold chirpC
    rw [if_neg (by omega)]
    have hr0 : 0 < 1 - δ - 2 / (m : ℝ) := by
      have : 2 / (m : ℝ) ≤ 2 / 3 := by gcongr
      linarith
    have hT := tT_regII (x₀ := (M : ℝ)) hp hc (by linarith) (by linarith) (r := 1 - δ - 2 / (m : ℝ)) (by
      have : 2 / (m : ℝ) ≤ 2 / 3 := by gcongr
      have : 4 / 3 / p ^ 2 = 4 / 3 * δ := by rw [hδ]; ring
      linarith) hJ0 hJ
    have hT' : Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J ≤ T₂ := by
      refine hT.trans ?_; rw [hT₂]; gcongr
    have hT0 := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := M) (d := δ) (δ := δ) (r := 1 - δ - 2 / (m : ℝ))
      (J := J) hc0 hd0.le (by linarith) hd0.le hJ0 hr0
    have hP := Cvs.L2a.TopCornerSum.PsiD_le hm3r (δ := δ) (by linarith)
    have hP0 : 0 ≤ Cvs.L2a.TopCornerSum.PsiD δ m := by
      unfold Cvs.L2a.TopCornerSum.PsiD
      exact intervalIntegral.integral_nonneg (by norm_num) fun t _ => by positivity
    have htC : tC c M δ δ (1 - δ - 2 / (m : ℝ)) J = Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J := rfl
    unfold Bloc
    rw [htC]
    rw [show 2 * √(2 * c / π) / (m : ℝ) * √(Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
        * Cvs.L2a.TopCornerSum.PsiD δ m / c)
        = 2 / m * (√(2 * c / π) * √(Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
          * Cvs.L2a.TopCornerSum.PsiD δ m / c)) by ring, ← Real.sqrt_mul (by positivity)]
    have hin : 2 * c / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
        * Cvs.L2a.TopCornerSum.PsiD δ m / c) ≤ (82 / 10 ^ 6 / (1 - δ - 2 / (m : ℝ))) ^ 2 := by
      have e : 2 * c / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
          * Cvs.L2a.TopCornerSum.PsiD δ m / c)
          = 2 / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J * Cvs.L2a.TopCornerSum.PsiD δ m) := by
        field_simp
      rw [e]
      have h2π : 2 / π ≤ 2 / (31415 / 10000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ1
      calc 2 / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J * Cvs.L2a.TopCornerSum.PsiD δ m)
          ≤ 2 / (31415 / 10000) * (T₂ * (11 / 16 / (1 - δ - 2 / (m : ℝ)) ^ 2)) := by gcongr
        _ = (2 / (31415 / 10000) * T₂ * (11 / 16)) / (1 - δ - 2 / (m : ℝ)) ^ 2 := by ring
        _ ≤ (82 / 10 ^ 6) ^ 2 / (1 - δ - 2 / (m : ℝ)) ^ 2 := by
            gcongr; rw [hT₂]; norm_num
        _ = (82 / 10 ^ 6 / (1 - δ - 2 / (m : ℝ))) ^ 2 := (div_pow _ _ _).symm
    have hsq := sqrt_le_of_le_sq (by positivity) hin
    have hden : (1 - 3 * (1 / 10 ^ 4)) * ((m : ℝ) - 2) ≤ m * (1 - δ - 2 / (m : ℝ)) := by
      have hq : (m : ℝ) * (2 / m) = 2 := by field_simp
      nlinarith [hq]
    calc 2 / (m : ℝ) * √(2 * c / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
          * Cvs.L2a.TopCornerSum.PsiD δ m / c))
        ≤ 2 / m * (82 / 10 ^ 6 / (1 - δ - 2 / (m : ℝ))) := by gcongr
      _ = 2 * (82 / 10 ^ 6) / (m * (1 - δ - 2 / (m : ℝ))) := div_mul_div_comm _ _ _ _
      _ ≤ 2 * (82 / 10 ^ 6) / ((1 - 3 * (1 / 10 ^ 4)) * ((m : ℝ) - 2)) := by
          gcongr
          have : 0 < (m : ℝ) - 2 := by linarith
          positivity
      _ = 2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4)) * (1 / ((m : ℝ) - 2)) := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, sum_inv_sub_two]
  have h65 := harmonic_le_of_le (show M - 3 ≤ 65 by omega)
  obtain ⟨H65, -⟩ := Cvs.L2a.LocalisedConstants.harmonic_65_69
  calc 2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4)) * (harmonic (M - 3) : ℝ)
      ≤ 2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4)) * (47593 / 10000) := by gcongr; linarith
    _ ≤ 782 / 10 ^ 6 := by norm_num

/-- `KcoBar ≤ 10⁻¹⁰` for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1`. -/
theorem KcoBar_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.TopCornerSum.KcoBar c J ≤ 1 / 10 ^ 10 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  obtain ⟨hk0, hk1⟩ := Cvs.L2a.LocalisedConstants.kappaI_mem (J := J) (c := c) (by linarith) hJ0 hJ
  have hkap : Cvs.L2a.TopCornerSum.kapI c J = Cvs.L2a.LocalisedConstants.kappaI J c := rfl
  have hs1 : √(Cvs.L2a.TopCornerSum.kapI c J) ≤ 1 := by
    rw [hkap, Real.sqrt_le_one]; exact hk1
  have h8 : 28 / 10 ≤ √8 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hπ : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  unfold Cvs.L2a.TopCornerSum.KcoBar
  calc 29 * π ^ 2 / (3 * √8) * √(Cvs.L2a.TopCornerSum.kapI c J) / c ≤ 29 * 10 / (3 * (28 / 10)) * 1 / 10 ^ 16 := by
        gcongr
    _ ≤ 1 / 10 ^ 10 := by norm_num

/-- **`remT ≤ 15/1000`** for `3 ≤ M ≤ 67` at `δ = d = 1/p²`, `s = (4/3)/p²`, dyadic shells. -/
theorem remT_le {c J p : ℝ} (hp : 100 ≤ p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {K M : ℕ}
    (hK : eSh (4 / 3 * (1 / p ^ 2)) K = 1) (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    Cvs.L2a.TopCornerSum.remT c J (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) (eSh (4 / 3 * (1 / p ^ 2))) K M
      ≤ 15 / 1000 := by
  have hp0 : 0 < p := by linarith
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc16 : 10 ^ 16 ≤ c := by rw [hc]; exact hp8
  have hc0 : 0 < c := by linarith
  have hcorr := Cvs.L2a.TopCornerSum.sum_corrC_le hc0 hJ0 hM3
  have hKco := KcoBar_le hc16 hJ0 hJ
  set δ := 1 / p ^ 2 with hδ
  set s := 4 / 3 * δ with hs
  have hcoll : ∑ m ∈ Finset.Ico 2 M, min (√(collC δ (eSh s) K m))
      (collC δ (eSh s) K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m
      ≤ 357 / 10000 / 2 + 116 / 10000 := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < M), show (2 : ℕ) + 1 = 3 from rfl]
    have h3 := collar_three_le (K := K) hp hM3 hM
    have h2 : min (√(collC δ (eSh s) K 2))
        (collC δ (eSh s) K 2 / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta ((2 : ℕ) : ℝ)))) / ((2 : ℕ) : ℝ)
        ≤ 357 / 10000 / 2 := by
      push_cast
      refine div_le_div_of_nonneg_right ((min_le_left _ _).trans ?_) (by norm_num)
      exact sqrt_le_of_le_sq (by norm_num) (collC_two_le hp hK)
    linarith
  have hchirp : ∑ m ∈ Finset.Ico 2 M, 2 * √(2 * c / π) / m * √(chirpC c J δ δ s (eSh s) K M m)
      ≤ 79 / 10 ^ 5 + 782 / 10 ^ 6 := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < M), show (2 : ℕ) + 1 = 3 from rfl]
    have h2 := chirp_two_le hp hc hJ0 hJ hK hM3 hM
    have h3 := chirp_three_le (K := K) hp hc hJ0 hJ hM3 hM
    linarith
  unfold Cvs.L2a.TopCornerSum.remT
  rw [Cvs.L2a.TopCornerSum.Icc_eq_Ico (by omega)] at hcorr ⊢
  have h2 : √2 ≤ 141422 / 100000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hπ := pi_bounds.1
  have hsπ : √2 / π ≤ 141422 / 100000 / (31415 / 10000) := div_le_div₀ (by norm_num) h2 (by norm_num) hπ
  have hcoll0 : (0 : ℝ) ≤ 357 / 10000 / 2 + 116 / 10000 := by norm_num
  have : √2 / π * ∑ m ∈ Finset.Ico 2 M, min (√(collC δ (eSh s) K m))
      (collC δ (eSh s) K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m
      ≤ 141422 / 100000 / (31415 / 10000) * (357 / 10000 / 2 + 116 / 10000) := by
    calc _ ≤ √2 / π * (357 / 10000 / 2 + 116 / 10000) :=
          mul_le_mul_of_nonneg_left hcoll (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsπ hcoll0
  norm_num at this hchirp hKco ⊢
  linarith

/-- `sup_{3 ≤ M < X} f(M)⁺ ≤ B` from `f ≤ B` on `[3, X)` and `B ≥ 0`. -/
theorem supBelow_le {f : ℕ → ℝ} {X : ℕ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ M ∈ Finset.Ico 3 X, f M ≤ B) :
    Cvs.L2a.TopCornerSum.supBelow f X ≤ B := by
  unfold Cvs.L2a.TopCornerSum.supBelow
  have : (Finset.Ico 3 X).sup (fun M => (f M).toNNReal) ≤ B.toNNReal :=
    Finset.sup_le fun M hM => Real.toNNReal_le_toNNReal (h M hM)
  calc (((Finset.Ico 3 X).sup fun M => (f M).toNNReal : NNReal) : ℝ) ≤ (B.toNNReal : ℝ) := by exact_mod_cast this
    _ = B := Real.coe_toNNReal B hB

end top

/-! ### `resLoc ≤ 7/100` -/

/-- **`ρ_t ≤ 15/1000`** at `S*`, `X_t = 68`, for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1`. -/
theorem rhoTL_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.FrameFloorIntegerM.rhoTL c J ≤ 15 / 1000 := by
  obtain ⟨p, hp, hδ, hcp⟩ := scale_p hc
  have hs : Cvs.L2a.TopCornerSum.sS c = 4 / 3 * (1 / p ^ 2) := by unfold Cvs.L2a.TopCornerSum.sS; rw [hδ]
  have hu : Cvs.L2a.TopCornerSum.uS c = Cvs.L2a.LocalisedBottomCorners.eSh (Cvs.L2a.TopCornerSum.sS c) := rfl
  have hK : Cvs.L2a.LocalisedBottomCorners.eSh (4 / 3 * (1 / p ^ 2)) (Cvs.L2a.TopCornerSum.KS c) = 1 := by
    rw [← hs, ← hu]; exact Cvs.L2a.TopCornerSum.uS_K (le_trans (by norm_num) hc)
  unfold Cvs.L2a.FrameFloorIntegerM.rhoTL Cvs.L2a.TopCornerSum.rhoT
  rw [hu, hs, hδ]
  refine max_le ((KcoBar_le hc hJ0 hJ).trans (by norm_num)) (supBelow_le (by norm_num) fun M hM => ?_)
  obtain ⟨hM3, hM68⟩ := Finset.mem_Ico.1 hM
  exact remT_le hp hcp hJ0 hJ hK hM3 (by omega)

/-- **`resLoc ≤ 7/100`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1` and every integer `M ≥ 3`. -/
theorem resLoc_le {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {M : ℕ} (hM : 3 ≤ M) :
    Cvs.L2a.FrameFloorIntegerM.resLoc c J M ≤ 7 / 100 := by
  have h1 := resB_le hc hJ0 hJ hM
  have h2 := rhoTL_le hc hJ0 hJ
  unfold Cvs.L2a.FrameFloorIntegerM.resLoc
  linarith

end Cvs.L2a.LocalResidualBound
