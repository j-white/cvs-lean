import Mathlib
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.CornerSuprema
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.LocalResidualBound
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.ScaledBandTransfer
import Cvs.L2a.TopCornerConstants
import Cvs.L2a.TopCornerSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `resLoc ≤ 7c^{−1/8}` for `c ≥ 10¹⁶`

`LocalResidualBound`'s pieces with `p = c^{1/8}` kept: at `q = 100/p ≤ 1` each piece is at most its `p = 100` bound times `q`
(the `T` envelope carries `q³`, shells and collars `q²` under a root, the strip `q³`), so
`resLoc ≤ (56/1000)q = 5.6c^{−1/8}`; `BandCouplingDischarged`'s full-span chain then runs at `ρ = 7c₁^{−1/8}`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.LocalResidualDecay

open Cvs.L2a.OrbitGapIntegerM Cvs.L2a.BandTransferKernelForm Cvs.L2a.BandTransferBandForm
open Cvs.L2a.LocalResidualBound

/-! ### The ratio `q = 100/p` -/

/-- `q = 100/p` with `p ≥ 100` lies in `(0, 1]`. -/
theorem q_mem {p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) : 0 < q ∧ q ≤ 1 := by
  have hp0 : 0 < p := by linarith
  refine ⟨by rw [hq]; positivity, ?_⟩
  rw [hq, div_le_one hp0]; exact hp

/-- `F/p^k = F q^k/100^k`. -/
theorem div_pow_q {p q F : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (k : ℕ) : F / p ^ k = F * q ^ k / 100 ^ k := by
  have hp0 : 0 < p := by linarith
  rw [hq, div_pow]; field_simp

/-- `q^k ≤ q^j` for `j ≤ k`, `0 ≤ q ≤ 1`. -/
theorem q_pow_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {j k : ℕ} (h : j ≤ k) : q ^ k ≤ q ^ j :=
  pow_le_pow_of_le_one hq0 hq1 h

/-! ### The `T` envelope with the decay kept -/

/-- **The `τ̂` envelope at `q`**: `LocalResidualBound`'s `tauHat_le` with the factor `q³ = 10⁶/p³` kept. -/
theorem tauHat_le_q {c x₀ δ p q S₁ S₂ S₃ B X : ℝ} {N : ℕ → ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8)
    (hx : 2 ≤ x₀) (hδ : 0 ≤ δ) (hN : ∀ j ≤ 3, 0 ≤ N j)
    (h1 : sigmaB (Ymax x₀ - 1) δ N 1 ≤ p ^ 2 * S₁) (h2 : sigmaB (Ymax x₀ - 1) δ N 2 ≤ p ^ 4 * S₂)
    (h3 : sigmaB (Ymax x₀ - 1) δ N 3 ≤ p ^ 6 * S₃)
    (hβ : betaW x₀ (1 / p ^ 2) ≤ B) (hB1 : B ≤ 1) (hχ : chirpW x₀ (1 / p ^ 2) ≤ X) :
    tauHat c x₀ (1 / p ^ 2) δ N
      ≤ q ^ 3 * (X * (3 * S₂ + S₃ / 3) / 4 + 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 + 9 * S₃ / 10 ^ 12) / 10 ^ 6 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
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
  have hq1' : √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) ≤ p ^ 3 * (2 * S₁ + S₂ / 2) / 2 := by
    refine (sqrt_mul_le_amgm s1 s2 h1 h2 (by positivity : (0 : ℝ) < 2 * p)).trans (le_of_eq ?_)
    field_simp
  have hq2' : √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) ≤ p ^ 5 * (3 * S₂ + S₃ / 3) / 2 := by
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
  have q53 : q ^ 5 ≤ q ^ 3 := q_pow_le hq0.le hq1 (by norm_num)
  have q93 : q ^ 9 ≤ q ^ 3 := q_pow_le hq0.le hq1 (by norm_num)
  have T1 : 2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
      * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) / c
      ≤ q ^ 3 * (3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4) / 10 ^ 6 := by
    have hA : 2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
        * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2)
        ≤ 2 * B * 3 * (p ^ 3 * (2 * S₁ + S₂ / 2) / 2) := by
      have := Real.exp_pos (betaW x₀ d * d)
      gcongr
    have hF : 0 ≤ 3 * B * (2 * S₁ + S₂ / 2) := by positivity
    calc 2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
          * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) / c
        ≤ 2 * B * 3 * (p ^ 3 * (2 * S₁ + S₂ / 2) / 2) / p ^ 8 := by
          rw [hc]; exact div_le_div_of_nonneg_right hA (by positivity)
      _ = 3 * B * (2 * S₁ + S₂ / 2) / p ^ 5 := by field_simp
      _ = 3 * B * (2 * S₁ + S₂ / 2) * q ^ 5 / 100 ^ 5 := div_pow_q hp hq 5
      _ ≤ 3 * B * (2 * S₁ + S₂ / 2) * q ^ 3 / 100 ^ 5 := by gcongr
      _ = q ^ 3 * (3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4) / 10 ^ 6 := by ring
  have T2 : chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) / (2 * c)
      ≤ q ^ 3 * (X * (3 * S₂ + S₃ / 3) / 4) / 10 ^ 6 := by
    have hA : chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3)
        ≤ X * (p ^ 5 * (3 * S₂ + S₃ / 3) / 2) := by gcongr
    calc chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) / (2 * c)
        ≤ X * (p ^ 5 * (3 * S₂ + S₃ / 3) / 2) / (2 * p ^ 8) := by
          rw [hc]; exact div_le_div_of_nonneg_right hA (by positivity)
      _ = X * (3 * S₂ + S₃ / 3) / 4 / p ^ 3 := by field_simp; ring
      _ = X * (3 * S₂ + S₃ / 3) / 4 * q ^ 3 / 100 ^ 3 := div_pow_q hp hq 3
      _ = q ^ 3 * (X * (3 * S₂ + S₃ / 3) / 4) / 10 ^ 6 := by ring
  have T3 : (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 / (√(5 * π) * √((c * d / 2) ^ 5))
      ≤ q ^ 3 * (9 * S₃ / 10 ^ 12) / 10 ^ 6 := by
    have hA : (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 ≤ 4 * (p ^ 6 * S₃) := by
      have := Real.exp_pos (2 * betaW x₀ d * d)
      gcongr
    have hD : 39 / 10 * (p ^ 15 / 8) ≤ √(5 * π) * √((c * d / 2) ^ 5) :=
      mul_le_mul h5π hcd (by positivity) (by positivity)
    calc (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 / (√(5 * π) * √((c * d / 2) ^ 5))
        ≤ 4 * (p ^ 6 * S₃) / (39 / 10 * (p ^ 15 / 8)) := by
          refine div_le_div₀ (by positivity) hA (by positivity) hD
      _ = 320 / 39 * S₃ / p ^ 9 := by field_simp; ring
      _ ≤ 9 * S₃ / p ^ 9 := by gcongr; norm_num
      _ = 9 * S₃ * q ^ 9 / 100 ^ 9 := div_pow_q hp hq 9
      _ ≤ 9 * S₃ * q ^ 3 / 100 ^ 9 := by gcongr
      _ = q ^ 3 * (9 * S₃ / 10 ^ 12) / 10 ^ 6 := by ring
  unfold tauHat
  have e : q ^ 3 * (X * (3 * S₂ + S₃ / 3) / 4 + 3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4 + 9 * S₃ / 10 ^ 12) / 10 ^ 6
      = q ^ 3 * (3 * B * (2 * S₁ + S₂ / 2) / 10 ^ 4) / 10 ^ 6 + q ^ 3 * (X * (3 * S₂ + S₃ / 3) / 4) / 10 ^ 6
        + q ^ 3 * (9 * S₃ / 10 ^ 12) / 10 ^ 6 := by ring
  rw [e]
  linarith

/-- `2(q³T)Y/10⁶ + (q³T)²G/10¹² ≤ q²(2TY/10⁶ + T²G/10¹²)` for `0 ≤ q ≤ 1` and `T, Y, G ≥ 0`. -/
theorem env_scale {q T Y G : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 ≤ T) (hY : 0 ≤ Y) (hG : 0 ≤ G) :
    2 * (q ^ 3 * T) * Y / 10 ^ 6 + (q ^ 3 * T) ^ 2 * G / 10 ^ 12
      ≤ q ^ 2 * (2 * T * Y / 10 ^ 6 + T ^ 2 * G / 10 ^ 12) := by
  have h3 : q ^ 3 ≤ q ^ 2 := q_pow_le hq0 hq1 (by norm_num)
  have h6 : q ^ 6 ≤ q ^ 2 := q_pow_le hq0 hq1 (by norm_num)
  have a : 0 ≤ 2 * T * Y / 10 ^ 6 := by positivity
  have b : 0 ≤ T ^ 2 * G / 10 ^ 12 := by positivity
  calc 2 * (q ^ 3 * T) * Y / 10 ^ 6 + (q ^ 3 * T) ^ 2 * G / 10 ^ 12
      = q ^ 3 * (2 * T * Y / 10 ^ 6) + q ^ 6 * (T ^ 2 * G / 10 ^ 12) := by ring
    _ ≤ q ^ 2 * (2 * T * Y / 10 ^ 6) + q ^ 2 * (T ^ 2 * G / 10 ^ 12) := by gcongr
    _ = q ^ 2 * (2 * T * Y / 10 ^ 6 + T ^ 2 * G / 10 ^ 12) := by ring

/-- **Regime II at `q`**: `T(c, x₀, δ, δ, r, J) ≤ q²((11·10⁻⁴)²u⁴ + (21·10⁻⁶)²u²)`, `u = 1/x₀`, `2 ≤ x₀ ≤ 549`. -/
theorem tT_regII_q {c x₀ r J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hx : 2 ≤ x₀)
    (hx' : x₀ ≤ 549) (hr : 4 / 3 / p ^ 2 ≤ r) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.tT c x₀ (1 / p ^ 2) (1 / p ^ 2) r J
      ≤ q ^ 2 * ((11 / 10 ^ 4) ^ 2 * (1 / x₀) ^ 4 + (21 / 10 ^ 6) ^ 2 * (1 / x₀) ^ 2) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
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
  have hτ := tauHat_le_q hp hq hc hx (by positivity) hN h1 h2 h3 hβ (by linarith) hχ
  have hτ0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg (c := c) (x₀ := x₀) (d := 1 / p ^ 2) (δ := 1 / p ^ 2)
    (by rw [hc]; positivity) (by positivity) (by linarith [hd]) (by positivity) hN
  obtain ⟨hG0, hG⟩ := G_le hp hc hx hJ0 hJ
  have hY := Y_le hp hc hx hJ0 hJ (δ := 1 / p ^ 2) (by positivity) le_rfl
  have hT0 : 0 ≤ 19 / 10 * (1 / x₀) ^ 3 * (3 * S₂ + S₃ / 3) / 4 + 3 * (14 / 10 * (1 / x₀)) * (2 * S₁ + S₂ / 2) / 10 ^ 4
      + 9 * S₃ / 10 ^ 12 := by positivity
  refine (tT_le_env hτ0 hτ hY hG0 hG).trans ((env_scale hq0.le hq1 hT0 (by positivity) (by positivity)).trans ?_)
  exact mul_le_mul_of_nonneg_left (poly_regII hu0 hu2 hu549 hS₁ hS₂ hS₃ h10 h20 h30) (by positivity)

/-- **Regime I at `q`** (`δ/3 ≤ δ′ ≤ δ`, `r ≥ δ/3`): `T(c, x₀, δ, δ′, r, J) ≤ q²·1.5·10⁻⁶` for `x₀ ≥ 2`. -/
theorem tT_regI_q {c x₀ δ r J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hx : 2 ≤ x₀)
    (hδlo : 1 / 3 / p ^ 2 ≤ δ) (hδhi : δ ≤ 1 / p ^ 2) (hr : 1 / 3 / p ^ 2 ≤ r) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.tT c x₀ (1 / p ^ 2) δ r J ≤ q ^ 2 * (15 / 10 ^ 7) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
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
  have hτ := tauHat_le_q hp hq hc hx (by positivity) hN h1 h2 h3
    (hβ.trans (by gcongr : 14 / 10 * u ≤ 14 / 10 * (1 / 2)))
    (by norm_num) (hχ.trans (by gcongr : 19 / 10 * u ^ 3 ≤ 19 / 10 * (1 / 2) ^ 3))
  have hτ0 := Cvs.L2a.ScaledBandTransfer.tauHat_nonneg (c := c) (x₀ := x₀) (d := 1 / p ^ 2) (δ := t ^ 2)
    (by rw [hc]; positivity) (by positivity) (by linarith) (by positivity) hN
  obtain ⟨hG0, hG⟩ := G_le hp hc hx hJ0 hJ
  have hY := Y_le hp hc hx hJ0 hJ (δ := t ^ 2) (by positivity) hδhi
  have hYc : 66 / 100 * u ^ 2 + 72 / 10000 * u ≤ 66 / 100 * (1 / 2) ^ 2 + 72 / 10000 * (1 / 2) := by gcongr
  have hGc : 201 / 100 * u ^ 2 ≤ 201 / 100 * (1 / 2) ^ 2 := by gcongr
  refine (tT_le_env hτ0 hτ (hY.trans hYc) hG0 (hG.trans hGc)).trans
    ((env_scale hq0.le hq1 (by norm_num) (by norm_num) (by norm_num)).trans ?_)
  exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)

/-- `δ = 1/p² = q²/10⁴`. -/
theorem delta_q {p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) : 1 / p ^ 2 = q ^ 2 / 10 ^ 4 := by
  have hp0 : 0 < p := by linarith
  rw [hq]; field_simp; norm_num

/-! ### The bottom chirps and corrections at `q` -/

section chirp

open Cvs.L2a.LocalisedBottomCorners (tT eSh dSh nSh iSh bP)

/-- **The `m = 2` chirp at `q`**: `E₂ ≤ q²(1.387·10⁻³)²`. -/
theorem e2_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.e2 c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) J ≤ q ^ 2 * (1387 / 10 ^ 6) ^ 2 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
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
  set A : ℕ → ℝ := fun k => 2 / π * (q ^ 2 * (15 / 10 ^ 7)) * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) with hA
  set B : ℕ → ℝ := fun k => 2 / π * (q ^ 2 * T₂) * (4 * π ^ 2 * (eSh s (k + 1) - eSh s k)) with hB
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
    · refine base _ (tT_regI_q hp hq hc le_rfl ?_ (min_le_left _ _) ?_ hJ0 hJ)
      · refine le_min (by gcongr; norm_num) ?_
        rw [hs3]; linarith
      · rw [hs3]; linarith
    · have hek2 : s * 4 ≤ eSh s k := by
        have := eSh_mono hs0.le (by omega : 2 ≤ k); rwa [he2] at this
      have hdk : dSh (1 / p ^ 2) s k = 1 / p ^ 2 := min_eq_left (by linarith)
      refine base (q ^ 2 * T₂) ?_
      rw [hdk]
      have := tT_regII_q (x₀ := 2) hp hq hc le_rfl (by norm_num) (r := eSh s k / 4) (by rw [hs43]; linarith) hJ0 hJ
      simpa [hT₂] using this
  unfold Cvs.L2a.LocalisedBottomCorners.e2
  refine (sum_split_two hA0 hB0 hterm).trans ?_
  have hAs : A 0 + A 1 = 8 * π * (q ^ 2 * (15 / 10 ^ 7)) * (eSh s 2 - eSh s 0) := by
    simp only [hA]; field_simp; ring
  have hBs : ∑ k ∈ Finset.range (nSh s), B k = 8 * π * (q ^ 2 * T₂) * (eSh s (nSh s) - eSh s 0) := by
    simp only [hB]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub (eSh s)]
    field_simp; ring
  rw [hAs, hBs, he0, he2]
  have hn1 := eSh_le_one s (nSh s)
  have hπ4 : π ≤ 31416 / 10000 := pi_bounds.2
  have hsle : s ≤ 4 / 3 * (1 / 10 ^ 4) := by rw [hs]; linarith
  have hT₂0 : 0 ≤ T₂ := by positivity
  calc 8 * π * (q ^ 2 * (15 / 10 ^ 7)) * (s * 4 - s) + 8 * π * (q ^ 2 * T₂) * (eSh s (nSh s) - s)
      ≤ 8 * π * (q ^ 2 * (15 / 10 ^ 7)) * (3 * (4 / 3 * (1 / 10 ^ 4))) + 8 * π * (q ^ 2 * T₂) * 1 := by
        gcongr
        · linarith
        · linarith
    _ ≤ 8 * (31416 / 10000) * (q ^ 2 * (15 / 10 ^ 7)) * (3 * (4 / 3 * (1 / 10 ^ 4)))
        + 8 * (31416 / 10000) * (q ^ 2 * T₂) * 1 := by gcongr
    _ = q ^ 2 * (8 * (31416 / 10000) * (15 / 10 ^ 7) * (3 * (4 / 3 * (1 / 10 ^ 4)))
        + 8 * (31416 / 10000) * T₂ * 1) := by ring
    _ ≤ q ^ 2 * (1387 / 10 ^ 6) ^ 2 := by gcongr; rw [hT₂]; norm_num

/-- **The near chirps at `q`**: `E^n_m ≤ q²(0.5644(11·10⁻⁴u² + 21·10⁻⁶u))²`, `u = 1/m`, `3 ≤ m ≤ 549`. -/
theorem eN_le_q {c J p q m : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hm3 : 3 ≤ m) (hm549 : m ≤ 549)
    (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.eN c (1 / p ^ 2) (1 / p ^ 2) m J
      ≤ q ^ 2 * (5644 / 10 ^ 4 * (11 / 10 ^ 4 * (1 / m) ^ 2 + 21 / 10 ^ 6 * (1 / m))) ^ 2 := by
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
  have hT := tT_regII_q hp hq hc (by linarith) hm549 hr hJ0 hJ
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
      ≤ 2 / (31415 / 10000) * (q ^ 2 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) * (1 / 2 + 1 / 3000) := by
        gcongr
        exact hT.trans (mul_le_mul_of_nonneg_left hW (sq_nonneg q))
    _ = q ^ 2 * (2 / (31415 / 10000) * (1 / 2 + 1 / 3000) * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) := by ring
    _ ≤ q ^ 2 * ((5644 / 10 ^ 4) ^ 2 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) := by gcongr; norm_num
    _ = q ^ 2 * (5644 / 10 ^ 4 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u)) ^ 2 := by ring

/-- **The far chirps at `q`**: `E^f_m ≤ q²(1.0302(11·10⁻⁴u² + 21·10⁻⁶u))²`, `u = 1/m`, `2 ≤ m ≤ 549`, `m < M`. -/
theorem eFar_le_q {c J p q : ℝ} {m M : ℕ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hm2 : 2 ≤ m)
    (hm549 : m ≤ 549) (hmM : m + 1 ≤ M) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.eFar c (1 / p ^ 2) (Cvs.L2a.LocalisedBottomCorners.deltaM (1 / p ^ 2) m) m M J
      ≤ q ^ 2 * (10302 / 10 ^ 4 * (11 / 10 ^ 4 * (1 / (m : ℝ)) ^ 2 + 21 / 10 ^ 6 * (1 / (m : ℝ)))) ^ 2 := by
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
  have hT := tT_regII_q hp hq hc hm2r hm549r hr hJ0 hJ
  have hT0 := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := m) (d := δ) (δ := δ) (r := ((M : ℝ) - bP m δ) / m)
    (J := J) hc0 hd0.le (by linarith) hd0.le hJ0 (by apply div_pos <;> linarith)
  have hπ : 2 / π ≤ 2 / (31415 / 10000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_bounds.1
  set u := 1 / (m : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hW : (11 / 10 ^ 4) ^ 2 * u ^ 4 + (21 / 10 ^ 6) ^ 2 * u ^ 2 ≤ (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2 := by
    nlinarith [pow_pos hu0 3]
  unfold Cvs.L2a.LocalisedBottomCorners.eFar
  calc 2 / π * tT c m δ δ (((M : ℝ) - bP m δ) / m) J / ((M : ℝ) - bP m δ)
      ≤ 2 / (31415 / 10000) * (q ^ 2 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) / (6 / 10) := by
        gcongr
        exact hT.trans (mul_le_mul_of_nonneg_left hW (sq_nonneg q))
    _ = q ^ 2 * (2 / (31415 / 10000) / (6 / 10) * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) := by ring
    _ ≤ q ^ 2 * ((10302 / 10 ^ 4) ^ 2 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u) ^ 2) := by gcongr; norm_num
    _ = q ^ 2 * (10302 / 10 ^ 4 * (11 / 10 ^ 4 * u ^ 2 + 21 / 10 ^ 6 * u)) ^ 2 := by ring

end chirp

/-- `K₂ ≤ q²·10⁻¹³` at `s = (4/3)/p²`, `c = p⁸`. -/
theorem k2_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.k2 c (4 / 3 * (1 / p ^ 2)) J ≤ q ^ 2 * (1 / 10 ^ 13) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
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
  have hint : ∫ t in (1 : ℝ)..(2 - s), (1 - Cvs.L2a.FarIntegrationByParts.wF t)
      * Cvs.L2a.CutKernelSimplified.kNear c 2 (t / 2) (Ymax 2) ^ 2 * Cvs.L2a.LocalisedBottomCorners.envN 2 t ≤ 300 / s ^ 4 := by
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
  have q82 : q ^ 8 ≤ q ^ 2 := q_pow_le hq0.le hq1 (by norm_num)
  unfold Cvs.L2a.LocalisedBottomCorners.k2
  rw [hkap]
  have hc2 : 0 < c ^ 2 := by positivity
  calc Cvs.L2a.LocalisedConstants.kappaI J c / c ^ 2 * ∫ t in (1 : ℝ)..(2 - s), (1 - Cvs.L2a.FarIntegrationByParts.wF t)
        * Cvs.L2a.CutKernelSimplified.kNear c 2 (t / 2) (Ymax 2) ^ 2 * Cvs.L2a.LocalisedBottomCorners.envN 2 t
      ≤ Cvs.L2a.LocalisedConstants.kappaI J c / c ^ 2 * (300 / s ^ 4) := by gcongr
    _ ≤ 1 / c ^ 2 * (300 / s ^ 4) := by gcongr
    _ = 300 * 81 / 256 / p ^ 8 := by rw [hc, hs]; field_simp; ring
    _ = 300 * 81 / 256 * q ^ 8 / 100 ^ 8 := div_pow_q hp hq 8
    _ ≤ 300 * 81 / 256 * q ^ 2 / 100 ^ 8 := by gcongr
    _ ≤ q ^ 2 * (1 / 10 ^ 13) := by
        rw [show 300 * 81 / 256 * q ^ 2 / 100 ^ 8 = q ^ 2 * (300 * 81 / 256 / 100 ^ 8) by ring]
        exact mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)

/-- `K_m ≤ q²(10⁻⁶)²` for `2 ≤ m ≤ M − 1`. -/
theorem kT_le_q {c J p q : ℝ} {m M : ℕ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) (hm2 : 2 ≤ m) (hmM : m + 1 ≤ M) :
    Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J ≤ q ^ 2 * (1 / 10 ^ 6) ^ 2 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc16 : 10 ^ 16 ≤ c := by rw [hc]; exact hp8
  have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  obtain ⟨hN, hF⟩ := kN_kF_le (J := J) (by linarith) hJ0 hJ hm2r hmMr
  have q162 : q ^ 16 ≤ q ^ 2 := q_pow_le hq0.le hq1 (by norm_num)
  have hc2 : 64 / c ^ 2 ≤ q ^ 2 * (64 / 10 ^ 32) := by
    calc 64 / c ^ 2 = 64 / p ^ 16 := by rw [hc]; ring
      _ = 64 * q ^ 16 / 100 ^ 16 := div_pow_q hp hq 16
      _ ≤ 64 * q ^ 2 / 100 ^ 16 := by gcongr
      _ = q ^ 2 * (64 / 10 ^ 32) := by ring
  unfold Cvs.L2a.LocalisedBottomCorners.kT
  split_ifs with h
  · have := k2_le_q hp hq hc hJ0 hJ
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    linarith
  · have hm3 : (3 : ℝ) ≤ m := by
      have : m ≠ 2 := fun h' => h (by rw [h']; norm_num)
      exact_mod_cast (show 3 ≤ m by omega)
    have := hN hm3
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    linarith

/-! ### `resB ≤ (41/1000)q` -/

section bottom

/-- **The chirp and correction sum at `q`**: `2Σ_{2 ≤ m < min(M, 550)}(√E_m + √K_m) ≤ q/100`. -/
theorem sum_E_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) {M : ℕ} (hM : 3 ≤ M) :
    2 * ∑ m ∈ Finset.Ico 2 (min M 550),
        (√(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M J)
          + √(Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J)) ≤ q / 100 := by
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  set K := min M 550 with hK
  have hK3 : 3 ≤ K := le_min hM (by norm_num)
  have hKM : K ≤ M := min_le_left _ _
  have hK550 : K ≤ 550 := min_le_right _ _
  set W : ℕ → ℝ := fun m => 11 / 10 ^ 4 * (1 / (m : ℝ)) ^ 2 + 21 / 10 ^ 6 * (1 / (m : ℝ)) with hW
  have hW0 : ∀ m, 0 ≤ W m := fun m => by simp only [hW]; positivity
  have hk : ∀ m ∈ Finset.Ico 2 K, √(Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J) ≤ q * (1 / 10 ^ 6) :=
    fun m hm => by
      obtain ⟨hm2, hmK⟩ := Finset.mem_Ico.1 hm
      refine sqrt_le_of_le_sq (by positivity) ?_
      rw [mul_pow]
      exact kT_le_q hp hq hc hJ0 hJ hm2 (by omega)
  have he2 : √(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) ((2 : ℕ) : ℝ) M J)
      ≤ q * (1387 / 10 ^ 6 + 10302 / 10 ^ 4 * W 2) := by
    have hw := hW0 2
    refine sqrt_le_of_le_sq (by positivity) ?_
    unfold Cvs.L2a.LocalisedBottomCorners.eT
    rw [if_pos (by norm_num)]
    have a := e2_le_q hp hq hc hJ0 hJ
    have b : Cvs.L2a.LocalisedBottomCorners.eFar c (1 / p ^ 2) (Cvs.L2a.LocalisedBottomCorners.deltaM (1 / p ^ 2) ((2 : ℕ) : ℝ))
        ((2 : ℕ) : ℝ) M J ≤ q ^ 2 * (10302 / 10 ^ 4 * W 2) ^ 2 :=
      eFar_le_q hp hq hc (m := 2) (M := M) le_rfl (by norm_num) (by omega) hJ0 hJ
    have : 0 ≤ q ^ 2 * (1387 / 10 ^ 6 * (10302 / 10 ^ 4 * W 2)) := by positivity
    nlinarith
  have hem : ∀ m ∈ Finset.Ico 3 K,
      √(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M J)
        ≤ q * ((5644 / 10 ^ 4 + 10302 / 10 ^ 4) * W m) := fun m hm => by
    obtain ⟨hm3, hmK⟩ := Finset.mem_Ico.1 hm
    have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hm549 : (m : ℝ) ≤ 549 := by exact_mod_cast (show m ≤ 549 by omega)
    have hw := hW0 m
    refine sqrt_le_of_le_sq (by positivity) ?_
    unfold Cvs.L2a.LocalisedBottomCorners.eT
    rw [if_neg (by linarith)]
    have a : Cvs.L2a.LocalisedBottomCorners.eN c (1 / p ^ 2) (1 / p ^ 2) (m : ℝ) J ≤ q ^ 2 * (5644 / 10 ^ 4 * W m) ^ 2 :=
      eN_le_q hp hq hc hm3r hm549 hJ0 hJ
    have b : Cvs.L2a.LocalisedBottomCorners.eFar c (1 / p ^ 2) (Cvs.L2a.LocalisedBottomCorners.deltaM (1 / p ^ 2) (m : ℝ))
        (m : ℝ) M J ≤ q ^ 2 * (10302 / 10 ^ 4 * W m) ^ 2 :=
      eFar_le_q hp hq hc (m := m) (M := M) (by omega) (by omega) (by omega) hJ0 hJ
    have : 0 ≤ q ^ 2 * (5644 / 10 ^ 4 * W m * (10302 / 10 ^ 4 * W m)) := by positivity
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
  have hEm : ∑ m ∈ Finset.Ico 3 K,
      √(Cvs.L2a.LocalisedBottomCorners.eT c (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M J)
        ≤ q * ((5644 / 10 ^ 4 + 10302 / 10 ^ 4) * (11 / 10 ^ 4 * (1 / 2) + 21 / 10 ^ 6 * 7)) := by
    refine (Finset.sum_le_sum hem).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    gcongr
  have hKsum : ∑ m ∈ Finset.Ico 2 K, √(Cvs.L2a.LocalisedBottomCorners.kT c (4 / 3 * (1 / p ^ 2)) m M J)
      ≤ q * (548 * (1 / 10 ^ 6)) := by
    refine (Finset.sum_le_sum hk).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    have : ((K - 2 : ℕ) : ℝ) ≤ 548 := by exact_mod_cast (show K - 2 ≤ 548 by omega)
    nlinarith
  have hW2 : W 2 = 11 / 10 ^ 4 * (1 / 2) ^ 2 + 21 / 10 ^ 6 * (1 / 2) := by simp only [hW]; norm_num
  rw [Finset.sum_add_distrib, hsplit]
  rw [hW2] at he2
  linarith

/-- `𝒮_b ≤ q·10⁻⁴` at `s = (4/3)/p²`, `c = p⁸`, `0 ≤ J ≤ c/4 + 1`. -/
theorem stripB_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.LocalisedBottomCorners.stripB c (4 / 3 * (1 / p ^ 2)) J ≤ q * (1 / 10 ^ 4) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc0 : 0 < c := by rw [hc]; positivity
  set s := 4 / 3 * (1 / p ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 4 / 3 * (1 / 10 ^ 4) := by rw [hs]; linarith
  have hsq : s = q ^ 2 * (4 / 3 * (1 / 10 ^ 4)) := by rw [hs, delta_q hp hq]; ring
  obtain ⟨hπ1, hπ2⟩ := pi_bounds
  have hJc : J / c ≤ 2501 / 10000 := by
    rw [div_le_iff₀ hc0]; rw [hc] at hJ ⊢; nlinarith
  have hX : π * J * s / c ≤ (q * (103 / 10000)) ^ 2 := by
    have e : π * J * s / c = π * (J / c) * s := by ring
    rw [e, hsq]
    calc π * (J / c) * (q ^ 2 * (4 / 3 * (1 / 10 ^ 4)))
        ≤ 31416 / 10000 * (2501 / 10000) * (q ^ 2 * (4 / 3 * (1 / 10 ^ 4))) := by gcongr
      _ = q ^ 2 * (31416 / 10000 * (2501 / 10000) * (4 / 3 * (1 / 10 ^ 4))) := by ring
      _ ≤ q ^ 2 * (103 / 10000) ^ 2 := by gcongr; norm_num
      _ = (q * (103 / 10000)) ^ 2 := by ring
  have hsqrt : √(π * J * s / c) ≤ q * (103 / 10000) := sqrt_le_of_le_sq (by positivity) hX
  have hF : 8 / (4 - s) + 2 * s / (2 - s) ≤ 8 / 3 + 2 := by
    have h1 : 8 / (4 - s) ≤ 8 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h2 : 2 * s / (2 - s) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hF0 : 0 ≤ 8 / (4 - s) + 2 * s / (2 - s) := by
    have : 0 < 4 - s := by linarith
    have : 0 < 2 - s := by linarith
    positivity
  have q31 : q ^ 3 ≤ q := by simpa using q_pow_le hq0.le hq1 (show 1 ≤ 3 by norm_num)
  unfold Cvs.L2a.LocalisedBottomCorners.stripB
  calc 2 * π * s * √(π * J * s / c) * (8 / (4 - s) + 2 * s / (2 - s))
      ≤ 2 * (31416 / 10000) * (q ^ 2 * (4 / 3 * (1 / 10 ^ 4))) * (q * (103 / 10000)) * (8 / 3 + 2) := by
        rw [← hsq]; gcongr
    _ = q ^ 3 * (2 * (31416 / 10000) * (4 / 3 * (1 / 10 ^ 4)) * (103 / 10000) * (8 / 3 + 2)) := by ring
    _ ≤ q * (2 * (31416 / 10000) * (4 / 3 * (1 / 10 ^ 4)) * (103 / 10000) * (8 / 3 + 2)) := by gcongr
    _ ≤ q * (1 / 10 ^ 4) := by gcongr; norm_num

/-- The tail `[M > 550](k_f/c)T̄_bot(550) ≤ q·10⁻¹⁰` at `c = p⁸`, `0 ≤ J ≤ c/4 + 1`. -/
theorem tail_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) (M : ℕ) :
    (if 550 < M then Cvs.L2a.LocalisedBottomCorners.kFb c / c
        * Cvs.L2a.CornerSuprema.Tbar (Cvs.L2a.LocalisedBottomCorners.kapI c J) 550 else 0) ≤ q * (1 / 10 ^ 10) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  split_ifs
  · have hp8 : 10 ^ 16 ≤ p ^ 8 := by
      calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
        _ ≤ p ^ 8 := by gcongr
    have hc16 : 10 ^ 16 ≤ c := by rw [hc]; exact hp8
    have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
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
    have q81 : q ^ 8 ≤ q := by simpa using q_pow_le hq0.le hq1 (show 1 ≤ 8 by norm_num)
    rw [hkap]
    calc Cvs.L2a.LocalisedBottomCorners.kFb c / c * Cvs.L2a.CornerSuprema.Tbar (Cvs.L2a.LocalisedConstants.kappaI J c) 550
        ≤ 8 / c * (1238 / 10000) := by
          gcongr
          linarith
      _ = 8 * (1238 / 10000) / p ^ 8 := by rw [hc]; ring
      _ = 8 * (1238 / 10000) * q ^ 8 / 100 ^ 8 := div_pow_q hp hq 8
      _ ≤ 8 * (1238 / 10000) * q / 100 ^ 8 := by gcongr
      _ ≤ q * (1 / 10 ^ 10) := by
          rw [show 8 * (1238 / 10000) * q / 100 ^ 8 = q * (8 * (1238 / 10000) / 100 ^ 8) by ring]
          exact mul_le_mul_of_nonneg_left (by norm_num) hq0.le
  · positivity

end bottom

section lam

open Cvs.L2a.LocalisedBottomCorners (gT collF bP eSh dSh nSh iSh)

/-- **`Σ lamX ≤ q²·8.12·10⁻⁴`** at `δ = 1/p²`, `s = 4δ/3`, `c = p⁸`, `q = 100/p`, every `M ≥ 3`. -/
theorem sum_lamX_le_q {c δ s p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hδ : δ = 1 / p ^ 2)
    (hs : s = 4 / 3 * δ) {M : ℕ} (hM : 3 ≤ M) :
    ∑ m ∈ Finset.Ico 2 (min M 550), Cvs.L2a.FrameFloorIntegerM.lamX c δ s m M ≤ q ^ 2 * (812 / 10 ^ 6) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ4 : δ ≤ 1 / 10 ^ 4 := by rw [hδ]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hδq : δ = q ^ 2 / 10 ^ 4 := by rw [hδ]; exact delta_q hp hq
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hπ2 : 9869 / 1000 ≤ π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hπ0 : 0 < π ^ 2 := by positivity
  have q62 : q ^ 6 ≤ q ^ 2 := q_pow_le hq0.le hq1 (by norm_num)
  have q82 : q ^ 8 ≤ q ^ 2 := q_pow_le hq0.le hq1 (by norm_num)
  have hic : 1 / (π ^ 2 * c) ≤ q ^ 2 * (1 / 10 ^ 16) := by
    have h1 : 1 / (π ^ 2 * c) ≤ 1 / c := one_div_le_one_div_of_le hc0 (by nlinarith)
    calc 1 / (π ^ 2 * c) ≤ 1 / c := h1
      _ = 1 / p ^ 8 := by rw [hc]
      _ = 1 * q ^ 8 / 100 ^ 8 := div_pow_q hp hq 8
      _ ≤ 1 * q ^ 2 / 100 ^ 8 := by gcongr
      _ = q ^ 2 * (1 / 10 ^ 16) := by ring
  have his : 1 / s / (π ^ 2 * c) ≤ q ^ 2 * (1 / 10 ^ 12) := by
    have e : 1 / s / (π ^ 2 * c) = 3 / 4 / π ^ 2 * (1 / p ^ 6) := by rw [hs, hδ, hc]; field_simp
    rw [e]
    have h1 : 3 / 4 / π ^ 2 ≤ 1 := by rw [div_le_one hπ0]; linarith
    have h2 : 1 / p ^ 6 ≤ q ^ 2 * (1 / 10 ^ 12) := by
      calc 1 / p ^ 6 = 1 * q ^ 6 / 100 ^ 6 := div_pow_q hp hq 6
        _ ≤ 1 * q ^ 2 / 100 ^ 6 := by gcongr
        _ = q ^ 2 * (1 / 10 ^ 12) := by ring
    calc 3 / 4 / π ^ 2 * (1 / p ^ 6) ≤ 1 * (q ^ 2 * (1 / 10 ^ 12)) :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = q ^ 2 * (1 / 10 ^ 12) := one_mul _
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
  -- each term is `q²` times its `p = 100` value
  have t2 : 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / 2) ≤ q ^ 2 * (239 / 10 ^ 7) := by
    have h1 : 12 * (181 / 462) / π ^ 2 ≤ 12 * (181 / 462) / (9869 / 1000) := by gcongr
    have h2 : 1 / (1 - δ) ^ 2 ≤ 1 / (1 - 1 / 10 ^ 4) ^ 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      gcongr
    calc 12 * (181 / 462) / π ^ 2 * δ / (1 - δ) ^ 2 * (1 / 2)
        = 12 * (181 / 462) / π ^ 2 * (q ^ 2 / 10 ^ 4) * (1 / (1 - δ) ^ 2) / 2 := by rw [← hδq]; ring
      _ ≤ 12 * (181 / 462) / (9869 / 1000) * (q ^ 2 / 10 ^ 4) * (1 / (1 - 1 / 10 ^ 4) ^ 2) / 2 := by gcongr
      _ = q ^ 2 * (12 * (181 / 462) / (9869 / 1000) / 10 ^ 4 * (1 / (1 - 1 / 10 ^ 4) ^ 2) / 2) := by ring
      _ ≤ q ^ 2 * (239 / 10 ^ 7) := mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)
  have t3 : 4 * (181 / 462) / π ^ 2 * δ * (9884 / 1000) ≤ q ^ 2 * (157 / 10 ^ 6) := by
    calc 4 * (181 / 462) / π ^ 2 * δ * (9884 / 1000)
        ≤ 4 * (181 / 462) / (9869 / 1000) * (q ^ 2 / 10 ^ 4) * (9884 / 1000) := by
          rw [← hδq]; gcongr
      _ = q ^ 2 * (4 * (181 / 462) / (9869 / 1000) / 10 ^ 4 * (9884 / 1000)) := by ring
      _ ≤ q ^ 2 * (157 / 10 ^ 6) := mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)
  have t1 : 16 * (181 / 462) * δ = q ^ 2 * (16 * (181 / 462) / 10 ^ 4) := by rw [hδq]; ring
  rw [hsplit]
  linarith

end lam

/-- **`resB ≤ (41/1000)q`** at `δ(c) = 1/p²`, `c = p⁸`, `q = 100/p`, `0 ≤ J ≤ c/4 + 1`, every `M ≥ 3`. -/
theorem resB_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hδ : Cvs.L2a.TopCornerSum.deltaS c = 1 / p ^ 2)
    (hcp : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {M : ℕ} (hM : 3 ≤ M) :
    Cvs.L2a.FrameFloorIntegerM.resB c J M ≤ q * (41 / 1000) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hs : Cvs.L2a.TopCornerSum.sS c = 4 / 3 * (1 / p ^ 2) := by unfold Cvs.L2a.TopCornerSum.sS; rw [hδ]
  have hW := Cvs.L2a.CornerSuprema.rbot_le M (min M 550) (min_le_left _ _)
  have hWs : √(∑ m ∈ Finset.Ico 2 (min M 550), (Cvs.L2a.CornerSuprema.Lnear (m : ℝ)
      + Cvs.L2a.CornerSuprema.Lfar (m : ℝ) (M : ℝ))) ≤ 20192 / 100000 :=
    (Real.sqrt_le_sqrt hW).trans Cvs.L2a.LocalisedConstants.sqrt_rbarBotSq_le
  have hL := sum_lamX_le_q hp hq hcp rfl rfl hM
  have hLs : √(∑ m ∈ Finset.Ico 2 (min M 550), Cvs.L2a.FrameFloorIntegerM.lamX c (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M)
      ≤ q * (285 / 10000) := by
    refine sqrt_le_of_le_sq (by positivity) (hL.trans ?_)
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)
  have hE := sum_E_le_q hp hq hcp hJ0 hJ hM
  have hS := stripB_le_q hp hq hcp hJ0 hJ
  have hT := tail_le_q hp hq hcp hJ0 hJ M
  have hπ : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hd2 : (1 / p ^ 2) ^ 2 ≤ (1 / 10 ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) hd4 2
  have q41 : q ^ 4 ≤ q := by simpa using q_pow_le hq0.le hq1 (show 1 ≤ 4 by norm_num)
  have hdq : (1 / p ^ 2) ^ 2 ≤ q * (1 / 10 ^ 4) ^ 2 := by
    rw [delta_q hp hq]
    calc (q ^ 2 / 10 ^ 4) ^ 2 = q ^ 4 * (1 / 10 ^ 4) ^ 2 := by ring
      _ ≤ q * (1 / 10 ^ 4) ^ 2 := by gcongr
  unfold Cvs.L2a.FrameFloorIntegerM.resB
  rw [hs, hδ]
  have a1 : π ^ 2 * (1 / p ^ 2) ^ 2 * √(∑ m ∈ Finset.Ico 2 (min M 550), (Cvs.L2a.CornerSuprema.Lnear (m : ℝ)
      + Cvs.L2a.CornerSuprema.Lfar (m : ℝ) (M : ℝ))) ≤ 10 * (q * (1 / 10 ^ 4) ^ 2) * (20192 / 100000) := by
    gcongr
  have a2 : (1 + π ^ 2 * (1 / p ^ 2) ^ 2)
      * √(∑ m ∈ Finset.Ico 2 (min M 550), Cvs.L2a.FrameFloorIntegerM.lamX c (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) m M)
      ≤ (1 + 10 * (1 / 10 ^ 4) ^ 2) * (q * (285 / 10000)) := by gcongr
  norm_num at a1 a2 hE hS hT ⊢
  linarith

/-! ### The top remainder at `q` -/

section top

open Cvs.L2a.LocalisedBottomCorners (eSh)
open Cvs.L2a.TopCornerSum (shellSet dK collSh psiSh collC chirpC Bloc Bloc2 tC)
open Cvs.L2a.CornerSuprema (theta2Int Theta)

/-- **The `m = 2` collar at `q`**: `C₂ ≤ q²·0.0357²` at `δ = 1/p²`. -/
theorem collC_two_le_q {p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) {K : ℕ}
    (hK : eSh (4 / 3 * (1 / p ^ 2)) K = 1) :
    collC (1 / p ^ 2) (eSh (4 / 3 * (1 / p ^ 2))) K 2 ≤ (q * (357 / 10000)) ^ 2 := by
  have hp0 : 0 < p := by linarith
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
    _ = q ^ 2 * (2 * (181 / 462) * (1 / 10 ^ 4 * (4 * (406344 / 100000)))) := by rw [delta_q hp hq]; ring
    _ ≤ q ^ 2 * (357 / 10000) ^ 2 := mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)
    _ = (q * (357 / 10000)) ^ 2 := by ring

/-- **The collars `m ≥ 3` at `q`**: `Σ_{3 ≤ m < M} min(√C_m, C_m/(2√ΔY Θ_m))/m ≤ q·0.0116` for `M ≤ 67`. -/
theorem collar_three_le_q {p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) {K M : ℕ} (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    ∑ m ∈ Finset.Ico 3 M, min (√(collC (1 / p ^ 2) (eSh (4 / 3 * (1 / p ^ 2))) K m))
        (collC (1 / p ^ 2) (eSh (4 / 3 * (1 / p ^ 2))) K m
          / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m ≤ q * (116 / 10000) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  have hdq : 1 / p ^ 2 ≤ q * (1 / 10 ^ 4) := by
    rw [delta_q hp hq]
    have : q ^ 2 ≤ q := by simpa using q_pow_le hq0.le hq1 (show 1 ≤ 2 by norm_num)
    calc q ^ 2 / 10 ^ 4 ≤ q / 10 ^ 4 := by gcongr
      _ = q * (1 / 10 ^ 4) := by ring
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
  have hA' : A ≤ (181 / 462) * (q * (1 / 10 ^ 4)) * (1 + 24 * (1 / 10 ^ 4) / 5) ^ 2 * 95 := by
    rw [hA]; gcongr
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  calc A * ∑ m ∈ Finset.Ico 3 M, Theta m / m
      ≤ (181 / 462) * (q * (1 / 10 ^ 4)) * (1 + 24 * (1 / 10 ^ 4) / 5) ^ 2 * 95
        * (331663 / 100000 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12)) := by gcongr
    _ = q * ((181 / 462) * (1 / 10 ^ 4) * (1 + 24 * (1 / 10 ^ 4) / 5) ^ 2 * 95
        * (331663 / 100000 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12))) := by ring
    _ ≤ q * (116 / 10000) := mul_le_mul_of_nonneg_left (by norm_num) hq0.le

end top

section chirpTop

open Cvs.L2a.LocalisedBottomCorners (eSh)
open Cvs.L2a.TopCornerSum (shellSet dK collSh psiSh collC chirpC Bloc Bloc2 tC)
open Cvs.L2a.CornerSuprema (theta2Int Theta)

/-- **The `m = 2` chirp at `q`**: `(2κ/2)√B₂ ≤ q·7.9·10⁻⁴` for `3 ≤ M ≤ 67`. -/
theorem chirp_two_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) {K M : ℕ} (hK : eSh (4 / 3 * (1 / p ^ 2)) K = 1) (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    2 * √(2 * c / π) / ((2 : ℕ) : ℝ)
        * √(chirpC c J (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) (eSh (4 / 3 * (1 / p ^ 2))) K M 2)
      ≤ q * (79 / 10 ^ 5) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp2 : 10 ^ 4 ≤ p ^ 2 := by nlinarith
  have hd4 : 1 / p ^ 2 ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hp2
  have hd0 : 0 < 1 / p ^ 2 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMr : (M : ℝ) ≤ 67 := by exact_mod_cast hM
  have hsq : 4 / 3 * (1 / p ^ 2) = q ^ 2 * (4 / 3 * (1 / 10 ^ 4)) := by rw [delta_q hp hq]; ring
  set δ := 1 / p ^ 2 with hδ
  set s := 4 / 3 * δ with hs
  have hs0 : 0 < s := by positivity
  have hs4 : s * 4 ≤ 1 := by rw [hs]; linarith
  have he0 : eSh s 0 = s := eSh_zero (by linarith)
  have he2 : eSh s 2 = s * 4 := by unfold eSh; norm_num; linarith
  obtain ⟨hπ1, hπ2⟩ := pi_bounds
  set T₂ : ℝ := (11 / 10 ^ 4) ^ 2 * (1 / 3) ^ 4 + (21 / 10 ^ 6) ^ 2 * (1 / 3) ^ 2 with hT₂
  set A : ℕ → ℝ := fun k => q ^ 2 * (15 / 10 ^ 7) * (16 * π ^ 4 * ((eSh s (k + 1) ^ 3 - eSh s k ^ 3) / 3)) with hA
  set B : ℕ → ℝ := fun k => q ^ 2 * T₂ * (16 * ∫ t in shellSet (eSh s) k, theta2Int t) with hB
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
    · have hT := tT_regI_q hp hq hc hM2 (δ := dK δ (eSh s) k) (r := eSh s k / 4)
        (le_min (by rw [hδ]; gcongr; norm_num) (by rw [hs3]; linarith)) (min_le_left _ _) (by rw [hs3]; linarith)
        hJ0 hJ
      have hP := (Cvs.L2a.TopCornerSum.shell_le (δ := δ) (u := eSh s) (k := k) hd0 (by linarith) hpos
        (eSh_mono hs0.le (Nat.le_succ k)) h1).2
      simp only [hA]
      calc Cvs.L2a.LocalisedBottomCorners.tT c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k
          ≤ q ^ 2 * (15 / 10 ^ 7) * psiSh δ (eSh s) k := by gcongr
        _ ≤ _ := by gcongr
    · have hek2 : s * 4 ≤ eSh s k := by
        have := eSh_mono hs0.le (by omega : 2 ≤ k); rwa [he2] at this
      have hdk : dK δ (eSh s) k = δ := min_eq_left (by rw [hs] at hek2; linarith)
      rw [hdk]
      have hT := tT_regII_q hp hq hc hM2 (by linarith) (r := eSh s k / 4) (by rw [hs43]; linarith) hJ0 hJ
      have hu3 : 1 / (M : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hM3r
      have hT' : Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (eSh s k / 4) J ≤ q ^ 2 * T₂ := by
        refine hT.trans ?_
        rw [hT₂]; gcongr
      have hP := (collSh_psiSh_le (δ := δ) hd0.le hpos h1).2
      rw [integral_const_mul] at hP
      have hT0' := Cvs.L2a.LocalisedBottomCorners.tT_nonneg (c := c) (x₀ := M) (d := δ) (δ := δ)
        (r := eSh s k / 4) (J := J) hc0 hd0.le (by linarith) hd0.le hJ0 hr0
      have hP0' : 0 ≤ psiSh δ (eSh s) k := setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
      simp only [hB]
      calc Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (eSh s k / 4) J * psiSh δ (eSh s) k
          ≤ q ^ 2 * T₂ * psiSh δ (eSh s) k := by gcongr
        _ ≤ _ := by gcongr
  have hsum := sum_split_two hA0 hB0 hf
  have hAs : A 0 + A 1 ≤ q ^ 2 * (15 / 10 ^ 7) * (16 * π ^ 4 * ((s * 4) ^ 3 / 3)) := by
    have e : A 0 + A 1 = q ^ 2 * (15 / 10 ^ 7) * (16 * π ^ 4 * ((eSh s 2 ^ 3 - eSh s 0 ^ 3) / 3)) := by
      simp only [hA]; ring
    rw [e, he2, he0]
    have h0 : 0 ≤ s ^ 3 := by positivity
    gcongr
    linarith
  have hBs : ∑ k ∈ Finset.range K, B k ≤ q ^ 2 * T₂ * (16 * (406344 / 100000)) := by
    simp only [hB]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := shells_theta_le (u := eSh s) (K := K) (eSh_pos hs0 0) hK (eSh_mono hs0.le)
    gcongr
  have q62 : q ^ 6 ≤ q ^ 2 := q_pow_le hq0.le hq1 (by norm_num)
  have hstrip : 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c ≤ q ^ 2 * (3 / 10 ^ 11) := by
    have hsI := Cvs.L2a.TopCornerSum.stripI_le hs0 (by linarith)
    have hJc : J / c ≤ 2501 / 10000 := by
      rw [div_le_iff₀ hc0]; rw [hc] at hJ ⊢
      have : (10 : ℝ) ^ 16 ≤ p ^ 8 := by
        calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
          _ ≤ p ^ 8 := by gcongr
      nlinarith
    have h9 : (3 : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hM3r 2
    have hM8 : 8 ≤ (M : ℝ) ^ 2 - 1 := by linarith
    have e : 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c
        = 6 * (J / c) / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s := by ring
    rw [e]
    have hI0 : 0 ≤ Cvs.L2a.TopCornerSum.stripI s := setIntegral_nonneg measurableSet_Ioo fun t _ => by positivity
    have hs3 : s ^ 3 ≤ q ^ 2 * (4 / 3 * (1 / 10 ^ 4)) ^ 3 := by
      rw [hsq]
      calc (q ^ 2 * (4 / 3 * (1 / 10 ^ 4))) ^ 3 = q ^ 6 * (4 / 3 * (1 / 10 ^ 4)) ^ 3 := by ring
        _ ≤ q ^ 2 * (4 / 3 * (1 / 10 ^ 4)) ^ 3 := by gcongr
    calc 6 * (J / c) / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s
        ≤ 6 * (2501 / 10000) / 8 * (16 * π ^ 4 / 9 * (s ^ 3 / 3)) := by
          gcongr
      _ ≤ 6 * (2501 / 10000) / 8 * (16 * (31416 / 10000) ^ 4 / 9 * (q ^ 2 * (4 / 3 * (1 / 10 ^ 4)) ^ 3 / 3)) := by
          gcongr
      _ = q ^ 2 * (6 * (2501 / 10000) / 8 * (16 * (31416 / 10000) ^ 4 / 9 * ((4 / 3 * (1 / 10 ^ 4)) ^ 3 / 3))) := by
          ring
      _ ≤ q ^ 2 * (3 / 10 ^ 11) := mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)
  unfold chirpC
  rw [if_pos rfl]
  rw [show 2 * √(2 * c / π) / ((2 : ℕ) : ℝ) = √(2 * c / π) by push_cast; ring,
    ← Real.sqrt_mul (by positivity)]
  refine sqrt_le_of_le_sq (by positivity) ?_
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
  have hA' : q ^ 2 * (15 / 10 ^ 7) * (16 * π ^ 4 * ((s * 4) ^ 3 / 3))
      ≤ q ^ 2 * (15 / 10 ^ 7) * (16 * (31416 / 10000) ^ 4 * ((4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 / 3)) := by gcongr
  have htot : ∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k
      ≤ q ^ 2 * (975 / 10 ^ 9) := by
    have : q ^ 2 * (15 / 10 ^ 7) * (16 * (31416 / 10000) ^ 4 * ((4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 / 3))
        + q ^ 2 * T₂ * (16 * (406344 / 100000)) ≤ q ^ 2 * (975 / 10 ^ 9) := by
      have e : q ^ 2 * (15 / 10 ^ 7) * (16 * (31416 / 10000) ^ 4 * ((4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 / 3))
          + q ^ 2 * T₂ * (16 * (406344 / 100000)) = q ^ 2 * ((15 / 10 ^ 7) * (16 * (31416 / 10000) ^ 4
            * ((4 / 3 * (1 / 10 ^ 4) * 4) ^ 3 / 3)) + T₂ * (16 * (406344 / 100000))) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by rw [hT₂]; norm_num) (sq_nonneg q)
    linarith
  have hsum0 : 0 ≤ 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c := by
    have h9 : (3 : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hM3r 2
    have : 0 < (M : ℝ) ^ 2 - 1 := by linarith
    have hI0 : 0 ≤ Cvs.L2a.TopCornerSum.stripI s := setIntegral_nonneg measurableSet_Ioo fun t _ => by positivity
    positivity
  calc 2 / π * (∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k)
        + 2 / π * (6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c)
      = 2 / π * ((∑ k ∈ Finset.range K, tC c M δ (dK δ (eSh s) k) (eSh s k / 4) J * psiSh δ (eSh s) k)
        + 6 * J / ((M : ℝ) ^ 2 - 1) * Cvs.L2a.TopCornerSum.stripI s / c) := by ring
    _ ≤ 2 / π * (q ^ 2 * (975 / 10 ^ 9) + q ^ 2 * (3 / 10 ^ 11)) :=
        mul_le_mul_of_nonneg_left (add_le_add htot hstrip) (by positivity)
    _ ≤ 2 / (31415 / 10000) * (q ^ 2 * (975 / 10 ^ 9) + q ^ 2 * (3 / 10 ^ 11)) :=
        mul_le_mul_of_nonneg_right h2π (by positivity)
    _ = q ^ 2 * (2 / (31415 / 10000) * (975 / 10 ^ 9 + 3 / 10 ^ 11)) := by ring
    _ ≤ q ^ 2 * (79 / 10 ^ 5) ^ 2 := mul_le_mul_of_nonneg_left (by norm_num) (sq_nonneg q)
    _ = (q * (79 / 10 ^ 5)) ^ 2 := by ring

/-- **The chirps `m ≥ 3` at `q`**: `Σ_{3 ≤ m < M}(2κ/m)√B_m ≤ q·7.82·10⁻⁴` for `M ≤ 67`. -/
theorem chirp_three_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) {K M : ℕ} (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    ∑ m ∈ Finset.Ico 3 M, 2 * √(2 * c / π) / m
        * √(chirpC c J (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) (eSh (4 / 3 * (1 / p ^ 2))) K M m)
      ≤ q * (782 / 10 ^ 6) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
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
      ≤ q * (2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4))) * (1 / ((m : ℝ) - 2)) := fun m hm => by
    have hm3 : 3 ≤ m := (Finset.mem_Ico.1 hm).1
    have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hm0 : (0 : ℝ) < m := by linarith
    unfold chirpC
    rw [if_neg (by omega)]
    have hr0 : 0 < 1 - δ - 2 / (m : ℝ) := by
      have : 2 / (m : ℝ) ≤ 2 / 3 := by gcongr
      linarith
    have hT := tT_regII_q (x₀ := (M : ℝ)) hp hq hc (by linarith) (by linarith) (r := 1 - δ - 2 / (m : ℝ)) (by
      have : 2 / (m : ℝ) ≤ 2 / 3 := by gcongr
      have : 4 / 3 / p ^ 2 = 4 / 3 * δ := by rw [hδ]; ring
      linarith) hJ0 hJ
    have hT' : Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J ≤ q ^ 2 * T₂ := by
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
        * Cvs.L2a.TopCornerSum.PsiD δ m / c) ≤ (q * (82 / 10 ^ 6) / (1 - δ - 2 / (m : ℝ))) ^ 2 := by
      have e : 2 * c / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
          * Cvs.L2a.TopCornerSum.PsiD δ m / c)
          = 2 / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J * Cvs.L2a.TopCornerSum.PsiD δ m) := by
        field_simp
      rw [e]
      have h2π : 2 / π ≤ 2 / (31415 / 10000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ1
      calc 2 / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J * Cvs.L2a.TopCornerSum.PsiD δ m)
          ≤ 2 / (31415 / 10000) * (q ^ 2 * T₂ * (11 / 16 / (1 - δ - 2 / (m : ℝ)) ^ 2)) := by gcongr
        _ = q ^ 2 * (2 / (31415 / 10000) * T₂ * (11 / 16)) / (1 - δ - 2 / (m : ℝ)) ^ 2 := by ring
        _ ≤ q ^ 2 * (82 / 10 ^ 6) ^ 2 / (1 - δ - 2 / (m : ℝ)) ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by rw [hT₂]; norm_num) (sq_nonneg q))
              (sq_nonneg _)
        _ = (q * (82 / 10 ^ 6) / (1 - δ - 2 / (m : ℝ))) ^ 2 := by rw [div_pow (q * (82 / 10 ^ 6)), mul_pow]
    have hsq := sqrt_le_of_le_sq (by positivity) hin
    have hden : (1 - 3 * (1 / 10 ^ 4)) * ((m : ℝ) - 2) ≤ m * (1 - δ - 2 / (m : ℝ)) := by
      have hq' : (m : ℝ) * (2 / m) = 2 := by field_simp
      nlinarith [hq']
    calc 2 / (m : ℝ) * √(2 * c / π * (Cvs.L2a.LocalisedBottomCorners.tT c M δ δ (1 - δ - 2 / (m : ℝ)) J
          * Cvs.L2a.TopCornerSum.PsiD δ m / c))
        ≤ 2 / m * (q * (82 / 10 ^ 6) / (1 - δ - 2 / (m : ℝ))) := by gcongr
      _ = q * (2 * (82 / 10 ^ 6) / (m * (1 - δ - 2 / (m : ℝ)))) := by field_simp
      _ ≤ q * (2 * (82 / 10 ^ 6) / ((1 - 3 * (1 / 10 ^ 4)) * ((m : ℝ) - 2))) := by
          gcongr
          have : 0 < (m : ℝ) - 2 := by linarith
          positivity
      _ = q * (2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4))) * (1 / ((m : ℝ) - 2)) := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, sum_inv_sub_two]
  have h65 := harmonic_le_of_le (show M - 3 ≤ 65 by omega)
  obtain ⟨H65, -⟩ := Cvs.L2a.LocalisedConstants.harmonic_65_69
  calc q * (2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4))) * (harmonic (M - 3) : ℝ)
      ≤ q * (2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4))) * (47593 / 10000) := by gcongr; linarith
    _ = q * (2 * (82 / 10 ^ 6) / (1 - 3 * (1 / 10 ^ 4)) * (47593 / 10000)) := by ring
    _ ≤ q * (782 / 10 ^ 6) := mul_le_mul_of_nonneg_left (by norm_num) hq0.le

end chirpTop

/-! ### `resLoc ≤ 7c^{−1/8}` -/

section assemble

open Cvs.L2a.LocalisedBottomCorners (eSh)
open Cvs.L2a.TopCornerSum (collC chirpC)
open Cvs.L2a.CornerSuprema (Theta)

/-- `KcoBar ≤ q·10⁻¹⁰` at `c = p⁸`, `0 ≤ J ≤ c/4 + 1`. -/
theorem KcoBar_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.TopCornerSum.KcoBar c J ≤ q * (1 / 10 ^ 10) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc16 : 10 ^ 16 ≤ c := by rw [hc]; exact hp8
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  obtain ⟨hk0, hk1⟩ := Cvs.L2a.LocalisedConstants.kappaI_mem (J := J) (c := c) (by linarith) hJ0 hJ
  have hkap : Cvs.L2a.TopCornerSum.kapI c J = Cvs.L2a.LocalisedConstants.kappaI J c := rfl
  have hs1 : √(Cvs.L2a.TopCornerSum.kapI c J) ≤ 1 := by
    rw [hkap, Real.sqrt_le_one]; exact hk1
  have h8 : 28 / 10 ≤ √8 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hπ : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have q81 : q ^ 8 ≤ q := by simpa using q_pow_le hq0.le hq1 (show 1 ≤ 8 by norm_num)
  unfold Cvs.L2a.TopCornerSum.KcoBar
  calc 29 * π ^ 2 / (3 * √8) * √(Cvs.L2a.TopCornerSum.kapI c J) / c
      ≤ 29 * 10 / (3 * (28 / 10)) * 1 / c := by gcongr
    _ = 29 * 10 / (3 * (28 / 10)) / p ^ 8 := by rw [hc]; ring
    _ = 29 * 10 / (3 * (28 / 10)) * q ^ 8 / 100 ^ 8 := div_pow_q hp hq 8
    _ ≤ 29 * 10 / (3 * (28 / 10)) * q / 100 ^ 8 := by gcongr
    _ = q * (29 * 10 / (3 * (28 / 10)) / 100 ^ 8) := by ring
    _ ≤ q * (1 / 10 ^ 10) := mul_le_mul_of_nonneg_left (by norm_num) hq0.le

/-- **`remT ≤ (15/1000)q`** for `3 ≤ M ≤ 67` at `δ = d = 1/p²`, `s = (4/3)/p²`, dyadic shells. -/
theorem remT_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hc : c = p ^ 8) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) {K M : ℕ} (hK : eSh (4 / 3 * (1 / p ^ 2)) K = 1) (hM3 : 3 ≤ M) (hM : M ≤ 67) :
    Cvs.L2a.TopCornerSum.remT c J (1 / p ^ 2) (1 / p ^ 2) (4 / 3 * (1 / p ^ 2)) (eSh (4 / 3 * (1 / p ^ 2))) K M
      ≤ q * (15 / 1000) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc16 : 10 ^ 16 ≤ c := by rw [hc]; exact hp8
  have hc0 : 0 < c := by linarith
  have hcorr := Cvs.L2a.TopCornerSum.sum_corrC_le hc0 hJ0 hM3
  have hKco := KcoBar_le_q hp hq hc hJ0 hJ
  set δ := 1 / p ^ 2 with hδ
  set s := 4 / 3 * δ with hs
  have hcoll : ∑ m ∈ Finset.Ico 2 M, min (√(collC δ (eSh s) K m))
      (collC δ (eSh s) K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m
      ≤ q * (357 / 10000) / 2 + q * (116 / 10000) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < M), show (2 : ℕ) + 1 = 3 from rfl]
    have h3 := collar_three_le_q (K := K) hp hq hM3 hM
    have h2 : min (√(collC δ (eSh s) K 2))
        (collC δ (eSh s) K 2 / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta ((2 : ℕ) : ℝ)))) / ((2 : ℕ) : ℝ)
        ≤ q * (357 / 10000) / 2 := by
      push_cast
      refine div_le_div_of_nonneg_right ((min_le_left _ _).trans ?_) (by norm_num)
      exact sqrt_le_of_le_sq (by positivity) (collC_two_le_q hp hq hK)
    linarith
  have hchirp : ∑ m ∈ Finset.Ico 2 M, 2 * √(2 * c / π) / m * √(chirpC c J δ δ s (eSh s) K M m)
      ≤ q * (79 / 10 ^ 5) + q * (782 / 10 ^ 6) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < M), show (2 : ℕ) + 1 = 3 from rfl]
    have h2 := chirp_two_le_q hp hq hc hJ0 hJ hK hM3 hM
    have h3 := chirp_three_le_q (K := K) hp hq hc hJ0 hJ hM3 hM
    linarith
  unfold Cvs.L2a.TopCornerSum.remT
  rw [Cvs.L2a.TopCornerSum.Icc_eq_Ico (by omega)] at hcorr ⊢
  have h2 : √2 ≤ 141422 / 100000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hπ := pi_bounds.1
  have hsπ : √2 / π ≤ 141422 / 100000 / (31415 / 10000) := div_le_div₀ (by norm_num) h2 (by norm_num) hπ
  have hcoll0 : (0 : ℝ) ≤ q * (357 / 10000) / 2 + q * (116 / 10000) := by positivity
  have : √2 / π * ∑ m ∈ Finset.Ico 2 M, min (√(collC δ (eSh s) K m))
      (collC δ (eSh s) K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M) * Theta m))) / m
      ≤ 141422 / 100000 / (31415 / 10000) * (q * (357 / 10000) / 2 + q * (116 / 10000)) := by
    calc _ ≤ √2 / π * (q * (357 / 10000) / 2 + q * (116 / 10000)) :=
          mul_le_mul_of_nonneg_left hcoll (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsπ hcoll0
  norm_num at this hchirp hKco ⊢
  linarith

/-- **`ρ_t ≤ (15/1000)q`** at `S*`, `X_t = 68`, with `δ(c) = 1/p²`, `c = p⁸`, `q = 100/p`. -/
theorem rhoTL_le_q {c J p q : ℝ} (hp : 100 ≤ p) (hq : q = 100 / p) (hδ : Cvs.L2a.TopCornerSum.deltaS c = 1 / p ^ 2)
    (hcp : c = p ^ 8) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Cvs.L2a.FrameFloorIntegerM.rhoTL c J ≤ q * (15 / 1000) := by
  obtain ⟨hq0, hq1⟩ := q_mem hp hq
  have hp8 : 10 ^ 16 ≤ p ^ 8 := by
    calc (10 : ℝ) ^ 16 = 100 ^ 8 := by norm_num
      _ ≤ p ^ 8 := by gcongr
  have hc : 10 ^ 16 ≤ c := by rw [hcp]; exact hp8
  have hs : Cvs.L2a.TopCornerSum.sS c = 4 / 3 * (1 / p ^ 2) := by unfold Cvs.L2a.TopCornerSum.sS; rw [hδ]
  have hu : Cvs.L2a.TopCornerSum.uS c = Cvs.L2a.LocalisedBottomCorners.eSh (Cvs.L2a.TopCornerSum.sS c) := rfl
  have hK : Cvs.L2a.LocalisedBottomCorners.eSh (4 / 3 * (1 / p ^ 2)) (Cvs.L2a.TopCornerSum.KS c) = 1 := by
    rw [← hs, ← hu]; exact Cvs.L2a.TopCornerSum.uS_K (le_trans (by norm_num) hc)
  unfold Cvs.L2a.FrameFloorIntegerM.rhoTL Cvs.L2a.TopCornerSum.rhoT
  rw [hu, hs, hδ]
  refine max_le ((KcoBar_le_q hp hq hcp hJ0 hJ).trans (mul_le_mul_of_nonneg_left (by norm_num) hq0.le))
    (supBelow_le (by positivity) fun M hM => ?_)
  obtain ⟨hM3, hM68⟩ := Finset.mem_Ico.1 hM
  exact remT_le_q hp hq hcp hJ0 hJ hK hM3 (by omega)

/-- `c^{−1/8} = 1/p` at `c = p⁸`, `p > 0`. -/
theorem rpow_neg_eighth {c p : ℝ} (hp0 : 0 < p) (hc : c = p ^ 8) : c ^ (-(1 / 8 : ℝ)) = 1 / p := by
  rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  norm_num
  rw [Real.rpow_neg_one]

/-- **`resLoc ≤ 5.6c^{−1/8}`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1` and every integer `M ≥ 3`. -/
theorem resLoc_le_decay_sharp {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {M : ℕ}
    (hM : 3 ≤ M) :
    Cvs.L2a.FrameFloorIntegerM.resLoc c J M ≤ 28 / 5 * c ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨p, hp, hδ, hcp⟩ := scale_p hc
  have hp0 : 0 < p := by linarith
  have h1 := resB_le_q hp rfl hδ hcp hJ0 hJ hM
  have h2 := rhoTL_le_q hp rfl hδ hcp hJ0 hJ
  rw [rpow_neg_eighth hp0 hcp]
  unfold Cvs.L2a.FrameFloorIntegerM.resLoc
  have e : 100 / p * (41 / 1000) + 100 / p * (15 / 1000) = 28 / 5 * (1 / p) := by field_simp; norm_num
  linarith

/-- **`resLoc ≤ 7c^{−1/8}`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1` and every integer `M ≥ 3`; `7/100` at `c = 10¹⁶`. -/
theorem resLoc_le_decay {c J : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) {M : ℕ} (hM : 3 ≤ M) :
    Cvs.L2a.FrameFloorIntegerM.resLoc c J M ≤ 7 * c ^ (-(1 / 8 : ℝ)) := by
  have h := resLoc_le_decay_sharp hc hJ0 hJ hM
  have h0 : 0 ≤ c ^ (-(1 / 8 : ℝ)) := Real.rpow_nonneg (by linarith) _
  linarith

end assemble

/-! ### The full-span chain at `ρ = 7c₁^{−1/8}` -/

section chain

open Cvs.L2a.AngularProlateTailPositive (psi)

variable {ι : Type} [Fintype ι]

end chain

end Cvs.L2a.LocalResidualDecay
