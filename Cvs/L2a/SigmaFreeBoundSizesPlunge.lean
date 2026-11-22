import Mathlib
import Cvs.L2a.ModeTailNormLowerSigmaFree
import Cvs.L2a.ModeTailTerminalSigmaFree
import Cvs.L2a.SigmaFreeWeightedPairTotal

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sizes of the `σ`-free bounds toward the plunge, in `t = c^{1/40}` and `ρ = L^{1/4}`

With `c = t⁴⁰`, `(c² − χ)/c² = ρ⁴`, `0 < ρ ≤ 1`, `t¹⁰ρ ≥ 1` (`cL ≥ 1`): at `s = t¹⁶/ρ²`, `c X̄ ≤ C_n/t`; at
`s = t²⁰/ρ²`, the prime bound is at most `G P_c/c`; at `η_p = t^{−30}`, the pole bound is at most `G Q_c/(c t²⁰)`; at
`η = 1/c`, `T = t⁴`, `t⁹ρ ≥ 1`, the Mellin bound is at most `√G B_m/t²⁴`; `C_n`, `P_c`, `Q_c`, `B_m` depend on `K` only.
-/

namespace Cvs.L2a.SigmaFreeBoundSizesPlunge

open Real
open Cvs.L2a.SigmaFreeWeightedPairTotal (κ₁)

variable {χ K t ρ : ℝ}

theorem sqrt_c : √(t ^ 40) = t ^ 20 := by
  rw [show t ^ 40 = (t ^ 20) ^ 2 by ring, sqrt_sq (by positivity)]

theorem A_eq : √(4 * K / (3 * t ^ 40)) = √(4 * K / 3) / t ^ 20 := by
  rw [show 4 * K / (3 * t ^ 40) = (4 * K / 3) / (t ^ 20) ^ 2 by ring, sqrt_div' _ (by positivity),
    sqrt_sq (by positivity)]

/-- `1/ρ² ≤ t²⁰`. -/
theorem inv_rho_sq_le' (hρ0 : 0 < ρ) (hρt : 1 ≤ t ^ 10 * ρ) : 1 / ρ ^ 2 ≤ t ^ 20 := by
  rw [div_le_iff₀ (by positivity)]
  have := pow_le_pow_left₀ zero_le_one hρt 2
  nlinarith

/-- The norm constant. -/
noncomputable def Cn (K : ℝ) : ℝ :=
  23 * √(4 * K / 3) * √10 + 17 * (√(4 * K / 3) + 2 * √(10 / 3)) + (κ₁ + 64 * √2 / 27) * (π ^ 2 / 6)
    + 32 * √3 / 9 * √(23 / 3) * 3

set_option maxHeartbeats 1000000 in
/-- **The first-mode cross terms at `s = t¹⁶/ρ²`**: `c X̄ ≤ C_n/t`. -/
theorem c_mul_Xbar_le (ht : 1 ≤ t) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρt : 1 ≤ t ^ 10 * ρ)
    (hL : ((t ^ 40) ^ 2 - χ) / (t ^ 40) ^ 2 = ρ ^ 4) :
    t ^ 40 * Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar (t ^ 40) χ K (t ^ 16 / ρ ^ 2) ≤ Cn K / t := by
  have ht0 : 0 < t := by linarith
  unfold Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar
  rw [hL, A_eq, sqrt_c]
  set a := √(4 * K / 3) with ha
  set q := √(10 / 3) with hq
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have hq0 : 0 ≤ q := sqrt_nonneg _
  have hκ : 0 ≤ κ₁ := by unfold κ₁; positivity
  have e1 : √(6 / (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4))) = √10 / (t ^ 8 * ρ) := by
    rw [show 6 / (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) = 10 / (t ^ 8 * ρ) ^ 2 by field_simp; ring,
      sqrt_div' _ (by positivity), sqrt_sq (by positivity)]
  have e2 : √(10 / (3 * ρ ^ 4)) = q / ρ ^ 2 := by
    rw [show 10 / (3 * ρ ^ 4) = (10 / 3) / (ρ ^ 2) ^ 2 by ring, sqrt_div' _ (by positivity),
      sqrt_sq (by positivity)]
  have e3 : √(t ^ 16 / ρ ^ 2) = t ^ 8 / ρ := by
    rw [show t ^ 16 / ρ ^ 2 = (t ^ 8 / ρ) ^ 2 by ring, sqrt_sq (by positivity)]
  rw [e1, e2, e3]
  have ht4 : t ≤ t ^ 4 := le_self_pow₀ ht (by norm_num)
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1
  have hir := inv_rho_sq_le' hρ0 hρt
  -- the log
  have hlog : 1 + log (max (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) 1) ≤ 17 * t := by
    have h1 : max (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) 1 ≤ t ^ 16 := by
      apply max_le
      · have e : t ^ 16 / ρ ^ 2 * ρ ^ 4 = t ^ 16 * ρ ^ 2 := by field_simp
        rw [e]; nlinarith [pow_pos ht0 16]
      · exact one_le_pow₀ ht
    have h2 := log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) h1
    rw [log_pow] at h2
    have h3 := log_le_sub_one_of_pos ht0
    push_cast at h2
    nlinarith
  have hlog0 : 0 ≤ 1 + log (max (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) 1) := by
    have := log_nonneg (le_max_right (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) 1); linarith
  rw [mul_add, mul_add, mul_add]
  -- term 1
  have T1 : t ^ 40 * (23 / 3 * (a / t ^ 20) / (t ^ 16 / ρ ^ 2) * (3 * (√10 / (t ^ 8 * ρ))))
      ≤ 23 * a * √10 / t := by
    have e : t ^ 40 * (23 / 3 * (a / t ^ 20) / (t ^ 16 / ρ ^ 2) * (3 * (√10 / (t ^ 8 * ρ))))
        = 23 * a * √10 * ρ / t ^ 4 := by field_simp
    rw [e]
    exact div_le_div₀ (by positivity) (mul_le_of_le_one_right (by positivity) hρ1) ht0 ht4
  -- term 2
  have T2 : t ^ 40 * ((a / t ^ 20 / t ^ 40 + 2 * (q / ρ ^ 2) / (t ^ 40 * (t ^ 16 / ρ ^ 2)))
        * (1 + log (max (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) 1)))
      ≤ 17 * (a + 2 * q) / t := by
    have e : t ^ 40 * (a / t ^ 20 / t ^ 40 + 2 * (q / ρ ^ 2) / (t ^ 40 * (t ^ 16 / ρ ^ 2)))
        = a / t ^ 20 + 2 * q / t ^ 16 := by field_simp
    rw [← mul_assoc, e]
    have h1 : a / t ^ 20 + 2 * q / t ^ 16 ≤ (a + 2 * q) / t ^ 16 := by
      have : a / t ^ 20 ≤ a / t ^ 16 :=
        div_le_div_of_nonneg_left ha0 (by positivity) (pow_le_pow_right₀ ht (by norm_num))
      rw [add_div]; linarith
    calc (a / t ^ 20 + 2 * q / t ^ 16) * (1 + log (max (3 / 5 * (t ^ 16 / ρ ^ 2 * ρ ^ 4)) 1))
        ≤ (a + 2 * q) / t ^ 16 * (17 * t) := mul_le_mul h1 hlog hlog0 (by positivity)
      _ = 17 * (a + 2 * q) / t ^ 15 := by field_simp
      _ ≤ 17 * (a + 2 * q) / t :=
          div_le_div_of_nonneg_left (by positivity) ht0 (le_self_pow₀ ht (by norm_num))
  -- term 3
  have T3 : t ^ 40 * ((κ₁ * (t ^ 16 / ρ ^ 2) / (t ^ 40) ^ 2
        + 64 * √2 / 27 * ρ ^ 4 * (t ^ 16 / ρ ^ 2) * t ^ 20 / (t ^ 40) ^ 2) * (π ^ 2 / 6))
      ≤ (κ₁ + 64 * √2 / 27) * (π ^ 2 / 6) / t := by
    have e : t ^ 40 * ((κ₁ * (t ^ 16 / ρ ^ 2) / (t ^ 40) ^ 2
        + 64 * √2 / 27 * ρ ^ 4 * (t ^ 16 / ρ ^ 2) * t ^ 20 / (t ^ 40) ^ 2) * (π ^ 2 / 6))
        = (κ₁ * (1 / ρ ^ 2) / t ^ 24 + 64 * √2 / 27 * ρ ^ 2 / t ^ 4) * (π ^ 2 / 6) := by
      field_simp
    rw [e]
    have h1 : κ₁ * (1 / ρ ^ 2) / t ^ 24 ≤ κ₁ / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]
      have : t ^ 20 * t ≤ t ^ 24 := by
        rw [← pow_succ]; exact pow_le_pow_right₀ ht (by norm_num)
      calc κ₁ * (1 / ρ ^ 2) * t ≤ κ₁ * t ^ 20 * t := by gcongr
        _ ≤ κ₁ * t ^ 24 := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this hκ
    have h2 : 64 * √2 / 27 * ρ ^ 2 / t ^ 4 ≤ 64 * √2 / 27 / t :=
      div_le_div₀ (by positivity) (mul_le_of_le_one_right (by positivity) hρ2) ht0 ht4
    have hp : 0 ≤ π ^ 2 / 6 := by positivity
    have := add_le_add (mul_le_mul_of_nonneg_right h1 hp) (mul_le_mul_of_nonneg_right h2 hp)
    calc (κ₁ * (1 / ρ ^ 2) / t ^ 24 + 64 * √2 / 27 * ρ ^ 2 / t ^ 4) * (π ^ 2 / 6)
        ≤ κ₁ / t * (π ^ 2 / 6) + 64 * √2 / 27 / t * (π ^ 2 / 6) := by rw [add_mul]; exact this
      _ = (κ₁ + 64 * √2 / 27) * (π ^ 2 / 6) / t := by ring
  -- term 4
  have T4 : t ^ 40 * (32 * √3 / 9 * √(23 / 3) * (t ^ 8 / ρ) / (t ^ 40) ^ 2 * 3)
      ≤ 32 * √3 / 9 * √(23 / 3) * 3 / t := by
    have e : t ^ 40 * (32 * √3 / 9 * √(23 / 3) * (t ^ 8 / ρ) / (t ^ 40) ^ 2 * 3)
        = 32 * √3 / 9 * √(23 / 3) * 3 * (t ^ 8 / (ρ * t ^ 40)) := by field_simp
    rw [e, div_eq_mul_one_div (32 * √3 / 9 * √(23 / 3) * 3) t]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_div_iff₀ (by positivity) ht0, one_mul]
    have h1 : t ^ 9 ≤ ρ * t ^ 40 := by
      have : t ^ 40 = t ^ 10 * t ^ 30 := by ring
      rw [this]
      have h30 : t ^ 9 ≤ t ^ 30 := pow_le_pow_right₀ ht (by norm_num)
      nlinarith [pow_pos ht0 10, pow_pos ht0 30]
    calc t ^ 8 * t = t ^ 9 := by ring
      _ ≤ ρ * t ^ 40 := h1
  unfold Cn
  rw [← ha, ← hq]
  have e : (23 * a * √10 + 17 * (a + 2 * q) + (κ₁ + 64 * √2 / 27) * (π ^ 2 / 6) + 32 * √3 / 9 * √(23 / 3) * 3) / t
      = 23 * a * √10 / t + 17 * (a + 2 * q) / t + (κ₁ + 64 * √2 / 27) * (π ^ 2 / 6) / t
        + 32 * √3 / 9 * √(23 / 3) * 3 / t := by ring
  rw [e]
  linarith

/-- The prime constant. -/
noncomputable def Pc (K : ℝ) : ℝ :=
  2 * ((23 / 3 * √(4 * K / 3) + κ₁ + 64 * √2 / 27) * (π ^ 2 / 6)
        * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
      + 3 * (32 * √3 / 9 * √(23 / 3)) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n)
      + 8820 * (√(4 * K / 3) + 2 * √(10 / 3))
      + 4 / 3 * (π ^ 2 / 6) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
      + 8 * (2 / √3) * (36 * (π ^ 2 / 6 + 6)))

set_option maxHeartbeats 1000000 in
/-- **The prime bound at `s = t²⁰/ρ²`** is at most `G P_c/c`. -/
theorem primeBound_le {G : ℝ} (hG : 0 ≤ G) (ht : 1 ≤ t) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρt : 1 ≤ t ^ 10 * ρ)
    (hL : ((t ^ 40) ^ 2 - χ) / (t ^ 40) ^ 2 = ρ ^ 4) :
    Cvs.L2a.ModeTailTerminalSigmaFree.primeBound (t ^ 40) χ G K (t ^ 20 / ρ ^ 2) ≤ G * Pc K / t ^ 40 := by
  have ht0 : 0 < t := by linarith
  set a := √(4 * K / 3) with ha
  set q := √(10 / 3) with hq
  have ha0 : 0 ≤ a := sqrt_nonneg _
  have hq0 : 0 ≤ q := sqrt_nonneg _
  have hκ : 0 ≤ κ₁ := by unfold κ₁; positivity
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1
  have hir := inv_rho_sq_le' hρ0 hρt
  have hρ40 : t ^ 30 ≤ ρ * t ^ 40 := by
    have : t ^ 40 = t ^ 10 * t ^ 30 := by ring
    rw [this]; nlinarith [pow_pos ht0 30]
  -- the three coefficients, times `c`
  have hC1 : t ^ 40 * Cvs.L2a.SigmaFreeWeightedPairTotal.C1 (t ^ 40) χ K (t ^ 20 / ρ ^ 2) ≤ 23 / 3 * a + κ₁ + 64 * √2 / 27 := by
    unfold Cvs.L2a.SigmaFreeWeightedPairTotal.C1
    rw [hL, A_eq, sqrt_c, ← ha]
    have e : t ^ 40 * (23 / 3 * (a / t ^ 20) / (t ^ 20 / ρ ^ 2) + κ₁ * (t ^ 20 / ρ ^ 2) / (t ^ 40) ^ 2
        + 64 * √2 / 27 * ρ ^ 4 * (t ^ 20 / ρ ^ 2) * t ^ 20 / (t ^ 40) ^ 2)
        = 23 / 3 * a * ρ ^ 2 + κ₁ * (1 / ρ ^ 2 / t ^ 20) + 64 * √2 / 27 * ρ ^ 2 := by field_simp
    rw [e]
    have h1 : 1 / ρ ^ 2 / t ^ 20 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hir.trans (pow_le_pow_right₀ ht (by norm_num))
    have := mul_le_of_le_one_right ha0 hρ2
    have := mul_le_of_le_one_right hκ h1
    have := mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 64 * √2 / 27) hρ2
    nlinarith
  have hC3 : t ^ 40 * Cvs.L2a.SigmaFreeWeightedPairTotal.C3 (t ^ 40) (t ^ 20 / ρ ^ 2) ≤ 32 * √3 / 9 * √(23 / 3) := by
    unfold Cvs.L2a.SigmaFreeWeightedPairTotal.C3
    have e3 : √(t ^ 20 / ρ ^ 2) = t ^ 10 / ρ := by
      rw [show t ^ 20 / ρ ^ 2 = (t ^ 10 / ρ) ^ 2 by ring, sqrt_sq (by positivity)]
    rw [e3]
    have e : t ^ 40 * (32 * √3 / 9 * √(23 / 3) * (t ^ 10 / ρ) / (t ^ 40) ^ 2)
        = 32 * √3 / 9 * √(23 / 3) * (t ^ 10 / (ρ * t ^ 40)) := by field_simp
    rw [e]
    apply mul_le_of_le_one_right (by positivity)
    rw [div_le_one (by positivity)]
    exact (pow_le_pow_right₀ ht (by norm_num)).trans hρ40
  set sp := Cvs.L2a.SigmaFreeWeightedPairTotal.sp (t ^ 40) χ (t ^ 20 / ρ ^ 2) with hsp
  have hsp1 : 1 ≤ sp := le_max_right _ _
  have hlsp : Real.log sp ≤ 20 * t := by
    have h1 : sp ≤ t ^ 20 := by
      rw [hsp]; unfold Cvs.L2a.SigmaFreeWeightedPairTotal.sp; rw [hL]
      apply max_le
      · have e : t ^ 20 / ρ ^ 2 * ρ ^ 4 = t ^ 20 * ρ ^ 2 := by field_simp
        rw [e]; nlinarith [pow_pos ht0 20]
      · exact one_le_pow₀ ht
    have h2 := log_le_log (by linarith) h1
    rw [log_pow] at h2
    have h3 := log_le_sub_one_of_pos ht0
    push_cast at h2
    nlinarith
  have hlsp0 : 0 ≤ Real.log sp := log_nonneg hsp1
  have hHc : t ^ 40 * Cvs.L2a.SigmaFreeWeightedPairTotal.Hc (t ^ 40) χ K (t ^ 20 / ρ ^ 2)
        * (Real.log sp * (1 + Real.log sp) ^ 2) ≤ 8820 * (a + 2 * q) := by
    unfold Cvs.L2a.SigmaFreeWeightedPairTotal.Hc
    rw [hL, A_eq, ← ha]
    have e2 : √(10 / (3 * ρ ^ 4)) = q / ρ ^ 2 := by
      rw [show 10 / (3 * ρ ^ 4) = (10 / 3) / (ρ ^ 2) ^ 2 by ring, sqrt_div' _ (by positivity),
        sqrt_sq (by positivity)]
    rw [e2]
    have e : t ^ 40 * (a / t ^ 20 / t ^ 40 + 2 * (q / ρ ^ 2) / (t ^ 40 * (t ^ 20 / ρ ^ 2)))
        = (a + 2 * q) / t ^ 20 := by field_simp
    rw [e]
    have hl : Real.log sp * (1 + Real.log sp) ^ 2 ≤ 8820 * t ^ 20 := by
      have h1 : Real.log sp * (1 + Real.log sp) ^ 2 ≤ 20 * t * (1 + 20 * t) ^ 2 := by
        apply mul_le_mul hlsp (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity) (by positivity)
      have h2 : 20 * t * (1 + 20 * t) ^ 2 ≤ 8820 * t ^ 3 := by
        have : (1 + 20 * t) ^ 2 ≤ (21 * t) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        nlinarith
      have h3 : t ^ 3 ≤ t ^ 20 := pow_le_pow_right₀ ht (by norm_num)
      linarith
    calc (a + 2 * q) / t ^ 20 * (Real.log sp * (1 + Real.log sp) ^ 2)
        ≤ (a + 2 * q) / t ^ 20 * (8820 * t ^ 20) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = 8820 * (a + 2 * q) := by field_simp
  -- assemble
  set S2 := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 with hS2
  set S3 := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n) with hS3
  have hS20 : 0 ≤ S2 := tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hS30 : 0 ≤ S3 := tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  set C1 := Cvs.L2a.SigmaFreeWeightedPairTotal.C1 (t ^ 40) χ K (t ^ 20 / ρ ^ 2) with hC1d
  set C3 := Cvs.L2a.SigmaFreeWeightedPairTotal.C3 (t ^ 40) (t ^ 20 / ρ ^ 2) with hC3d
  set Hc := Cvs.L2a.SigmaFreeWeightedPairTotal.Hc (t ^ 40) χ K (t ^ 20 / ρ ^ 2) with hHcd
  set lg := Real.log sp * (1 + Real.log sp) ^ 2 with hlg
  have hX : t ^ 40 * Cvs.L2a.ModeTailTerminalSigmaFree.primeBound (t ^ 40) χ G K (t ^ 20 / ρ ^ 2)
      = 2 * (G * ((t ^ 40 * C1) * (π ^ 2 / 6) * S2 + 3 * (t ^ 40 * C3) * S3 + t ^ 40 * Hc * lg)
        + G * (4 / 3) * (π ^ 2 / 6) * S2 + 8 * G * (2 / √3) / t ^ 40 * (36 * (π ^ 2 / 6 + 6))) := by
    unfold Cvs.L2a.ModeTailTerminalSigmaFree.primeBound
    rw [← hsp, ← hC1d, ← hC3d, ← hHcd, ← hS2, ← hS3, ← hlg]
    field_simp
  rw [le_div_iff₀ (by positivity), mul_comm, hX]
  have hd : 8 * G * (2 / √3) / t ^ 40 ≤ 8 * G * (2 / √3) :=
    div_le_self (by positivity) (one_le_pow₀ ht)
  have hp : 0 ≤ π ^ 2 / 6 := by positivity
  have k1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hp) hS20
  have k3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC3 (by norm_num : (0 : ℝ) ≤ 3)) hS30
  have hin : (t ^ 40 * C1) * (π ^ 2 / 6) * S2 + 3 * (t ^ 40 * C3) * S3 + t ^ 40 * Hc * lg
      ≤ (23 / 3 * a + κ₁ + 64 * √2 / 27) * (π ^ 2 / 6) * S2 + 3 * (32 * √3 / 9 * √(23 / 3)) * S3
        + 8820 * (a + 2 * q) := by linarith
  have hG1 := mul_le_mul_of_nonneg_left hin hG
  have hd2 := mul_le_mul_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ 36 * (π ^ 2 / 6 + 6))
  unfold Pc
  rw [← ha, ← hq, ← hS2, ← hS3]
  nlinarith

/-- The pole constant. -/
noncomputable def Qc (K : ℝ) : ℝ := 2 * (√K + 4 + 56 / 9 * (π ^ 2 / 6)) * (√K + 5 + 16 / 3 * (π ^ 2 / 6))

/-- **One pole factor at `η_p = t^{−30}`**: `η_p|ψ(1)| + k√(cG)(1+η_p)/(c²((1+η_p)²−1)) + m√(cG)/c² ≤ √G(√K + k + m)/t³⁰`. -/
theorem pole_factor_le {G ψ1 k m : ℝ} (hG : 0 ≤ G) (ht : 1 ≤ t) (hk : 0 ≤ k) (hm : 0 ≤ m)
    (hψ1 : ψ1 ^ 2 ≤ K * G) :
    1 / t ^ 30 * |ψ1| + k * √(t ^ 40 * G) * (1 + 1 / t ^ 30) / ((t ^ 40) ^ 2 * ((1 + 1 / t ^ 30) ^ 2 - 1))
        + m * √(t ^ 40 * G) / (t ^ 40) ^ 2
      ≤ √G * (√K + k + m) / t ^ 30 := by
  have ht0 : 0 < t := by linarith
  have hK : 0 ≤ K * G := le_trans (sq_nonneg _) hψ1
  have habs : |ψ1| ≤ √K * √G := by
    rw [← sqrt_mul' _ hG]; exact Real.abs_le_sqrt hψ1
  rw [sqrt_mul (by positivity), sqrt_c]
  set e := 1 / t ^ 30 with he
  have he0 : 0 < e := by positivity
  have hsG : 0 ≤ √G := sqrt_nonneg _
  have h1 : e * |ψ1| ≤ √K * √G / t ^ 30 := by
    rw [he, one_div_mul_eq_div]; exact div_le_div_of_nonneg_right habs (by positivity)
  have h2 : k * (t ^ 20 * √G) * (1 + e) / ((t ^ 40) ^ 2 * ((1 + e) ^ 2 - 1)) ≤ k * √G / t ^ 30 := by
    have eq : (1 + e) ^ 2 - 1 = e * (2 + e) := by ring
    rw [eq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hte : e * t ^ 30 = 1 := by rw [he]; field_simp
    have key : k * (t ^ 20 * √G) * (1 + e) * t ^ 30 ≤ k * √G * ((t ^ 40) ^ 2 * (e * (2 + e))) := by
      have e1 : k * √G * ((t ^ 40) ^ 2 * (e * (2 + e))) = k * √G * t ^ 50 * (2 + e) * (e * t ^ 30) := by ring
      have e2 : k * (t ^ 20 * √G) * (1 + e) * t ^ 30 = k * √G * t ^ 50 * (1 + e) := by ring
      rw [e1, e2, hte, mul_one]
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact key
  have h3 : m * (t ^ 20 * √G) / (t ^ 40) ^ 2 ≤ m * √G / t ^ 30 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : t ^ 20 * t ^ 30 ≤ (t ^ 40) ^ 2 := by
      rw [← pow_add, ← pow_mul]; exact pow_le_pow_right₀ ht (by norm_num)
    calc m * (t ^ 20 * √G) * t ^ 30 = m * √G * (t ^ 20 * t ^ 30) := by ring
      _ ≤ m * √G * (t ^ 40) ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
  have e4 : √G * (√K + k + m) / t ^ 30 = √K * √G / t ^ 30 + k * √G / t ^ 30 + m * √G / t ^ 30 := by ring
  rw [e4]; linarith

/-- **The pole bound at `η_p = t^{−30}`** is at most `G Q_c/(c t²⁰)`. -/
theorem poleBound_le {G ψ1 : ℝ} (hG : 0 ≤ G) (ht : 1 ≤ t) (hψ1 : ψ1 ^ 2 ≤ K * G) :
    Cvs.L2a.ModeTailTerminalSigmaFree.poleBound (t ^ 40) G (1 / t ^ 30) ψ1 ≤ G * Qc K / (t ^ 40 * t ^ 20) := by
  have ht0 : 0 < t := by linarith
  have hp : 0 ≤ π ^ 2 / 6 := by positivity
  have f1 := pole_factor_le (k := 4) (m := 56 / 9 * (π ^ 2 / 6)) hG ht (by norm_num) (by positivity) hψ1
  have f2 := pole_factor_le (k := 5) (m := 16 / 3 * (π ^ 2 / 6)) hG ht (by norm_num) (by positivity) hψ1
  unfold Cvs.L2a.ModeTailTerminalSigmaFree.poleBound
  have hη : 0 < 1 / t ^ 30 := by positivity
  have p1 : 0 ≤ 1 / t ^ 30 * |ψ1| + 4 * √(t ^ 40 * G) * (1 + 1 / t ^ 30)
      / ((t ^ 40) ^ 2 * ((1 + 1 / t ^ 30) ^ 2 - 1)) + 56 / 9 * (π ^ 2 / 6) * √(t ^ 40 * G) / (t ^ 40) ^ 2 := by
    have : 0 ≤ (1 + 1 / t ^ 30) ^ 2 - 1 := by nlinarith
    positivity
  have hm := mul_le_mul f1 f2 (by
    have : 0 ≤ (1 + 1 / t ^ 30) ^ 2 - 1 := by nlinarith
    positivity) (by positivity)
  calc _ = 2 * ((1 / t ^ 30 * |ψ1| + 4 * √(t ^ 40 * G) * (1 + 1 / t ^ 30)
          / ((t ^ 40) ^ 2 * ((1 + 1 / t ^ 30) ^ 2 - 1)) + 56 / 9 * (π ^ 2 / 6) * √(t ^ 40 * G) / (t ^ 40) ^ 2)
        * (1 / t ^ 30 * |ψ1| + 5 * √(t ^ 40 * G) * (1 + 1 / t ^ 30)
          / ((t ^ 40) ^ 2 * ((1 + 1 / t ^ 30) ^ 2 - 1)) + 16 / 3 * (π ^ 2 / 6) * √(t ^ 40 * G) / (t ^ 40) ^ 2)) := by
        ring
    _ ≤ 2 * (√G * (√K + 4 + 56 / 9 * (π ^ 2 / 6)) / t ^ 30 * (√G * (√K + 5 + 16 / 3 * (π ^ 2 / 6)) / t ^ 30)) := by
        linarith
    _ = 2 * (√G * √G) * ((√K + 4 + 56 / 9 * (π ^ 2 / 6)) * (√K + 5 + 16 / 3 * (π ^ 2 / 6)))
          / (t ^ 30 * t ^ 30) := by ring
    _ = G * Qc K / (t ^ 40 * t ^ 20) := by
        rw [mul_self_sqrt hG]; unfold Qc; field_simp

end Cvs.L2a.SigmaFreeBoundSizesPlunge
