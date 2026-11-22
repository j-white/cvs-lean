import Mathlib
import Cvs.L2a.ExactRootWeightedPairTotal
import Cvs.L2a.FirstModeHigherModeScale
import Cvs.L2a.ModeTailTerminalExactRoot
import Cvs.L2a.NormCrossTermsVanish
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailModesTerminalInequality
import Cvs.Prolate.Envelope.ProlateWeightSizes
import Cvs.Prolate.Mellin.ModeMellinDyadicRange

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sizes of the prolate weights for `ℓc² ≤ c² − χ`

With `0 < ℓ ≤ 1` and `σ = √(c² − χ) ≥ √ℓ c`: `κ₀ ≤ ℓ^{−1/4}`, `A ≤ √(2K/√ℓ)/√c`, `W ≤ √(10/(√3ℓ))/(√ℓc)`; the prime
bound of Cvs.L2a.ModeTailTerminalExactRoot is at most `G P_ℓ/c`, the pole bound at most `Q_ℓ G/c³`, the Mellin bound at most `√G B_ℓ/c`, and at
`s = c^{2/5}`, `c X̄ ≤ C_ℓ/c^{1/10}`, with `P_ℓ`, `Q_ℓ`, `B_ℓ`, `C_ℓ` explicit in `K` and `ℓ`.
-/

namespace Cvs.L2a.ProlateWeightSizesBelowPlunge

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.StationaryPairsWeightedTotal (Aw κw)

variable {c χ ℓ K : ℝ}

theorem sigma_ge (hℓ0 : 0 ≤ ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) : √ℓ * c ≤ √(c ^ 2 - χ) := by
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, sq_sqrt hℓ0]; exact hσ

theorem inv_sigma_sq_le (hc : 0 < c) (hℓ0 : 0 < ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) :
    1 / (c ^ 2 - χ) ≤ 1 / ℓ / c ^ 2 := by
  rw [div_div]; exact one_div_le_one_div_of_le (by positivity) hσ

/-- `κ₀ = √(c/σ) ≤ ℓ^{−1/4}`. -/
theorem κw_le (hc : 0 < c) (hℓ0 : 0 < ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) : κw c χ ≤ √(1 / √ℓ) := by
  unfold κw
  apply sqrt_le_sqrt
  have h := sigma_ge hℓ0.le hσ
  have hs : 0 < √ℓ := sqrt_pos.mpr hℓ0
  rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) h) hs]
  nlinarith

/-- `A = √(2K/(√3σ)) ≤ √(2K/√ℓ)/√c`. -/
theorem Aw_le (hc : 0 < c) (hℓ0 : 0 < ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hK : 0 ≤ K) :
    Aw c χ K ≤ √(2 * K / √ℓ) / √c := by
  unfold Aw
  rw [← sqrt_div' _ hc.le]
  apply sqrt_le_sqrt
  have h := sigma_ge hℓ0.le hσ
  have hs : 0 < √ℓ := sqrt_pos.mpr hℓ0
  have h3 : (1 : ℝ) ≤ √3 := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc √ℓ * c ≤ √(c ^ 2 - χ) := h
    _ ≤ √3 * √(c ^ 2 - χ) := le_mul_of_one_le_left (sqrt_nonneg _) h3

/-- `W = √(10/(√3ℓ))/σ ≤ √(10/(√3ℓ))/(√ℓ c)`. -/
theorem Ww_le (hc : 0 < c) (hℓ0 : 0 < ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) :
    Cvs.L2a.FirstModeHigherModeScale.Ww c χ ℓ ≤ √(10 / (√3 * ℓ)) / (√ℓ * c) := by
  unfold Cvs.L2a.FirstModeHigherModeScale.Ww
  exact div_le_div_of_nonneg_left (sqrt_nonneg _) (by positivity) (sigma_ge hℓ0.le hσ)

/-- The constant of the pole bound. -/
noncomputable def Ql (ℓ : ℝ) : ℝ := 2 * (π ^ 2 / 6) ^ 2 * (2 / ℓ + 2 / ℓ ^ 2) * (2 / ℓ + 3 / (2 * ℓ ^ 2))

/-- **The pole bound is `O(G/c³)`.** -/
theorem poleBound_le {G : ℝ} (hc : 0 < c) (hℓ0 : 0 < ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hG : 0 ≤ G) :
    Cvs.L2a.TailModesTerminalInequality.poleBound c χ G ≤ Ql ℓ * G / c ^ 3 := by
  unfold Cvs.L2a.TailModesTerminalInequality.poleBound Ql
  have hd : 0 < c ^ 2 - χ := lt_of_lt_of_le (by positivity) hσ
  have hi := inv_sigma_sq_le hc hℓ0 hσ
  have hi2 : 1 / (c ^ 2 - χ) ^ 2 ≤ 1 / ℓ ^ 2 / c ^ 4 := by
    rw [div_div]; apply one_div_le_one_div_of_le (by positivity)
    have := pow_le_pow_left₀ (by positivity) hσ 2
    calc ℓ ^ 2 * c ^ 4 = (ℓ * c ^ 2) ^ 2 := by ring
      _ ≤ (c ^ 2 - χ) ^ 2 := this
  set U := √(c * G) with hU
  have hU0 : 0 ≤ U := sqrt_nonneg _
  have hUsq : U ^ 2 = c * G := sq_sqrt (by positivity)
  have hπ : 0 ≤ π ^ 2 / 6 := by positivity
  have a1 : 2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2 ≤ (2 / ℓ + 2 / ℓ ^ 2) * U / c ^ 2 := by
    have e1 : 2 * U / (c ^ 2 - χ) = 2 * U * (1 / (c ^ 2 - χ)) := by ring
    have e2 : 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2 = 2 * c ^ 2 * U * (1 / (c ^ 2 - χ) ^ 2) := by ring
    rw [e1, e2]
    have b1 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * U)
    have b2 := mul_le_mul_of_nonneg_left hi2 (by positivity : 0 ≤ 2 * c ^ 2 * U)
    have e3 : 2 * U * (1 / ℓ / c ^ 2) + 2 * c ^ 2 * U * (1 / ℓ ^ 2 / c ^ 4) = (2 / ℓ + 2 / ℓ ^ 2) * U / c ^ 2 := by
      field_simp
    linarith
  have a2 : 2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2) ≤ (2 / ℓ + 3 / (2 * ℓ ^ 2)) * U / c ^ 2 := by
    have e1 : 2 * U / (c ^ 2 - χ) = 2 * U * (1 / (c ^ 2 - χ)) := by ring
    have e2 : 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2) = 3 * c ^ 2 * U / 2 * (1 / (c ^ 2 - χ) ^ 2) := by field_simp
    rw [e1, e2]
    have b1 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * U)
    have b2 := mul_le_mul_of_nonneg_left hi2 (by positivity : 0 ≤ 3 * c ^ 2 * U / 2)
    have e3 : 2 * U * (1 / ℓ / c ^ 2) + 3 * c ^ 2 * U / 2 * (1 / ℓ ^ 2 / c ^ 4)
        = (2 / ℓ + 3 / (2 * ℓ ^ 2)) * U / c ^ 2 := by field_simp
    linarith
  have p1 : 0 ≤ 2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2 := by positivity
  have p2 : 0 ≤ 2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2) := by positivity
  calc 2 * (π ^ 2 / 6 * (2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2))
        * (π ^ 2 / 6 * (2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2)))
      ≤ 2 * (π ^ 2 / 6 * ((2 / ℓ + 2 / ℓ ^ 2) * U / c ^ 2)) * (π ^ 2 / 6 * ((2 / ℓ + 3 / (2 * ℓ ^ 2)) * U / c ^ 2)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a1 hπ) (by norm_num))
          (mul_le_mul_of_nonneg_left a2 hπ) (by positivity) (by positivity)
    _ = 2 * (π ^ 2 / 6) ^ 2 * (2 / ℓ + 2 / ℓ ^ 2) * (2 / ℓ + 3 / (2 * ℓ ^ 2)) * U ^ 2 / c ^ 4 := by ring
    _ = _ := by rw [hUsq]; field_simp

/-- The constant of the prime bound. -/
noncomputable def Pl (K ℓ : ℝ) : ℝ :=
  2 * (((5 / ℓ + 1) * √(2 * K / √ℓ) + 20 * √(1 / √ℓ) + 32 * √(1 / √ℓ) / 9) * (π ^ 2 / 6)
        * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
      + 3 * (32 * √(5 / ℓ + 1) * √(1 / √ℓ) / 3) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n)
      + 8 * (√(2 * K / √ℓ) + 2 * √(10 / (√3 * ℓ)) / √ℓ)
    + 4 / 3 * (π ^ 2 / 6) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
    + 8 * (2 / √3) * (36 * (π ^ 2 / 6 + 6)))

set_option maxHeartbeats 2000000 in
/-- **The prime bound is `O(G/c)`**, for `ℓc² ≤ c² − χ`, `ℓ ≤ 1`, `(3/5)√c ℓ ≥ 1`. -/
theorem primeBound_le {G : ℝ} (hc : 1 ≤ c) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ)
    (hsℓ : 1 ≤ 3 / 5 * (√c * ℓ)) (hG : 0 ≤ G) (hK : 0 ≤ K) :
    Cvs.L2a.ModeTailTerminalExactRoot.primeBound c χ G K ℓ ≤ G * Pl K ℓ / c := by
  have hc0 : 0 < c := by linarith
  have hsc0 : 0 < √c := sqrt_pos.mpr hc0
  have hsc1 : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  have hscc : √c ≤ c := by rw [sqrt_le_left hc0.le]; nlinarith
  have hss : √(√c) ≤ c := (Real.sqrt_le_sqrt hscc).trans (by rw [sqrt_le_left hc0.le]; nlinarith)
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  have hsℓ0 : 0 < √ℓ := sqrt_pos.mpr hℓ0
  set L2 := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 with hL2
  set L3 := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n) with hL3
  have hL20 : 0 ≤ L2 := tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hL30 : 0 ≤ L3 := tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hπ : 0 ≤ π ^ 2 / 6 := by positivity
  set a₀ := √(2 * K / √ℓ) with ha₀
  set kl := √(1 / √ℓ) with hkl
  set w₁ := √(10 / (√3 * ℓ)) with hw₁
  set L := 5 / ℓ + 1 with hL
  have ha₀0 : 0 ≤ a₀ := sqrt_nonneg _
  have hkl0 : 0 ≤ kl := sqrt_nonneg _
  have hw₁0 : 0 ≤ w₁ := sqrt_nonneg _
  have hL0 : 0 < L := by positivity
  have hA : Aw c χ K ≤ a₀ / √c := Aw_le hc0 hℓ0 hσ hK
  have hA0 : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : κw c χ ≤ kl := κw_le hc0 hℓ0 hσ
  have hκ0 : 0 ≤ κw c χ := sqrt_nonneg _
  have hσ' := sigma_ge hℓ0.le hσ
  have hd : 0 < c ^ 2 - χ := lt_of_lt_of_le (by positivity) hσ
  -- the pieces
  have b1 : Cvs.L2a.ExactRootWeightedPairTotal.C1 c χ K ℓ ≤ (L * a₀ + 20 * kl + 32 * kl / 9) / c := by
    unfold Cvs.L2a.ExactRootWeightedPairTotal.C1
    have t1 : L * Aw c χ K / √c ≤ L * a₀ / c := by
      calc L * Aw c χ K / √c ≤ L * (a₀ / √c) / √c :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA hL0.le) hsc0.le
        _ = L * a₀ / (√c * √c) := by field_simp
        _ = L * a₀ / c := by rw [hcc]
    have t2 : 20 * κw c χ * √c / c ^ 2 ≤ 20 * kl / c := by
      rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith [mul_le_mul hκ hscc hsc0.le hkl0]
    have t3 : 32 * κw c χ / (9 * c) ≤ 32 * kl / 9 / c := by
      rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith
    have e : (L * a₀ + 20 * kl + 32 * kl / 9) / c = L * a₀ / c + 20 * kl / c + 32 * kl / 9 / c := by ring
    linarith
  have b2 : Cvs.L2a.ExactRootWeightedPairTotal.C3 c χ ℓ ≤ 32 * √L * kl / 3 / c := by
    unfold Cvs.L2a.ExactRootWeightedPairTotal.C3
    rw [div_le_div_iff₀ (by positivity) hc0]
    have := mul_le_mul hκ hss (sqrt_nonneg _) hkl0
    have hsL : 0 ≤ √L := sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 32 * √L)]
  have b3 : Cvs.L2a.ExactRootWeightedPairTotal.Hc c χ K ℓ * (log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2)
      ≤ 8 * (a₀ + 2 * w₁ / √ℓ) / c := by
    have hl := Cvs.Prolate.Envelope.ProlateWeightSizes.log_cube_le hsℓ
    have hl0 : 0 ≤ log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2 :=
      mul_nonneg (log_nonneg hsℓ) (sq_nonneg _)
    have hl' : log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2 ≤ 8 * √c := by
      refine hl.trans ?_
      have : 3 / 5 * (√c * ℓ) ≤ √c := by nlinarith
      linarith
    have hsum : Cvs.L2a.ExactRootWeightedPairTotal.Hc c χ K ℓ ≤ (a₀ + 2 * w₁ / √ℓ) / (c * √c) := by
      unfold Cvs.L2a.ExactRootWeightedPairTotal.Hc
      have u1 : Aw c χ K / c ≤ a₀ / (c * √c) := by
        calc Aw c χ K / c ≤ a₀ / √c / c := div_le_div_of_nonneg_right hA hc0.le
          _ = a₀ / (c * √c) := by field_simp
      have u2 : 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / √c ≤ 2 * w₁ / √ℓ / (c * √c) := by
        calc 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / √c ≤ 2 * w₁ / (√ℓ * c) / √c := by
              apply div_le_div_of_nonneg_right _ hsc0.le
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) hσ'
          _ = 2 * w₁ / √ℓ / (c * √c) := by field_simp
      have e : (a₀ + 2 * w₁ / √ℓ) / (c * √c) = a₀ / (c * √c) + 2 * w₁ / √ℓ / (c * √c) := by ring
      linarith
    have hH0 : 0 ≤ Cvs.L2a.ExactRootWeightedPairTotal.Hc c χ K ℓ := by
      unfold Cvs.L2a.ExactRootWeightedPairTotal.Hc; positivity
    calc _ ≤ (a₀ + 2 * w₁ / √ℓ) / (c * √c) * (8 * √c) := mul_le_mul hsum hl' hl0 (by positivity)
      _ = 8 * (a₀ + 2 * w₁ / √ℓ) / c := by field_simp
  have b4 : G / (3 / 4 * c) = 4 / 3 * G / c := by field_simp
  have b5 : 8 * G * (2 / √3) / c ^ 2 ≤ 8 * G * (2 / √3) / c := by
    apply div_le_div_of_nonneg_left (by positivity) hc0; nlinarith
  unfold Cvs.L2a.ModeTailTerminalExactRoot.primeBound Pl
  rw [← hL2, ← hL3, ← ha₀, ← hkl, ← hw₁, ← hL]
  have hC10 : 0 ≤ Cvs.L2a.ExactRootWeightedPairTotal.C1 c χ K ℓ := by unfold Cvs.L2a.ExactRootWeightedPairTotal.C1; positivity
  have m1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right b1 hπ) hL20
  have m2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ 3)) hL30
  have m5 := mul_le_mul_of_nonneg_right b5 (by positivity : (0 : ℝ) ≤ 36 * (π ^ 2 / 6 + 6))
  have hin : G * (Cvs.L2a.ExactRootWeightedPairTotal.C1 c χ K ℓ * (π ^ 2 / 6) * L2 + 3 * Cvs.L2a.ExactRootWeightedPairTotal.C3 c χ ℓ * L3
        + Cvs.L2a.ExactRootWeightedPairTotal.Hc c χ K ℓ * (log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2))
      ≤ G * ((L * a₀ + 20 * kl + 32 * kl / 9) / c * (π ^ 2 / 6) * L2 + 3 * (32 * √L * kl / 3 / c) * L3
        + 8 * (a₀ + 2 * w₁ / √ℓ) / c) :=
    mul_le_mul_of_nonneg_left (by linarith) hG
  have e2 : G * (2 * ((L * a₀ + 20 * kl + 32 * kl / 9) * (π ^ 2 / 6) * L2 + 3 * (32 * √L * kl / 3) * L3
        + 8 * (a₀ + 2 * w₁ / √ℓ) + 4 / 3 * (π ^ 2 / 6) * L2 + 8 * (2 / √3) * (36 * (π ^ 2 / 6 + 6)))) / c
      = 2 * (G * ((L * a₀ + 20 * kl + 32 * kl / 9) / c * (π ^ 2 / 6) * L2 + 3 * (32 * √L * kl / 3 / c) * L3
        + 8 * (a₀ + 2 * w₁ / √ℓ) / c) + 4 / 3 * G / c * (π ^ 2 / 6) * L2
        + 8 * G * (2 / √3) / c * (36 * (π ^ 2 / 6 + 6))) := by
    field_simp
  rw [e2, b4]
  linarith

/-- The constant of the Mellin bound. -/
noncomputable def Bml (K ℓ : ℝ) : ℝ :=
  √K + 16 * √2 * √K / √ℓ + 32 * √2 / ℓ + 4 / 3 * (2 * √(1 / √ℓ) + 2)
    + π ^ 2 / 6 * (16 / 3) * (2 * √2 * √(1 / √ℓ) + √2)

set_option maxHeartbeats 2000000 in
/-- **The Mellin bound below `√c` is `O(√G/c)`**, at `η = 1/c`, for `ℓc² ≤ c² − χ`. -/
theorem mellinBound_le {G ψ1 : ℝ} (hc : 1 ≤ c) (hℓ0 : 0 < ℓ) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ)
    (hK : 0 ≤ K) (hψ1 : ψ1 ^ 2 ≤ K * G) :
    Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G (1 / c) √c ψ1 ≤ √G * Bml K ℓ / c := by
  have hc0 : 0 < c := by linarith
  have hsc0 : 0 < √c := sqrt_pos.mpr hc0
  have hsc1 : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  have hscc : √c ≤ c := by rw [sqrt_le_left hc0.le]; nlinarith
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  have hsG : 0 ≤ √G := sqrt_nonneg _
  have hsℓ : 0 < √ℓ := sqrt_pos.mpr hℓ0
  have hσ' := sigma_ge hℓ0.le hσ
  have hσ0 : 0 < √(c ^ 2 - χ) := lt_of_lt_of_le (by positivity) hσ'
  have hi := inv_sigma_sq_le hc0 hℓ0 hσ
  have hd : 0 < c ^ 2 - χ := lt_of_lt_of_le (by positivity) hσ
  have hp1 : |ψ1| ≤ √K * √G := by
    rw [← sqrt_mul hK]; exact Real.abs_le_sqrt hψ1
  have hV : √c + 1 / 2 ≤ 2 * √c := by linarith
  have h2 : (0 : ℝ) < √2 := by positivity
  have h3 : (1 : ℝ) ≤ √3 := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set kl := √(1 / √ℓ) with hkl
  have hkl0 : 0 ≤ kl := sqrt_nonneg _
  have hkl2 : kl * kl = 1 / √ℓ := mul_self_sqrt (by positivity)
  unfold Cvs.L2a.TailModesPoleMellinValues.mellinBound Cvs.Prolate.Mellin.ModeMellinDyadicRange.P
  -- t1
  have t1 : 1 / c * |ψ1| * 1 ≤ √K * √G / c := by
    rw [mul_one, one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hp1 hc0.le
  -- t2
  have t2 : 8 * √2 * |ψ1| * (√c + 1 / 2) / (c * √(c ^ 2 - χ)) ≤ 16 * √2 * √K / √ℓ * √G / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]
    have b : c * (√ℓ * c) ≤ c * √(c ^ 2 - χ) := mul_le_mul_of_nonneg_left hσ' hc0.le
    have a := mul_le_mul hp1 hV (by positivity) (by positivity)
    calc 8 * √2 * |ψ1| * (√c + 1 / 2) * c = 8 * √2 * (|ψ1| * (√c + 1 / 2)) * c := by ring
      _ ≤ 8 * √2 * (√K * √G * (2 * √c)) * c := by gcongr
      _ = 16 * √2 * √K * √G * (√c * c) := by ring
      _ ≤ 16 * √2 * √K * √G * (c * c) := by gcongr
      _ = 16 * √2 * √K / √ℓ * √G * (c * (√ℓ * c)) := by field_simp
      _ ≤ 16 * √2 * √K / √ℓ * √G * (c * √(c ^ 2 - χ)) := by gcongr
  -- t3
  have t3 : 32 * √2 * √(c * G) * 1 / (c ^ 2 - χ) ≤ 32 * √2 / ℓ * √G / c := by
    rw [mul_one, sqrt_mul hc0.le]
    calc 32 * √2 * (√c * √G) / (c ^ 2 - χ) = 32 * √2 * (√c * √G) * (1 / (c ^ 2 - χ)) := by ring
      _ ≤ 32 * √2 * (√c * √G) * (1 / ℓ / c ^ 2) := by gcongr
      _ = 32 * √2 / ℓ * √G * √c / c ^ 2 := by ring
      _ ≤ 32 * √2 / ℓ * √G * c / c ^ 2 := by gcongr
      _ = 32 * √2 / ℓ * √G / c := by field_simp
  -- a common size: `√(G/y) ≤ √G/(√β √c)` for `y ≥ β c`
  have hsq : ∀ β y : ℝ, 0 < β → β * c ≤ y → √(G / y) ≤ √G / (√β * √c) := by
    intro β y hβ hy
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
    rw [sqrt_div' _ hy0.le, ← sqrt_mul hβ.le]
    exact div_le_div_of_nonneg_left hsG (by positivity) (sqrt_le_sqrt hy)
  have hβ1 : √(√ℓ) * √c * kl = √c := by
    have : √(√ℓ) * kl = 1 := by
      rw [hkl, ← sqrt_mul (sqrt_nonneg _), mul_one_div_cancel hsℓ.ne', sqrt_one]
    calc √(√ℓ) * √c * kl = (√(√ℓ) * kl) * √c := by ring
      _ = √c := by rw [this, one_mul]
  -- t4
  have t4 : 2 * (8 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) / 1 + 1 * √(2 * c * G * 2))
      / (c ^ 2 * 1 ^ 2 * 2 ^ 2)) ≤ 4 / 3 * (2 * kl + 2) * √G / c := by
    have hy : √ℓ * c ≤ √3 / 2 * √(c ^ 2 - χ) * 2 := by nlinarith
    have hA := hsq (√ℓ) _ hsℓ hy
    have hA' : √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) ≤ kl * √G / √c := by
      refine hA.trans (le_of_eq ?_)
      rw [div_eq_div_iff (by positivity) hsc0.ne']
      nlinarith [hβ1]
    have u1 : (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) ≤ 2 * kl * √G := by
      calc (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) ≤ 2 * √c * (kl * √G / √c) :=
            mul_le_mul hV hA' (sqrt_nonneg _) (by positivity)
        _ = 2 * kl * √G := by field_simp
    have u2 : √(2 * c * G * 2) = 2 * √c * √G := by
      rw [show 2 * c * G * 2 = 2 ^ 2 * (c * G) by ring, sqrt_mul (by norm_num), sqrt_sq (by norm_num),
        sqrt_mul hc0.le]; ring
    rw [div_one, one_mul, u2, one_pow, mul_one]
    have hnum : 2 * kl * √G + 2 * √c * √G ≤ (2 * kl + 2) * √G * c := by
      nlinarith [mul_le_mul_of_nonneg_left hscc (by positivity : (0:ℝ) ≤ 2 * √G),
        mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 2 * kl * √G)]
    calc 2 * (8 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) + 2 * √c * √G) / (c ^ 2 * 2 ^ 2))
        ≤ 2 * (8 / 3 * (2 * kl * √G + 2 * √c * √G) / (c ^ 2 * 2 ^ 2)) := by gcongr
      _ ≤ 2 * (8 / 3 * ((2 * kl + 2) * √G * c) / (c ^ 2 * 2 ^ 2)) := by gcongr
      _ = 4 / 3 * (2 * kl + 2) * √G / c := by field_simp; ring
  -- t5
  have t5 : π ^ 2 / 6 * (16 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) + 1 * √(2 * c * G)) / c ^ 2)
      ≤ π ^ 2 / 6 * (16 / 3) * (2 * √2 * kl + √2) * √G / c := by
    have hy : √ℓ / 2 * c ≤ √3 / 2 * √(c ^ 2 - χ) := by nlinarith
    have hA := hsq (√ℓ / 2) _ (by positivity) hy
    have hA' : √(G / (√3 / 2 * √(c ^ 2 - χ))) ≤ √2 * kl * √G / √c := by
      refine hA.trans (le_of_eq ?_)
      have e : √(√ℓ / 2) = √(√ℓ) / √2 := sqrt_div' _ (by norm_num)
      rw [e, div_eq_div_iff (by positivity) hsc0.ne']
      field_simp
      nlinarith [hβ1]
    have u1 : (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) ≤ 2 * √2 * kl * √G := by
      calc (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) ≤ 2 * √c * (√2 * kl * √G / √c) :=
            mul_le_mul hV hA' (sqrt_nonneg _) (by positivity)
        _ = 2 * √2 * kl * √G := by field_simp
    have u2 : √(2 * c * G) = √2 * √c * √G := by rw [sqrt_mul (by positivity), sqrt_mul (by norm_num)]
    rw [one_mul, u2]
    have hnum : 2 * √2 * kl * √G + √2 * √c * √G ≤ (2 * √2 * kl + √2) * √G * c := by
      nlinarith [mul_le_mul_of_nonneg_left hscc (by positivity : (0:ℝ) ≤ √2 * √G),
        mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 2 * √2 * kl * √G)]
    calc π ^ 2 / 6 * (16 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) + √2 * √c * √G) / c ^ 2)
        ≤ π ^ 2 / 6 * (16 / 3 * (2 * √2 * kl * √G + √2 * √c * √G) / c ^ 2) := by gcongr
      _ ≤ π ^ 2 / 6 * (16 / 3 * ((2 * √2 * kl + √2) * √G * c) / c ^ 2) := by gcongr
      _ = π ^ 2 / 6 * (16 / 3) * (2 * √2 * kl + √2) * √G / c := by field_simp
  have e : √G * Bml K ℓ / c = √K * √G / c + 16 * √2 * √K / √ℓ * √G / c + 32 * √2 / ℓ * √G / c
      + 4 / 3 * (2 * kl + 2) * √G / c + π ^ 2 / 6 * (16 / 3) * (2 * √2 * kl + √2) * √G / c := by
    unfold Bml; rw [← hkl]; field_simp
  rw [e]
  linarith

/-- The constant of the cross terms at `s = c^{2/5}`. -/
noncomputable def Cxl (K ℓ : ℝ) : ℝ :=
  3 * (5 / ℓ + 1) * √(2 * K / √ℓ) * √(10 / ℓ) + 5 * (√(2 * K / √ℓ) + 2 * (√(10 / (√3 * ℓ)) / √ℓ))
    + √(1 / √ℓ) * (32 / 9 + 20 + 64 / 9) * (π ^ 2 / 6) + 32 * √(5 / ℓ + 1) * √(1 / √ℓ)

set_option maxHeartbeats 4000000 in
/-- **The cross terms at `s = c^{2/5}`**: `c X̄ ≤ C_ℓ/c^{1/10}`, for `ℓc² ≤ c² − χ`, `(3/5)c^{2/5}ℓ ≥ 1`. -/
theorem c_mul_Xbar_le (hc : 1 ≤ c) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hσ : ℓ * c ^ 2 ≤ c ^ 2 - χ) (hK : 0 ≤ K)
    (hs : 1 ≤ 3 / 5 * (c ^ ((2 : ℝ) / 5) * ℓ)) :
    c * Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K (c ^ ((2 : ℝ) / 5)) ℓ ≤ Cxl K ℓ / c ^ ((1 : ℝ) / 10) := by
  have hc0 : 0 < c := by linarith
  set t := c ^ ((1 : ℝ) / 10) with ht
  have ht0 : 0 < t := rpow_pos_of_pos hc0 _
  have ht1 : 1 ≤ t := one_le_rpow hc (by norm_num)
  have hct : c = t ^ 10 := by rw [ht, ← Cvs.L2a.NormCrossTermsVanish.rpow_tenth hc0 10]; norm_num
  have hs4 : c ^ ((2 : ℝ) / 5) = t ^ 4 := by rw [ht, ← Cvs.L2a.NormCrossTermsVanish.rpow_tenth hc0 4]; norm_num
  have hsc : √c = t ^ 5 := by
    rw [hct, show t ^ 10 = (t ^ 5) ^ 2 by ring, sqrt_sq (by positivity)]
  have hss : √(t ^ 4) = t ^ 2 := by rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, sqrt_sq (by positivity)]
  have hsℓ : 0 < √ℓ := sqrt_pos.mpr hℓ0
  set a₀ := √(2 * K / √ℓ) with ha₀
  set kl := √(1 / √ℓ) with hkl
  set w₂ := √(10 / (√3 * ℓ)) / √ℓ with hw₂
  set L := 5 / ℓ + 1 with hL
  have ha₀0 : 0 ≤ a₀ := sqrt_nonneg _
  have hkl0 : 0 ≤ kl := sqrt_nonneg _
  have hw₂0 : 0 ≤ w₂ := by positivity
  have hL0 : 0 < L := by positivity
  have hA : Aw c χ K ≤ a₀ / t ^ 5 := by rw [← hsc]; exact Aw_le hc0 hℓ0 hσ hK
  have hA0 : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : κw c χ ≤ kl := κw_le hc0 hℓ0 hσ
  have hκ0 : 0 ≤ κw c χ := sqrt_nonneg _
  have hW : Cvs.L2a.FirstModeHigherModeScale.Ww c χ ℓ ≤ w₂ / t ^ 10 := by
    refine (Ww_le hc0 hℓ0 hσ).trans (le_of_eq ?_); rw [hw₂, ← hct]; field_simp
  have hW0 : 0 ≤ Cvs.L2a.FirstModeHigherModeScale.Ww c χ ℓ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  rw [hs4] at hs ⊢
  unfold Cvs.L2a.FirstModeHigherModeScale.Xbar
  rw [hss, hsc]
  set Av := Aw c χ K with hAv
  set κv := κw c χ with hκv
  set Wv := Cvs.L2a.FirstModeHigherModeScale.Ww c χ ℓ with hWv
  -- the four terms
  have h1 : √(6 / (3 / 5 * (t ^ 4 * ℓ))) = √(10 / ℓ) / t ^ 2 := by
    rw [show 6 / (3 / 5 * (t ^ 4 * ℓ)) = 10 / ℓ / (t ^ 2) ^ 2 by field_simp; ring, sqrt_div' _ (by positivity),
      sqrt_sq (by positivity)]
  have v1 : c * (L * Av / t ^ 4 * (3 * √(6 / (3 / 5 * (t ^ 4 * ℓ))))) ≤ 3 * L * a₀ * √(10 / ℓ) / t := by
    rw [h1, hct]
    calc t ^ 10 * (L * Av / t ^ 4 * (3 * (√(10 / ℓ) / t ^ 2)))
        ≤ t ^ 10 * (L * (a₀ / t ^ 5) / t ^ 4 * (3 * (√(10 / ℓ) / t ^ 2))) := by gcongr
      _ = 3 * L * a₀ * √(10 / ℓ) / t := by field_simp
  have hlog : log (3 / 5 * (t ^ 4 * ℓ)) ≤ 4 * t := by
    have hle : 3 / 5 * (t ^ 4 * ℓ) ≤ t ^ 4 := by nlinarith [pow_pos ht0 4]
    calc log (3 / 5 * (t ^ 4 * ℓ)) ≤ log (t ^ 4) := log_le_log (by linarith) hle
      _ = 4 * log t := by rw [log_pow]; push_cast; ring
      _ ≤ 4 * t := by have := log_le_sub_one_of_pos ht0; linarith
  have hlog0 : 0 ≤ log (3 / 5 * (t ^ 4 * ℓ)) := log_nonneg hs
  have v2 : c * ((Av / c + 2 * Wv / t ^ 4) * (1 + log (3 / 5 * (t ^ 4 * ℓ))))
      ≤ 5 * (a₀ + 2 * w₂) / t := by
    rw [hct]
    have hb : Av / t ^ 10 + 2 * Wv / t ^ 4 ≤ (a₀ + 2 * w₂) / t ^ 14 := by
      have u1 : Av / t ^ 10 ≤ a₀ / t ^ 14 := by
        calc Av / t ^ 10 ≤ a₀ / t ^ 5 / t ^ 10 := by gcongr
          _ = a₀ / t ^ 15 := by field_simp
          _ ≤ a₀ / t ^ 14 := div_le_div_of_nonneg_left ha₀0 (by positivity)
              (by nlinarith [pow_le_pow_right₀ ht1 (show 14 ≤ 15 by norm_num), pow_pos ht0 14])
      have u2 : 2 * Wv / t ^ 4 ≤ 2 * w₂ / t ^ 14 := by
        calc 2 * Wv / t ^ 4 ≤ 2 * (w₂ / t ^ 10) / t ^ 4 := by gcongr
          _ = 2 * w₂ / t ^ 14 := by field_simp
      have e : (a₀ + 2 * w₂) / t ^ 14 = a₀ / t ^ 14 + 2 * w₂ / t ^ 14 := by ring
      linarith
    have hb0 : 0 ≤ Av / t ^ 10 + 2 * Wv / t ^ 4 := by positivity
    calc t ^ 10 * ((Av / t ^ 10 + 2 * Wv / t ^ 4) * (1 + log (3 / 5 * (t ^ 4 * ℓ))))
        ≤ t ^ 10 * ((a₀ + 2 * w₂) / t ^ 14 * (5 * t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hb (by linarith) (by linarith) (by positivity)
      _ = 5 * (a₀ + 2 * w₂) / t ^ 3 := by field_simp
      _ ≤ 5 * (a₀ + 2 * w₂) / t := div_le_div_of_nonneg_left (by positivity) ht0
          (by nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 3 by norm_num)])
  have v3 : c * (κv * (32 * t ^ 4 * t ^ 5 / (9 * c ^ 2) + 20 * t ^ 4 / c ^ 2 + 64 * t ^ 4 / (9 * c ^ 2))
      * (π ^ 2 / 6)) ≤ kl * (32 / 9 + 20 + 64 / 9) * (π ^ 2 / 6) / t := by
    rw [hct]
    have h6 : 1 / t ^ 6 ≤ 1 / t := one_div_le_one_div_of_le ht0 (by nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 6 by norm_num)])
    have e : t ^ 10 * (κv * (32 * t ^ 4 * t ^ 5 / (9 * (t ^ 10) ^ 2) + 20 * t ^ 4 / (t ^ 10) ^ 2
        + 64 * t ^ 4 / (9 * (t ^ 10) ^ 2)) * (π ^ 2 / 6))
        = κv * (π ^ 2 / 6) * (32 / 9 * (1 / t) + (20 + 64 / 9) * (1 / t ^ 6)) := by field_simp; ring
    rw [e]
    have hπ : 0 ≤ π ^ 2 / 6 := by positivity
    calc κv * (π ^ 2 / 6) * (32 / 9 * (1 / t) + (20 + 64 / 9) * (1 / t ^ 6))
        ≤ kl * (π ^ 2 / 6) * (32 / 9 * (1 / t) + (20 + 64 / 9) * (1 / t)) := by gcongr
      _ = kl * (32 / 9 + 20 + 64 / 9) * (π ^ 2 / 6) / t := by ring
  have v4 : c * (32 * √L * κv * t ^ 2 / (3 * c ^ 2) * 3) ≤ 32 * √L * kl / t := by
    rw [hct]
    have e : t ^ 10 * (32 * √L * κv * t ^ 2 / (3 * (t ^ 10) ^ 2) * 3) = 32 * √L * κv / t ^ 8 := by
      field_simp
    rw [e]
    have hsL : 0 ≤ √L := sqrt_nonneg _
    calc 32 * √L * κv / t ^ 8 ≤ 32 * √L * kl / t ^ 8 := by gcongr
      _ ≤ 32 * √L * kl / t := div_le_div_of_nonneg_left (by positivity) ht0
          (by nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 8 by norm_num)])
  have e : Cxl K ℓ / t = 3 * L * a₀ * √(10 / ℓ) / t + 5 * (a₀ + 2 * w₂) / t
      + kl * (32 / 9 + 20 + 64 / 9) * (π ^ 2 / 6) / t + 32 * √L * kl / t := by
    unfold Cxl; rw [← ha₀, ← hkl, ← hL, ← hw₂]; field_simp
  rw [e, mul_add, mul_add, mul_add]
  linarith

end Cvs.L2a.ProlateWeightSizesBelowPlunge
