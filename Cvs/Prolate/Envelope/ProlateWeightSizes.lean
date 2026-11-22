import Mathlib
import Cvs.L2a.FirstModeHigherModePair
import Cvs.L2a.NonstationaryPairsAllShifts
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailModesTerminalInequality
import Cvs.Prolate.Mellin.ModeMellinDyadicRange

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sizes of the prolate weights for `c ≥ 4`, `0 ≤ χ ≤ c√c`

Then `c² − χ ≥ c²/2`, so `σ ≥ c/√2`: `κ₀ = √(c/σ) ≤ 2`, `A = √(2K/(√3σ)) ≤ √(2K/c)`, `Q = √(4√3)/σ ≤ 4/c`,
`α = (√3/2)σ ≥ c/2`, and `√(2c/(√3σ)) ≤ 2`.
-/

namespace Cvs.Prolate.Envelope.ProlateWeightSizes

open Real Cvs.L2a.StationaryPairsWeightedTotal

variable {c χ K : ℝ}

theorem half_sq_le (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : c ^ 2 / 2 ≤ c ^ 2 - χ := by
  have h2 : 2 ≤ √c := by rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
                         exact Real.sqrt_le_sqrt hc
  have hsc : √c ≤ c / 2 := by
    have := mul_self_sqrt (by linarith : (0 : ℝ) ≤ c)
    nlinarith
  have : c * √c ≤ c * (c / 2) := mul_le_mul_of_nonneg_left hsc (by linarith)
  nlinarith

theorem sigma_ge (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : c / 2 ≤ √(c ^ 2 - χ) := by
  apply Real.le_sqrt_of_sq_le
  have := half_sq_le hc hχ0 hχs
  nlinarith

theorem κw_le (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : κw c χ ≤ 2 := by
  unfold κw
  have hσ := sigma_ge hc hχ0 hχs
  have hσ0 : 0 < √(c ^ 2 - χ) := by linarith
  rw [sqrt_le_left (by norm_num)]
  rw [div_le_iff₀ hσ0]; nlinarith

theorem Aw_le (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) (hK : 0 ≤ K) : Aw c χ K ≤ √(4 * K / c) := by
  unfold Aw
  apply Real.sqrt_le_sqrt
  have hσ := sigma_ge hc hχ0 hχs
  have hc0 : 0 < c := by linarith
  have h3 : (1 : ℝ) ≤ √3 := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hd : c / 2 ≤ √3 * √(c ^ 2 - χ) := by nlinarith
  calc 2 * K / (√3 * √(c ^ 2 - χ)) ≤ 2 * K / (c / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = 4 * K / c := by field_simp; ring

theorem Qw_le (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : Qw c χ ≤ 8 / c := by
  unfold Qw
  have hσ := sigma_ge hc hχ0 hχs
  have hc0 : 0 < c := by linarith
  have h1 : √(4 * √3) ≤ 4 := by
    rw [sqrt_le_left (by norm_num)]
    have : √3 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
    linarith
  calc √(4 * √3) / √(c ^ 2 - χ) ≤ 4 / (c / 2) :=
        div_le_div₀ (by norm_num) h1 (by linarith) hσ
    _ = 8 / c := by field_simp; ring

theorem alpha_ge (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : c / 4 ≤ √3 / 2 * √(c ^ 2 - χ) := by
  have hσ := sigma_ge hc hχ0 hχs
  have h3 : (1 : ℝ) ≤ √3 := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith

theorem kappa_le (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : √(2 * c / (√3 * √(c ^ 2 - χ))) ≤ 2 := by
  have hσ := sigma_ge hc hχ0 hχs
  have hc0 : 0 < c := by linarith
  have h3 : (1 : ℝ) ≤ √3 := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hden : 0 < √3 * √(c ^ 2 - χ) := mul_pos (by linarith) (by linarith)
  rw [sqrt_le_left (by norm_num), div_le_iff₀ hden]
  nlinarith

theorem inv_sigma_sq_le (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) : 1 / (c ^ 2 - χ) ≤ 2 / c ^ 2 := by
  have h := half_sq_le hc hχ0 hχs
  have hc0 : 0 < c := by linarith
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]; linarith

/-- **The pole bound is `O(G/c³)`.** -/
theorem poleBound_le {G : ℝ} (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) (hG : 0 ≤ G) :
    Cvs.L2a.TailModesTerminalInequality.poleBound c χ G ≤ 240 * (π ^ 2 / 6) ^ 2 * G / c ^ 3 := by
  unfold Cvs.L2a.TailModesTerminalInequality.poleBound
  have hc0 : 0 < c := by linarith
  have hd : 0 < c ^ 2 - χ := by nlinarith [half_sq_le hc hχ0 hχs]
  have hi := inv_sigma_sq_le hc hχ0 hχs
  have hi2 : 1 / (c ^ 2 - χ) ^ 2 ≤ 4 / c ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hi 2
    rw [div_pow, one_pow, div_pow] at this
    have e : (2 : ℝ) ^ 2 / (c ^ 2) ^ 2 = 4 / c ^ 4 := by ring
    rwa [e] at this
  set U := √(c * G) with hU
  have hU0 : 0 ≤ U := sqrt_nonneg _
  have hUsq : U ^ 2 = c * G := sq_sqrt (by positivity)
  have hπ : 0 ≤ π ^ 2 / 6 := by positivity
  have a1 : 2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2 ≤ 12 * U / c ^ 2 := by
    have e1 : 2 * U / (c ^ 2 - χ) = 2 * U * (1 / (c ^ 2 - χ)) := by ring
    have e2 : 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2 = 2 * c ^ 2 * U * (1 / (c ^ 2 - χ) ^ 2) := by ring
    rw [e1, e2]
    have b1 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * U)
    have b2 := mul_le_mul_of_nonneg_left hi2 (by positivity : 0 ≤ 2 * c ^ 2 * U)
    have e3 : 2 * U * (2 / c ^ 2) + 2 * c ^ 2 * U * (4 / c ^ 4) = 12 * U / c ^ 2 := by field_simp; ring
    linarith
  have a2 : 2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2) ≤ 10 * U / c ^ 2 := by
    have e1 : 2 * U / (c ^ 2 - χ) = 2 * U * (1 / (c ^ 2 - χ)) := by ring
    have e2 : 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2) = 3 * c ^ 2 * U / 2 * (1 / (c ^ 2 - χ) ^ 2) := by field_simp
    rw [e1, e2]
    have b1 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * U)
    have b2 := mul_le_mul_of_nonneg_left hi2 (by positivity : 0 ≤ 3 * c ^ 2 * U / 2)
    have e3 : 2 * U * (2 / c ^ 2) + 3 * c ^ 2 * U / 2 * (4 / c ^ 4) = 10 * U / c ^ 2 := by field_simp; ring
    linarith
  have p1 : 0 ≤ 2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2 := by positivity
  have p2 : 0 ≤ 2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2) := by positivity
  calc 2 * (π ^ 2 / 6 * (2 * U / (c ^ 2 - χ) + 2 * c ^ 2 * U / (c ^ 2 - χ) ^ 2))
        * (π ^ 2 / 6 * (2 * U / (c ^ 2 - χ) + 3 * c ^ 2 * U / (2 * (c ^ 2 - χ) ^ 2)))
      ≤ 2 * (π ^ 2 / 6 * (12 * U / c ^ 2)) * (π ^ 2 / 6 * (10 * U / c ^ 2)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a1 hπ) (by norm_num))
          (mul_le_mul_of_nonneg_left a2 hπ) (by positivity) (by positivity)
    _ = 240 * (π ^ 2 / 6) ^ 2 * U ^ 2 / c ^ 4 := by field_simp; ring
    _ = 240 * (π ^ 2 / 6) ^ 2 * G / c ^ 3 := by rw [hUsq]; field_simp

/-- `log y (1 + log y)² ≤ 8y` for `y ≥ 1`. -/
theorem log_cube_le {y : ℝ} (hy : 1 ≤ y) : log y * (1 + log y) ^ 2 ≤ 8 * y := by
  have h1 := Cvs.L2a.NonstationaryPairsAllShifts.one_add_log_sq_le hy
  have hl : 0 ≤ log y := log_nonneg hy
  have hsy : √y ≤ y := by
    rw [sqrt_le_left (by linarith)]; nlinarith
  have h2 : 1 + log y ≤ 2 * √y := by
    have hsq : (1 + log y) ^ 2 ≤ (2 * √y) ^ 2 := by
      rw [mul_pow, sq_sqrt (by linarith)]; nlinarith [h1, hsy]
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp hsq
  calc log y * (1 + log y) ^ 2 ≤ (1 + log y) * (4 * √y) := mul_le_mul (by linarith) h1 (sq_nonneg _) (by linarith)
    _ ≤ (2 * √y) * (4 * √y) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 8 * y := by rw [show (2 * √y) * (4 * √y) = 8 * (√y * √y) by ring, mul_self_sqrt (by linarith)]

/-- The constant of the prime bound. -/
noncomputable def Pc (K : ℝ) : ℝ :=
  2 * ((4 * √(4 * K) + 32 + 32 / 3) * (π ^ 2 / 6) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2
      + 96 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n) + 8 * (√(4 * K) + 16)
    + 4 * (π ^ 2 / 6) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 + 8 * (36 * (π ^ 2 / 6 + 6)))

set_option maxHeartbeats 1000000 in
/-- **The prime bound is `O(G/c)`.** -/
theorem primeBound_le {G : ℝ} (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) (hG : 0 ≤ G) (hK : 0 ≤ K) :
    Cvs.L2a.TailModesTerminalInequality.primeBound c χ G K ≤ G * Pc K / c := by
  have hc0 : 0 < c := by linarith
  have hsc0 : 0 < √c := sqrt_pos.mpr hc0
  have hsc1 : 1 ≤ √c := Real.one_le_sqrt.mpr (by linarith)
  have hscc : √c ≤ c := by rw [sqrt_le_left hc0.le]; nlinarith
  have hss : √(√c) ≤ c := (Real.sqrt_le_sqrt hscc).trans (by rw [sqrt_le_left hc0.le]; nlinarith)
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  set L2 := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 with hL2
  set L3 := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n) with hL3
  have hL20 : 0 ≤ L2 := tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hL30 : 0 ≤ L3 := tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hπ : 0 ≤ π ^ 2 / 6 := by positivity
  set ak := √(4 * K) with hak
  have hak0 : 0 ≤ ak := sqrt_nonneg _
  have hA : Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K ≤ ak / √c := by
    have := Aw_le hc hχ0 hχs hK
    rwa [sqrt_div' _ hc0.le] at this
  have hA0 : 0 ≤ Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K := sqrt_nonneg _
  have hκ := κw_le hc hχ0 hχs
  have hκ0 : 0 ≤ Cvs.L2a.StationaryPairsWeightedTotal.κw c χ := sqrt_nonneg _
  have hQ := Qw_le hc hχ0 hχs
  have hQ0 : 0 ≤ Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ := div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have hα := alpha_ge hc hχ0 hχs
  have hks := kappa_le hc hχ0 hχs
  -- the four pieces
  have b1 : 4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / √c + 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √c / c ^ 2
      + 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ / (3 * c) ≤ (4 * ak + 32 + 32 / 3) / c := by
    have t1 : 4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / √c ≤ 4 * ak / c := by
      calc 4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / √c ≤ 4 * (ak / √c) / √c :=
            div_le_div_of_nonneg_right (by linarith) hsc0.le
        _ = 4 * ak / (√c * √c) := by field_simp
        _ = 4 * ak / c := by rw [hcc]
    have t2 : 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √c / c ^ 2 ≤ 32 / c := by
      rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith [mul_le_mul hκ hscc (le_of_lt hsc0) (by norm_num)]
    have t3 : 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ / (3 * c) ≤ 32 / 3 / c := by
      rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith
    have e : (4 * ak + 32 + 32 / 3) / c = 4 * ak / c + 32 / c + 32 / 3 / c := by ring
    linarith
  have b2 : 48 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √(√c) / c ^ 2 ≤ 96 / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]
    have := mul_le_mul hκ hss (sqrt_nonneg _) (by norm_num)
    nlinarith
  have b3 : (Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c)
      * (log √c * (1 + log √c) ^ 2) ≤ 8 * (ak + 16) / c := by
    have hl := log_cube_le hsc1
    have hl0 : 0 ≤ log √c * (1 + log √c) ^ 2 := mul_nonneg (log_nonneg hsc1) (sq_nonneg _)
    have hsum : Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c ≤ (ak + 16) / (c * √c) := by
      have u1 : Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c ≤ ak / (c * √c) := by
        calc Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c ≤ ak / √c / c := div_le_div_of_nonneg_right hA hc0.le
          _ = ak / (c * √c) := by field_simp
      have u2 : 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c ≤ 16 / (c * √c) := by
        calc 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c ≤ 2 * (8 / c) / √c := div_le_div_of_nonneg_right (by linarith) hsc0.le
          _ = 16 / (c * √c) := by field_simp; ring
      have e : (ak + 16) / (c * √c) = ak / (c * √c) + 16 / (c * √c) := by ring
      linarith
    calc _ ≤ (ak + 16) / (c * √c) * (8 * √c) :=
          mul_le_mul hsum hl (by positivity) (by positivity)
      _ = 8 * (ak + 16) / c := by field_simp
  have b4 : G / (√3 / 2 * √(c ^ 2 - χ)) ≤ 4 * G / c := by
    calc G / (√3 / 2 * √(c ^ 2 - χ)) ≤ G / (c / 4) := div_le_div_of_nonneg_left hG (by positivity) hα
      _ = 4 * G / c := by field_simp
  have b5 : 4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2 ≤ 8 * G / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]
    have h1 := mul_le_mul_of_nonneg_left hks (by positivity : (0 : ℝ) ≤ 4 * G)
    have h2 := mul_le_mul_of_nonneg_right h1 hc0.le
    have h3 : 4 * G * 2 * c ≤ 8 * G * c ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hG hc0.le) (by linarith : (0 : ℝ) ≤ c - 1)]
    linarith
  unfold Cvs.L2a.TailModesTerminalInequality.primeBound Pc
  rw [← hL2, ← hL3, ← hak]
  have m1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right b1 hπ) hL20
  have m2 := mul_le_mul_of_nonneg_right b2 hL30
  have m4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right b4 hπ) hL20
  have m5 := mul_le_mul_of_nonneg_right b5 (by positivity : (0 : ℝ) ≤ 36 * (π ^ 2 / 6 + 6))
  have hin : G * ((4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / √c + 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √c / c ^ 2
          + 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ / (3 * c)) * (π ^ 2 / 6) * L2
        + 48 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √(√c) / c ^ 2 * L3
        + (Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c) * (log √c * (1 + log √c) ^ 2))
      ≤ G * ((4 * ak + 32 + 32 / 3) / c * (π ^ 2 / 6) * L2 + 96 / c * L3 + 8 * (ak + 16) / c) :=
    mul_le_mul_of_nonneg_left (by linarith) hG
  have e : G * ((4 * ak + 32 + 32 / 3) * (π ^ 2 / 6) * L2 + 96 * L3 + 8 * (ak + 16)) / c
      = G * ((4 * ak + 32 + 32 / 3) / c * (π ^ 2 / 6) * L2 + 96 / c * L3 + 8 * (ak + 16) / c) := by
    field_simp
  have e2 : G * (2 * ((4 * ak + 32 + 32 / 3) * (π ^ 2 / 6) * L2 + 96 * L3 + 8 * (ak + 16)
        + 4 * (π ^ 2 / 6) * L2 + 8 * (36 * (π ^ 2 / 6 + 6)))) / c
      = 2 * (G * ((4 * ak + 32 + 32 / 3) * (π ^ 2 / 6) * L2 + 96 * L3 + 8 * (ak + 16)) / c
        + 4 * G / c * (π ^ 2 / 6) * L2 + 8 * G / c * (36 * (π ^ 2 / 6 + 6))) := by
    field_simp
  rw [e2, e]
  linarith

/-- The constant of the Mellin bound. -/
noncomputable def Bm (K : ℝ) : ℝ :=
  √K + 32 * √2 * √K + 64 * √2 + 4 / 3 * (2 * √2 + 2) + π ^ 2 / 6 * (16 / 3) * (4 + √2)

set_option maxHeartbeats 1000000 in
/-- **The Mellin bound below `√c` is `O(√G/c)`**, at `η = 1/c`. -/
theorem mellinBound_le {G ψ1 : ℝ} (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hψ1 : ψ1 ^ 2 ≤ K * G) :
    Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G (1 / c) √c ψ1 ≤ √G * Bm K / c := by
  have hc0 : 0 < c := by linarith
  have hsc0 : 0 < √c := sqrt_pos.mpr hc0
  have hsc1 : 1 ≤ √c := Real.one_le_sqrt.mpr (by linarith)
  have hscc : √c ≤ c := by rw [sqrt_le_left hc0.le]; nlinarith
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  have hsG : 0 ≤ √G := sqrt_nonneg _
  have hσ := sigma_ge hc hχ0 hχs
  have hσ0 : 0 < √(c ^ 2 - χ) := by linarith
  have hα := alpha_ge hc hχ0 hχs
  have hi := inv_sigma_sq_le hc hχ0 hχs
  have hd : 0 < c ^ 2 - χ := by nlinarith [half_sq_le hc hχ0 hχs]
  have hp1 : |ψ1| ≤ √K * √G := by
    rw [← sqrt_mul hK]; exact Real.abs_le_sqrt hψ1
  have hV : √c + 1 / 2 ≤ 2 * √c := by linarith
  have h2 : (0 : ℝ) < √2 := by positivity
  unfold Cvs.L2a.TailModesPoleMellinValues.mellinBound Cvs.Prolate.Mellin.ModeMellinDyadicRange.P
  -- t1
  have t1 : 1 / c * |ψ1| * 1 ≤ √K * √G / c := by
    rw [mul_one, one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hp1 hc0.le
  -- t2
  have t2 : 8 * √2 * |ψ1| * (√c + 1 / 2) / (c * √(c ^ 2 - χ)) ≤ 32 * √2 * √K * √G / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]
    have a := mul_le_mul hp1 hV (by positivity) (by positivity)
    have b : c * √(c ^ 2 - χ) ≥ c * (c / 2) := mul_le_mul_of_nonneg_left hσ hc0.le
    calc 8 * √2 * |ψ1| * (√c + 1 / 2) * c = 8 * √2 * (|ψ1| * (√c + 1 / 2)) * c := by ring
      _ ≤ 8 * √2 * (√K * √G * (2 * √c)) * c := by gcongr
      _ = 16 * √2 * √K * √G * (√c * c) := by ring
      _ ≤ 16 * √2 * √K * √G * (c * c) := by gcongr
      _ = 32 * √2 * √K * √G * (c * (c / 2)) := by ring
      _ ≤ 32 * √2 * √K * √G * (c * √(c ^ 2 - χ)) := by gcongr
  -- t3
  have t3 : 32 * √2 * √(c * G) * 1 / (c ^ 2 - χ) ≤ 64 * √2 * √G / c := by
    rw [mul_one, sqrt_mul hc0.le]
    calc 32 * √2 * (√c * √G) / (c ^ 2 - χ) = 32 * √2 * (√c * √G) * (1 / (c ^ 2 - χ)) := by ring
      _ ≤ 32 * √2 * (√c * √G) * (2 / c ^ 2) := by gcongr
      _ = 64 * √2 * √G * √c / c ^ 2 := by ring
      _ ≤ 64 * √2 * √G * c / c ^ 2 := by gcongr
      _ = 64 * √2 * √G / c := by field_simp
  -- a common size: √(G/(a y)) ≤ 2√G/√c for `a y ≥ c/4`
  have hsq : ∀ y : ℝ, c / 4 ≤ y → √(G / y) ≤ 2 * √G / √c := by
    intro y hy
    have hy0 : 0 < y := by linarith
    rw [sqrt_div' _ hy0.le]
    have : √c / 2 ≤ √y := by
      rw [show √c / 2 = √(c / 4) by rw [sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2 ^ 2 by norm_num,
        sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hy
    rw [div_le_div_iff₀ (by positivity) hsc0]
    nlinarith [mul_le_mul_of_nonneg_left this hsG]
  -- t4
  have t4 : 2 * (8 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) / 1 + 1 * √(2 * c * G * 2))
      / (c ^ 2 * 1 ^ 2 * 2 ^ 2)) ≤ 4 / 3 * (2 * √2 + 2) * √G / c := by
    have hA := hsq (√3 / 2 * √(c ^ 2 - χ) * 2) (by linarith)
    have u1 : (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) ≤ 4 * √G := by
      calc (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) ≤ 2 * √c * (2 * √G / √c) :=
            mul_le_mul hV hA (sqrt_nonneg _) (by positivity)
        _ = 4 * √G := by field_simp; ring
    have u2 : √(2 * c * G * 2) = 2 * √c * √G := by
      rw [show 2 * c * G * 2 = 2 ^ 2 * (c * G) by ring, sqrt_mul (by norm_num), sqrt_sq (by norm_num),
        sqrt_mul hc0.le]; ring
    rw [div_one, one_mul, u2, one_pow, mul_one]
    have hnum : 4 * √G + 2 * √c * √G ≤ (2 * √2 + 2) * √G * c := by
      have : 4 ≤ 2 * √2 * c := by nlinarith [Real.one_lt_sqrt_two]
      nlinarith [mul_le_mul_of_nonneg_right this hsG, mul_le_mul_of_nonneg_left hscc (by positivity : (0:ℝ) ≤ 2 * √G)]
    calc 2 * (8 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ) * 2)) + 2 * √c * √G) / (c ^ 2 * 2 ^ 2))
        ≤ 2 * (8 / 3 * (4 * √G + 2 * √c * √G) / (c ^ 2 * 2 ^ 2)) := by gcongr
      _ ≤ 2 * (8 / 3 * ((2 * √2 + 2) * √G * c) / (c ^ 2 * 2 ^ 2)) := by gcongr
      _ = 4 / 3 * (2 * √2 + 2) * √G / c := by field_simp; ring
  -- t5
  have t5 : π ^ 2 / 6 * (16 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) + 1 * √(2 * c * G)) / c ^ 2)
      ≤ π ^ 2 / 6 * (16 / 3) * (4 + √2) * √G / c := by
    have hA := hsq (√3 / 2 * √(c ^ 2 - χ)) hα
    have u1 : (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) ≤ 4 * √G := by
      calc (√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) ≤ 2 * √c * (2 * √G / √c) :=
            mul_le_mul hV hA (sqrt_nonneg _) (by positivity)
        _ = 4 * √G := by field_simp; ring
    have u2 : √(2 * c * G) = √2 * √c * √G := by rw [sqrt_mul (by positivity), sqrt_mul (by norm_num)]
    rw [one_mul, u2]
    have hnum : 4 * √G + √2 * √c * √G ≤ (4 + √2) * √G * c := by
      nlinarith [mul_le_mul_of_nonneg_left hscc (by positivity : (0:ℝ) ≤ √2 * √G)]
    calc π ^ 2 / 6 * (16 / 3 * ((√c + 1 / 2) * √(G / (√3 / 2 * √(c ^ 2 - χ))) + √2 * √c * √G) / c ^ 2)
        ≤ π ^ 2 / 6 * (16 / 3 * (4 * √G + √2 * √c * √G) / c ^ 2) := by gcongr
      _ ≤ π ^ 2 / 6 * (16 / 3 * ((4 + √2) * √G * c) / c ^ 2) := by gcongr
      _ = π ^ 2 / 6 * (16 / 3) * (4 + √2) * √G / c := by field_simp
  have e : √G * Bm K / c = √K * √G / c + 32 * √2 * √K * √G / c + 64 * √2 * √G / c
      + 4 / 3 * (2 * √2 + 2) * √G / c + π ^ 2 / 6 * (16 / 3) * (4 + √2) * √G / c := by
    unfold Bm; field_simp
  rw [e]
  linarith

/-- The `χ`-free majorant of `X̄`. -/
noncomputable def Xm (c K s : ℝ) : ℝ :=
  12 * √6 * √(4 * K) / (√c * (s * √s)) + (√(4 * K) / (c * √c) + 16 / (c * s)) * (1 + log s)
    + 2 * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (π ^ 2 / 6)
    + 96 * √s / c ^ 2

set_option maxHeartbeats 1000000 in
theorem Xbar_le {s : ℝ} (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχs : χ ≤ c * √c) (hK : 0 ≤ K) (hs : 1 ≤ s) :
    Cvs.L2a.FirstModeHigherModePair.Xbar c χ K s ≤ Xm c K s := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hsc0 : 0 < √c := sqrt_pos.mpr hc0
  have hss0 : 0 < √s := sqrt_pos.mpr hs0
  have hl : 0 ≤ 1 + log s := by have := log_nonneg hs; linarith
  have hA : Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K ≤ √(4 * K) / √c := by
    have := Aw_le hc hχ0 hχs hK; rwa [sqrt_div' _ hc0.le] at this
  have hκ := κw_le hc hχ0 hχs
  have hκ0 : 0 ≤ Cvs.L2a.StationaryPairsWeightedTotal.κw c χ := sqrt_nonneg _
  have hQ := Qw_le hc hχ0 hχs
  have h6 : √(6 / s) = √6 / √s := sqrt_div' _ hs0.le
  unfold Cvs.L2a.FirstModeHigherModePair.Xbar Xm
  have t1 : 4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / s * (3 * √(6 / s)) ≤ 12 * √6 * √(4 * K) / (√c * (s * √s)) := by
    rw [h6]
    calc 4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / s * (3 * (√6 / √s))
        ≤ 4 * (√(4 * K) / √c) / s * (3 * (√6 / √s)) := by gcongr
      _ = 12 * √6 * √(4 * K) / (√c * (s * √s)) := by field_simp; ring
  have t2 : (Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / s) * (1 + log s)
      ≤ (√(4 * K) / (c * √c) + 16 / (c * s)) * (1 + log s) := by
    apply mul_le_mul_of_nonneg_right _ hl
    have u1 : Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c ≤ √(4 * K) / (c * √c) := by
      calc Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c ≤ √(4 * K) / √c / c := by gcongr
        _ = √(4 * K) / (c * √c) := by field_simp
    have u2 : 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / s ≤ 16 / (c * s) := by
      calc 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / s ≤ 2 * (8 / c) / s := by gcongr
        _ = 16 / (c * s) := by field_simp; ring
    linarith
  have t3 : Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (π ^ 2 / 6)
      ≤ 2 * (16 * s * √c / (3 * c ^ 2) + 16 * s / c ^ 2 + 16 * s / (3 * c ^ 2)) * (π ^ 2 / 6) := by
    gcongr
  have t4 : 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √s / c ^ 2 * 3 ≤ 96 * √s / c ^ 2 := by
    calc 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √s / c ^ 2 * 3 ≤ 16 * 2 * √s / c ^ 2 * 3 := by gcongr
      _ = 96 * √s / c ^ 2 := by ring
  linarith

end Cvs.Prolate.Envelope.ProlateWeightSizes
