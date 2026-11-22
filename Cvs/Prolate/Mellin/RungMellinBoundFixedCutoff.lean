import Mathlib
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.Prolate.Mellin.ModeMellinDyadicRange

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin bound at a fixed cutoff, with `σ` in one term

For `c ≥ 1`, `c² − χ ≥ 1`, `T ≥ 0`, `ψ(1)² ≤ KG`, at `η = 1/c`: `TailModesPoleMellinValues`'s Mellin bound is at most
`√G(E/c + 32√2√c/(c² − χ))`, `E = √K + 8√2√K V + (4/3)(V + 2) + (16√2/3)(π²/6)(V + 1)`, `V = T + 1/2`.
-/

namespace Cvs.Prolate.Mellin.RungMellinBoundFixedCutoff

open Real

/-- The `σ`-free part of the Mellin constant. -/
noncomputable def E (K T : ℝ) : ℝ :=
  √K + 8 * √2 * √K * (T + 1 / 2) + 4 / 3 * (T + 1 / 2 + 2) + 16 * √2 / 3 * (π ^ 2 / 6) * (T + 1 / 2 + 1)

set_option maxHeartbeats 1000000 in
/-- **The Mellin bound at `η = 1/c`, cutoff `T`**: at most `√G(E/c + 32√2√c/(c² − χ))`. -/
theorem mellinBound_le {c χ G K T ψ1 : ℝ} (hc : 1 ≤ c) (hσ : 1 ≤ c ^ 2 - χ) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hψ1 : ψ1 ^ 2 ≤ K * G) :
    Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G (1 / c) T ψ1 ≤ √G * (E K T / c + 32 * √2 * √c / (c ^ 2 - χ)) := by
  have hc0 : 0 < c := by linarith
  have hsG : 0 ≤ √G := sqrt_nonneg _
  have hsK : 0 ≤ √K := sqrt_nonneg _
  have habs : |ψ1| ≤ √K * √G := by
    rw [← sqrt_mul' _ hG]; exact Real.abs_le_sqrt hψ1
  have hd0 : 0 < c ^ 2 - χ := by linarith
  set σ := √(c ^ 2 - χ) with hσdef
  have hσ1 : 1 ≤ σ := by rw [hσdef, show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt hσ
  set V := T + 1 / 2 with hV
  have hV0 : 0 ≤ V := by positivity
  have hsc : √c ≤ c := by rw [sqrt_le_left hc0.le]; nlinarith
  have hs3 : 1 ≤ √3 := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by norm_num)
  unfold Cvs.L2a.TailModesPoleMellinValues.mellinBound Cvs.Prolate.Mellin.ModeMellinDyadicRange.P
  rw [← hσdef, ← hV]
  -- term 1
  have M1 : 1 / c * |ψ1| * 1 ≤ √K * √G / c := by
    rw [mul_one, one_div_mul_eq_div]; exact div_le_div_of_nonneg_right habs hc0.le
  -- term 2
  have M2 : 8 * √2 * |ψ1| * V / (c * σ) ≤ 8 * √2 * √K * V * √G / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]
    calc 8 * √2 * |ψ1| * V * c ≤ 8 * √2 * (√K * √G) * V * c := by gcongr
      _ = 8 * √2 * √K * V * √G * (c * 1) := by ring
      _ ≤ 8 * √2 * √K * V * √G * (c * σ) := by gcongr
  -- term 3
  have M3 : 32 * √2 * √(c * G) * 1 / (c ^ 2 - χ) = √G * (32 * √2 * √c / (c ^ 2 - χ)) := by
    rw [sqrt_mul hc0.le]; ring
  -- term 4
  have hq1 : √(G / (√3 / 2 * σ * 2)) ≤ √G := by
    apply sqrt_le_sqrt; apply div_le_self hG; nlinarith
  have hq2 : √(2 * c * G * 2) ≤ 2 * c * √G := by
    rw [show 2 * c * G * 2 = 2 ^ 2 * (c * G) by ring, sqrt_mul (by norm_num), sqrt_sq (by norm_num),
      sqrt_mul hc0.le]
    nlinarith
  have M4 : 2 * (8 / 3 * (V * √(G / (√3 / 2 * σ * 2)) / 1 + 1 * √(2 * c * G * 2)) / (c ^ 2 * 1 ^ 2 * 2 ^ 2))
      ≤ 4 / 3 * (V + 2) * √G / c := by
    have h1 : V * √(G / (√3 / 2 * σ * 2)) / 1 + 1 * √(2 * c * G * 2) ≤ (V + 2) * c * √G := by
      have := mul_le_mul_of_nonneg_left hq1 hV0
      have hVc : V * √G ≤ V * c * √G := by nlinarith [mul_nonneg hV0 hsG]
      rw [div_one]; nlinarith
    calc 2 * (8 / 3 * (V * √(G / (√3 / 2 * σ * 2)) / 1 + 1 * √(2 * c * G * 2)) / (c ^ 2 * 1 ^ 2 * 2 ^ 2))
        ≤ 2 * (8 / 3 * ((V + 2) * c * √G) / (c ^ 2 * 1 ^ 2 * 2 ^ 2)) := by gcongr
      _ = 4 / 3 * (V + 2) * √G / c := by field_simp; ring
  -- term 5
  have hq3 : √(G / (√3 / 2 * σ)) ≤ √2 * √G := by
    rw [← sqrt_mul (by norm_num)]
    apply sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have h3 : 1 ≤ √3 * σ := by nlinarith
    have := mul_le_mul_of_nonneg_left h3 hG
    nlinarith
  have hq4 : √(2 * c * G) ≤ √2 * c * √G := by
    rw [show 2 * c * G = 2 * (c * G) by ring, sqrt_mul (by norm_num), sqrt_mul hc0.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsc (sqrt_nonneg 2)) hsG
  have M5 : π ^ 2 / 6 * (16 / 3 * (V * √(G / (√3 / 2 * σ)) + 1 * √(2 * c * G)) / c ^ 2)
      ≤ 16 * √2 / 3 * (π ^ 2 / 6) * (V + 1) * √G / c := by
    have h1 : V * √(G / (√3 / 2 * σ)) + 1 * √(2 * c * G) ≤ √2 * (V + 1) * c * √G := by
      have := mul_le_mul_of_nonneg_left hq3 hV0
      have h2 : 0 ≤ √2 * V * √G := by positivity
      have hVc : √2 * V * √G ≤ √2 * V * √G * c := le_mul_of_one_le_right h2 hc
      nlinarith
    calc π ^ 2 / 6 * (16 / 3 * (V * √(G / (√3 / 2 * σ)) + 1 * √(2 * c * G)) / c ^ 2)
        ≤ π ^ 2 / 6 * (16 / 3 * (√2 * (V + 1) * c * √G) / c ^ 2) := by gcongr
      _ = 16 * √2 / 3 * (π ^ 2 / 6) * (V + 1) * √G / c := by field_simp
  have e : √G * (E K T / c + 32 * √2 * √c / (c ^ 2 - χ))
      = √K * √G / c + 8 * √2 * √K * V * √G / c + √G * (32 * √2 * √c / (c ^ 2 - χ))
        + 4 / 3 * (V + 2) * √G / c + 16 * √2 / 3 * (π ^ 2 / 6) * (V + 1) * √G / c := by
    unfold E; rw [← hV]; ring
  rw [e, ← M3]
  linarith

end Cvs.Prolate.Mellin.RungMellinBoundFixedCutoff
