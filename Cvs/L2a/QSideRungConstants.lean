import Mathlib
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.LowRungFullTail
import Cvs.L2a.LowRungHighSpectralMass
import Cvs.L2a.LowRungTruncationRate
import Cvs.L2a.PositionTailEdgeRow
import Cvs.Prolate.RungTailIntegralMass
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The q-side's rung constants are absolute

For `c ≥ 100`: `Khigh(c) ≤ 80000`, `Krate(c) ≤ 72000`, `Kfr(c) ≤ 100`, `C_π(2, c) ≤ 2`, and `a(2c) ≤ 6 + log c`.
Every amplitude is `√c` or `1/√c` times an absolute constant, so each constant is bounded uniformly in `c`.
-/

noncomputable section

open Real

namespace Cvs.L2a.QSideRungConstants

/-- `√a ≤ b` from `a ≤ b²`, `0 ≤ b`. -/
theorem sqrt_le_of_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : √a ≤ b :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hb)

/-- The four rung amplitudes at `c ≥ 100`, `u = √c`. -/
theorem amps {c : ℝ} (hc : 100 ≤ c) :
    10 ≤ √c ∧ √c ^ 2 = c ∧ √c ≤ c / 10 ∧
    2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c) ≤ 17 * √c ∧ 0 ≤ 2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c) ∧
    √(64 * exp 1 / c) ≤ 14 / √c ∧ √(256 / 3 * exp 1 * c) ≤ 16 * √c ∧
    √(64 * exp 1 / c) * √(256 / 3 * exp 1 * c) ≤ 224 ∧ exp 1 ≤ 3 := by
  have hc0 : 0 < c := by linarith
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hu2 : √c ^ 2 = c := Real.sq_sqrt hc0.le
  have hu : 10 ≤ √c := by
    rw [show (10 : ℝ) = √(10 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]; exact Real.sqrt_le_sqrt (by linarith)
  have hu0 : 0 < √c := by linarith
  have hr : (2 : ℝ) ^ (-(3/4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) ≤ 2 ^ (-(3/4) : ℝ) := by positivity
  have h96 : √(96 * exp 1 * c) ≤ 17 * √c := sqrt_le_of_le_sq (by positivity) (by nlinarith)
  have hB : √(64 * exp 1 / c) ≤ 14 / √c := sqrt_le_of_le_sq (by positivity) (by
    rw [div_pow, hu2]; exact div_le_div_of_nonneg_right (by nlinarith) hc0.le)
  have hD : √(256 / 3 * exp 1 * c) ≤ 16 * √c := sqrt_le_of_le_sq (by positivity) (by nlinarith)
  refine ⟨hu, hu2, ?_, ?_, by positivity, hB, hD, ?_, by linarith⟩
  · rw [le_div_iff₀ (by norm_num)]; nlinarith
  · calc 2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c) ≤ 1 * (17 * √c) := mul_le_mul hr h96 (by positivity) zero_le_one
      _ = 17 * √c := one_mul _
  · calc √(64 * exp 1 / c) * √(256 / 3 * exp 1 * c) ≤ (14 / √c) * (16 * √c) :=
          mul_le_mul hB hD (by positivity) (by positivity)
      _ = 224 := by field_simp; norm_num

/-- **`Khigh(c) ≤ 80000`** for `c ≥ 100`. -/
theorem Khigh_le {c : ℝ} (hc : 100 ≤ c) : Cvs.L2a.LowRungHighSpectralMass.Khigh c ≤ 80000 := by
  obtain ⟨hu, hu2, -, ht, ht0, -, -, -, he⟩ := amps hc
  have hc0 : 0 < c := by linarith
  set t := 2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)
  unfold Cvs.L2a.LowRungHighSpectralMass.Khigh
  rw [div_le_iff₀ hc0]
  have h1 : (6 + 4 * (4 * t)) ^ 2 ≤ 74529 * c := by
    have : 6 + 4 * (4 * t) ≤ 273 * √c := by nlinarith
    nlinarith
  have h2 : 74 ^ 2 * (48 * exp 1 / c) * 25 ≤ 1972 * c := by
    rw [show 74 ^ 2 * (48 * exp 1 / c) * 25 = 74 ^ 2 * 48 * 25 * exp 1 / c by ring, div_le_iff₀ hc0]
    nlinarith
  nlinarith

/-- **The edge-row constant at the rung amplitudes is at most `25`** for `c ≥ 100`. -/
theorem rowC_le {c : ℝ} (hc : 100 ≤ c) :
    Cvs.L2a.PositionTailEdgeRow.rowC c 1 (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c))) (√(64 * exp 1 / c))
      (√(256 / 3 * exp 1 * c)) (9 / 10) ≤ 25 := by
  obtain ⟨hu, hu2, huc, ht, ht0, hB, hD, hBD, he⟩ := amps hc
  have hc0 : 0 < c := by linarith
  set u := √c
  set t := 2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)
  set B := √(64 * exp 1 / c)
  set D := √(256 / 3 * exp 1 * c)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  unfold Cvs.L2a.PositionTailEdgeRow.rowC
  -- the edge part
  have hDA : D * (6 * 1 / (9 / 10) + 2 * (4 * t) / (9 / 10) + 2 * 1 / (9 / 10) ^ 2) ≤ 2433 * c := by
    have hDt : D * t ≤ 272 * c := by
      calc D * t ≤ (16 * u) * (17 * u) := mul_le_mul hD ht ht0 (by positivity)
        _ = 272 * c := by rw [← hu2]; ring
    have hDu : D ≤ 16 * (c / 10) := hD.trans (by linarith)
    nlinarith
  have e1 : D * (6 * 1 / (9 / 10) + 2 * (4 * t) / (9 / 10) + 2 * 1 / (9 / 10) ^ 2) / c ^ 2 ≤ 2433 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e2 : 7 / 3 * (B * D) / c ^ 2 ≤ 1 / 10 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e3 : B ^ 2 / 18 ≤ 1 / 2 := by
    have hB2 : B ^ 2 ≤ 196 / c := by
      calc B ^ 2 ≤ (14 / u) ^ 2 := pow_le_pow_left₀ hB0 hB 2
        _ = 196 / c := by rw [div_pow, hu2]; norm_num
    have : 196 / c ≤ 2 := by rw [div_le_iff₀ hc0]; linarith
    linarith
  linarith

/-- **`Krate(c) ≤ 72000`** for `c ≥ 100`. -/
theorem Krate_le {c : ℝ} (hc : 100 ≤ c) : Cvs.L2a.LowRungTruncationRate.Krate c ≤ 72000 := by
  obtain ⟨hu, hu2, -, -, -, -, -, hBD, he⟩ := amps hc
  have hc0 : 0 < c := by linarith
  have hr := rowC_le hc
  unfold Cvs.L2a.LowRungTruncationRate.Krate
  have e1 : 400 * exp 1 / c ≤ 12 := by rw [div_le_iff₀ hc0]; nlinarith
  have e2 : 64 * exp 1 / c ≤ 2 := by rw [div_le_iff₀ hc0]; nlinarith
  have e3 : √(64 * exp 1 / c) * √(256 / 3 * exp 1 * c) / c ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`Kfr(c) ≤ 100`** for `c ≥ 100`. -/
theorem Kfr_le {c : ℝ} (hc : 100 ≤ c) : Cvs.L2a.LowRungFullTail.Kfr c ≤ 100 := by
  obtain ⟨hu, hu2, -, -, -, -, -, hBD, he⟩ := amps hc
  have hc0 : 0 < c := by linarith
  have hr := rowC_le hc
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hp : π ^ 2 / 6 ≤ 5 / 3 := by nlinarith
  have hp0 : 0 ≤ π ^ 2 / 6 := by positivity
  unfold Cvs.L2a.LowRungFullTail.Kfr
  have e2 : 64 * exp 1 / c ≤ 2 := by rw [div_le_iff₀ hc0]; nlinarith
  have e20 : 0 ≤ 64 * exp 1 / c := by positivity
  have e3 : 14 / 3 * (√(64 * exp 1 / c) * √(256 / 3 * exp 1 * c)) / c ^ 2 ≤ 1 / 5 := by
    have hc2 : 10000 ≤ c ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hr0 : 0 ≤ Cvs.L2a.PositionTailEdgeRow.rowC c 1 (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)))
      (√(64 * exp 1 / c)) (√(256 / 3 * exp 1 * c)) (9 / 10) := by
    unfold Cvs.L2a.PositionTailEdgeRow.rowC; positivity
  have a1 : π ^ 2 / 6 * (64 * exp 1 / c) ≤ 5 / 3 * 2 := mul_le_mul hp e2 e20 (by norm_num)
  have a2 : 2 * (π ^ 2 / 6) * Cvs.L2a.PositionTailEdgeRow.rowC c 1 (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)))
      (√(64 * exp 1 / c)) (√(256 / 3 * exp 1 * c)) (9 / 10) ≤ 2 * (5 / 3) * 25 :=
    mul_le_mul (by linarith) hr hr0 (by norm_num)
  have a4 : 16 / 9 * (π ^ 2 / 6) ^ 2 * (64 * exp 1 / c) ≤ 16 / 9 * (5 / 3) ^ 2 * 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2) (by norm_num)) e2 e20 (by norm_num)
  linarith

/-- **`C_π(2, c) ≤ 2`** for `c ≥ 100`. -/
theorem piConst_two_le {c : ℝ} (hc : 100 ≤ c) : Cvs.Prolate.RungTailIntegralMass.piConst 2 c ≤ 2 := by
  have hc0 : 0 < c := by linarith
  unfold Cvs.Prolate.RungTailIntegralMass.piConst
  have h5 : 1 / √5 ≤ 1 := by
    rw [div_le_one (by positivity)]
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have h12 : √(6 * 2) ≤ 4 := sqrt_le_of_le_sq (by norm_num) (by norm_num)
  have : 3 * √(6 * 2) / c * (30 / 11 + 3 / 4) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hc0]
    calc 3 * √(6 * 2) * (30 / 11 + 3 / 4) ≤ 3 * 4 * (30 / 11 + 3 / 4) := by gcongr
      _ ≤ c := by linarith
  linarith

/-- **The archimedean symbol at `2c`**: `a(2c) ≤ 6 + log c` for `c ≥ 1`. -/
theorem archSymbol_two_mul_le {c : ℝ} (hc : 1 ≤ c) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c) ≤ 6 + Real.log c := by
  have hlog := Real.log_nonneg hc
  have hc0 : 0 < c := by linarith
  rcases le_or_gt |2 * c| 1024 with h | h
  · have := Cvs.L2a.BetaProfilePoissonTail.abs_archSymbol_le_of_abs_le h
    linarith [le_abs_self (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c))]
  · have := Cvs.L2a.BetaProfilePoissonTail.abs_archSymbol_le_log h.le
    have h2 : |2 * c| = 2 * c := abs_of_pos (by linarith)
    rw [h2, show 2 * c / 2 = c by ring] at this
    linarith [le_abs_self (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c))]

end Cvs.L2a.QSideRungConstants
