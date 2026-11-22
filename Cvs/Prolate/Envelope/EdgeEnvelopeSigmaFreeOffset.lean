import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.StationaryEnvelopeMonotone
import Cvs.L2a.StationaryMismatchExactRoots
import Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi
import Cvs.Prolate.Envelope.ProlateWeightToEdge
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Prolate envelopes at the edge without `σ`, and the exact offset of the stationary point

For `ξ ≥ 1` and `χ ≤ c²`, `q = c²p + (c² − χ) ≥ c²p`, so `a = √(pq) ≥ cp` and `ψ(ξ)² ≤ G/(c(ξ² − 1))`, whatever
`σ = √(c² − χ)`; with the flux bound `u² ≤ c ew G`, `|u(ξ₁)ψ(ξ₂)| ≤ G√(ew(ξ₁)/(ξ₂² − 1))`. The stationary point sits at
`T₊ = k² + y` with `y(k² − 1/m² + y) = ℓk²/m²` exactly, `ℓ = (c² − χ)/c²`, so `y ≤ ℓk²/(k²m² − 1)`.
-/

namespace Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset

open Real Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryMismatchExactRoots

variable {c χ : ℝ}

/-- **`a ≥ c(ξ² − 1)`** for `ξ ≥ 1`, `χ ≤ c²`. -/
theorem aP_ge_cp {ξ : ℝ} (hχc : χ ≤ c ^ 2) (hξ : 1 ≤ ξ) : c * (ξ ^ 2 - 1) ≤ aP c χ ξ := by
  unfold aP pP qP
  apply Real.le_sqrt_of_sq_le
  have hp : 0 ≤ ξ ^ 2 - 1 := by nlinarith
  have hq : c ^ 2 * (ξ ^ 2 - 1) ≤ c ^ 2 * ξ ^ 2 - χ := by nlinarith
  have := mul_le_mul_of_nonneg_left hq hp
  nlinarith

/-- **The edge envelope**: `ψ(ξ)² ≤ G/(c(ξ² − 1))` for `ξ > 1`. -/
theorem psi_sq_le_edge {G ξ : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hξ : 1 < ξ)
    (hG : energy (aP c χ) ψ u ξ ≤ G) : ψ ξ ^ 2 ≤ G / (c * (ξ ^ 2 - 1)) := by
  have ha := aP_ge_cp hχc.le hξ.le
  have hp : 0 < c * (ξ ^ 2 - 1) := by have : 0 < ξ ^ 2 - 1 := by nlinarith
                                      positivity
  have hapos : 0 < aP c χ ξ := lt_of_lt_of_le hp ha
  have hE : aP c χ ξ * ψ ξ ^ 2 ≤ G := by
    unfold energy at hG
    have : 0 ≤ u ξ ^ 2 / aP c χ ξ := by positivity
    linarith
  rw [le_div_iff₀ hp]
  calc ψ ξ ^ 2 * (c * (ξ ^ 2 - 1)) ≤ ψ ξ ^ 2 * aP c χ ξ := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
    _ ≤ G := by linarith

/-- **The flux–value envelope**: `|u_a(ξ₁)ψ_b(ξ₂)| ≤ G√(ew(ξ₁)/(ξ₂² − 1))` for `ξ₁, ξ₂ > 1`. -/
theorem flux_val_le {χa χb G ξ₁ ξ₂ : ℝ} {ψa ua ψb ub : ℝ → ℝ} (hc : 0 < c) (hχa0 : 0 ≤ χa)
    (hχa : χa < c ^ 2) (hχb : χb < c ^ 2) (h₁ : 1 < ξ₁) (h₂ : 1 < ξ₂)
    (hGa : energy (aP c χa) ψa ua ξ₁ ≤ G) (hGb : energy (aP c χb) ψb ub ξ₂ ≤ G) :
    |ua ξ₁ * ψb ξ₂| ≤ G * √(ew ξ₁ / (ξ₂ ^ 2 - 1)) := by
  have e1 := Cvs.Prolate.Envelope.ProlateEnvelopeBoundedChi.flux_sq_le hc hχa0 hχa h₁ hGa
  have e2 := psi_sq_le_edge (u := ub) hc hχb h₂ hGb
  have hG : 0 ≤ G := by
    have := two_mul_abs_le_energy (ψ := ψa) (u := ua) (aP_pos h₁ (by positivity) hχa)
    linarith [abs_nonneg (ψa ξ₁ * ua ξ₁)]
  have hp : 0 < ξ₂ ^ 2 - 1 := by nlinarith
  have hew : 0 < ew ξ₁ := Cvs.L2a.StationaryEnvelopeMonotone.ew_pos h₁
  rw [← sqrt_sq_eq_abs, show G * √(ew ξ₁ / (ξ₂ ^ 2 - 1)) = √(G ^ 2 * (ew ξ₁ / (ξ₂ ^ 2 - 1))) by
    rw [sqrt_mul (sq_nonneg _), sqrt_sq hG]]
  apply sqrt_le_sqrt
  calc (ua ξ₁ * ψb ξ₂) ^ 2 = ua ξ₁ ^ 2 * ψb ξ₂ ^ 2 := by ring
    _ ≤ c * ew ξ₁ * G * (G / (c * (ξ₂ ^ 2 - 1))) := mul_le_mul e1 e2 (sq_nonneg _) (by positivity)
    _ = G ^ 2 * (ew ξ₁ / (ξ₂ ^ 2 - 1)) := by field_simp

/-- **The exact offset of the stationary point**: `y = T₊ − k²` satisfies `y(k² − 1/m² + y) = ℓk²/m²`. -/
theorem Tp_offset_eq {k m : ℝ} (hc : 0 < c) (hm : 0 < m) (hΔ : 0 ≤ disc c χ k m) :
    (Tp c χ k m - k ^ 2) * (k ^ 2 - 1 / m ^ 2 + (Tp c χ k m - k ^ 2)) = (c ^ 2 - χ) / c ^ 2 * k ^ 2 / m ^ 2 := by
  have h1 := Tp_add_Tm (c := c) (χ := χ) (k := k) (m := m)
  have h2 := Tp_mul_Tm (k := k) hc hm hΔ
  have hTm : Tm c χ k m = k ^ 2 + 1 / m ^ 2 - Tp c χ k m := by linarith
  rw [hTm] at h2
  have e : (Tp c χ k m - k ^ 2) * (k ^ 2 - 1 / m ^ 2 + (Tp c χ k m - k ^ 2))
      = Tp c χ k m * (k ^ 2 + 1 / m ^ 2 - Tp c χ k m) * (-1) + k ^ 2 / m ^ 2 := by ring
  rw [e, h2]; field_simp; ring

/-- **The stationary point is `ℓk²/(k²m² − 1)` above `k²`**: `T₊ − k² ≤ ℓk²/(k²m² − 1)`, `ℓ = (c² − χ)/c²`. -/
theorem Tp_sub_le {k m : ℝ} (hc : 0 < c) (hk : 0 < k) (hm : 0 < m) (hkm : 1 < m * k) (hχ0 : 0 ≤ χ)
    (hχc : χ ≤ c ^ 2) :
    Tp c χ k m - k ^ 2 ≤ (c ^ 2 - χ) / c ^ 2 * k ^ 2 / (k ^ 2 * m ^ 2 - 1) := by
  have hΔ : 0 ≤ disc c χ k m := le_trans (sq_nonneg _) (disc_ge hc hm hχc)
  have heq := Tp_offset_eq hc hm hΔ
  have hy : 0 ≤ Tp c χ k m - k ^ 2 := by
    have := Tp_ge hc hk hm hkm.le hχ0 hχc
    have : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
    linarith
  have hkm2 : 0 < k ^ 2 * m ^ 2 - 1 := by nlinarith
  have hk2 : 0 < k ^ 2 - 1 / m ^ 2 := by
    have : k ^ 2 - 1 / m ^ 2 = (k ^ 2 * m ^ 2 - 1) / m ^ 2 := by field_simp
    rw [this]; positivity
  have hℓ : 0 ≤ (c ^ 2 - χ) / c ^ 2 := div_nonneg (by linarith) (by positivity)
  rw [le_div_iff₀ hkm2]
  have h1 : (Tp c χ k m - k ^ 2) * (k ^ 2 - 1 / m ^ 2) ≤ (c ^ 2 - χ) / c ^ 2 * k ^ 2 / m ^ 2 := by
    rw [← heq]; nlinarith [mul_nonneg hy hy]
  have e : (Tp c χ k m - k ^ 2) * (k ^ 2 * m ^ 2 - 1) = (Tp c χ k m - k ^ 2) * (k ^ 2 - 1 / m ^ 2) * m ^ 2 := by
    field_simp
  rw [e]
  calc (Tp c χ k m - k ^ 2) * (k ^ 2 - 1 / m ^ 2) * m ^ 2 ≤ (c ^ 2 - χ) / c ^ 2 * k ^ 2 / m ^ 2 * m ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (c ^ 2 - χ) / c ^ 2 * k ^ 2 := by field_simp

end Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset
