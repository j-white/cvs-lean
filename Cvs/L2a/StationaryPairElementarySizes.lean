import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.Envelope.ProlateWeightToEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The elementary sizes behind a stationary pair's bound

For `k ≥ 1`, `m ≥ 1`, `S = k² + 1/m²`: `1/(3km²) ≤ √S − k ≤ 1/(2km²)`; `ew(ξ) ≥ ξ − 1` on `[1, ∞)` and
`ew(ξ) ≥ (√3/2) ξ²` on `[2, ∞)`; `p_m(t) ≤ t²` and `p_{1/k}(t) = t² − k²`.
-/

namespace Cvs.L2a.StationaryPairElementarySizes

open Real Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge

theorem sqrtS_sub_le {k m : ℝ} (hk : 0 < k) (hm : 0 < m) :
    √(k ^ 2 + 1 / m ^ 2) - k ≤ 1 / (2 * k * m ^ 2) := by
  have hm2' : 0 ≤ 1 / m ^ 2 := by positivity
  have hS : k ≤ √(k ^ 2 + 1 / m ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have hsq : √(k ^ 2 + 1 / m ^ 2) ^ 2 = k ^ 2 + 1 / m ^ 2 := sq_sqrt (by positivity)
  -- (√S − k)(√S + k) = 1/m², and √S + k ≥ 2k
  have e : (√(k ^ 2 + 1 / m ^ 2) - k) * (√(k ^ 2 + 1 / m ^ 2) + k) = 1 / m ^ 2 := by nlinarith
  have h2k : 2 * k ≤ √(k ^ 2 + 1 / m ^ 2) + k := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hnn : 0 ≤ √(k ^ 2 + 1 / m ^ 2) - k := by linarith
  calc (√(k ^ 2 + 1 / m ^ 2) - k) * (2 * k * m ^ 2)
      ≤ (√(k ^ 2 + 1 / m ^ 2) - k) * ((√(k ^ 2 + 1 / m ^ 2) + k) * m ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hnn; nlinarith [sq_nonneg m]
    _ = 1 := by rw [← mul_assoc, e]; field_simp

theorem le_sqrtS_sub {k m : ℝ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    1 / (3 * k * m ^ 2) ≤ √(k ^ 2 + 1 / m ^ 2) - k := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hm2' : 0 ≤ 1 / m ^ 2 := by positivity
  have hS : k ≤ √(k ^ 2 + 1 / m ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have hsq : √(k ^ 2 + 1 / m ^ 2) ^ 2 = k ^ 2 + 1 / m ^ 2 := sq_sqrt (by positivity)
  have hup : √(k ^ 2 + 1 / m ^ 2) ≤ 2 * k := by
    rw [Real.sqrt_le_left (by positivity)]
    have : 1 / m ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    nlinarith
  have e : (√(k ^ 2 + 1 / m ^ 2) - k) * (√(k ^ 2 + 1 / m ^ 2) + k) = 1 / m ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hpos : 0 < √(k ^ 2 + 1 / m ^ 2) + k := by linarith
  -- (√S − k) = (1/m²)/(√S + k) ≥ (1/m²)/(3k)
  have h3 : √(k ^ 2 + 1 / m ^ 2) + k ≤ 3 * k := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  calc (1 : ℝ) = (√(k ^ 2 + 1 / m ^ 2) - k) * (√(k ^ 2 + 1 / m ^ 2) + k) * m ^ 2 := by
        rw [e]; field_simp
    _ ≤ (√(k ^ 2 + 1 / m ^ 2) - k) * (3 * k) * m ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hm2.le
        exact mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = (√(k ^ 2 + 1 / m ^ 2) - k) * (3 * k * m ^ 2) := by ring

theorem ew_ge_sub {ξ : ℝ} (h : 1 ≤ ξ) : ξ - 1 ≤ ew ξ := by
  unfold ew
  have h1 : ξ - 1 ≤ √(ξ ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : √(ξ ^ 2 - 1) ≤ ξ * √(ξ ^ 2 - 1) := le_mul_of_one_le_left (sqrt_nonneg _) h
  linarith

theorem ew_ge_sq {ξ : ℝ} (h : 2 ≤ ξ) : √3 / 2 * ξ ^ 2 ≤ ew ξ := by
  unfold ew
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h1 : √3 / 2 * ξ ≤ √(ξ ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  nlinarith [sqrt_nonneg 3]

theorem pm_le {m t : ℝ} (hm : m ≠ 0) : pm m t ≤ t ^ 2 := by
  unfold pm; rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (m * t)]

theorem pm_inv {k t : ℝ} (hk : k ≠ 0) : pm (1 / k) t = t ^ 2 - k ^ 2 := by
  unfold pm; field_simp

end Cvs.L2a.StationaryPairElementarySizes
