import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sign of a stationary pair's mismatch on either side of `√(k² + 1/m²)`

For the pair of modes `m` and `1/k`, `D = (m² − 1/k²) E` with `E(t) = c²t²(t² − S) + χk²/m²`, `S = k² + 1/m²`.
Past `√S + δ`, `E ≥ 2c²t²√S δ`; before `√S − δ` (and after `k`), `E ≤ −c²t² k δ` once `δ ≥ χ/(c²m²k)`.
The windows of Cvs.L2a.StationaryCrossPairSplit are therefore explicit, with no root to locate.
-/

namespace Cvs.L2a.StationaryPairMismatchSign

open Real

/-- The stationary mismatch `E(t) = c²t²(t² − k² − 1/m²) + χk²/m²`. -/
noncomputable def Est (c χ k m t : ℝ) : ℝ := c ^ 2 * t ^ 2 * (t ^ 2 - (k ^ 2 + 1 / m ^ 2)) + χ * k ^ 2 / m ^ 2

/-- `D = (m² − 1/k²) E` for the pair `(m, 1/k)`. -/
theorem Dmr_eq_Est {c χ k m t : ℝ} (hk : k ≠ 0) (hm : m ≠ 0) :
    Cvs.L2a.NonresonantCrossIntegral.Dmr c χ m (1 / k) t = (m ^ 2 - 1 / k ^ 2) * Est c χ k m t := by
  rw [Cvs.L2a.NonstationaryCrossPairClosed.Dmr_eq hm (by positivity)]
  unfold Est; field_simp; ring

/-- **Right of the window**: `t ≥ √S + δ`, `0 ≤ χ`, `0 < δ` give `E(t) ≥ 2c²t²√S δ`. -/
theorem Est_right {c χ k m t δ : ℝ} (hχ : 0 ≤ χ) (hδ : 0 < δ) (hm : m ≠ 0)
    (ht : √(k ^ 2 + 1 / m ^ 2) + δ ≤ t) :
    2 * c ^ 2 * t ^ 2 * √(k ^ 2 + 1 / m ^ 2) * δ ≤ Est c χ k m t := by
  set S := k ^ 2 + 1 / m ^ 2
  have hS : 0 ≤ S := by positivity
  have hsS : 0 ≤ √S := sqrt_nonneg S
  have hsq : √S ^ 2 = S := sq_sqrt hS
  have h1 : 2 * √S * δ ≤ t ^ 2 - S := by nlinarith
  unfold Est
  have : 0 ≤ χ * k ^ 2 / m ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ c ^ 2 * t ^ 2)
  nlinarith

/-- **Left of the window**: `k ≤ t ≤ √S − δ`, `0 < k`, `χ/(c² m² k) ≤ δ` give `E(t) ≤ −c²t²kδ`. -/
theorem Est_left {c χ k m t δ : ℝ} (hc : 0 < c) (hk : 0 < k) (hm : m ≠ 0) (hδ : 0 < δ)
    (hδχ : χ / (c ^ 2 * m ^ 2 * k) ≤ δ) (hkt : k ≤ t) (ht : t ≤ √(k ^ 2 + 1 / m ^ 2) - δ) :
    Est c χ k m t ≤ -(c ^ 2 * t ^ 2 * k * δ) := by
  set S := k ^ 2 + 1 / m ^ 2
  have hS : 0 ≤ S := by positivity
  have hsS : 0 ≤ √S := sqrt_nonneg S
  have hsq : √S ^ 2 = S := sq_sqrt hS
  have ht0 : 0 < t := lt_of_lt_of_le hk hkt
  -- t² − S = (t − √S)(t + √S) ≤ −δ · 2k
  have h1 : t ^ 2 - S ≤ -(2 * k * δ) := by
    have ha : t - √S ≤ -δ := by linarith
    have hb : 2 * k ≤ t + √S := by
      have : k ≤ √S := by rw [show k = √(k ^ 2) by rw [sqrt_sq hk.le]]; exact sqrt_le_sqrt (by
        have : 0 ≤ 1 / m ^ 2 := by positivity
        linarith)
      linarith
    nlinarith
  have hc2 : 0 < c ^ 2 * m ^ 2 * k := by positivity
  have hχ : χ ≤ δ * (c ^ 2 * m ^ 2 * k) := by rwa [div_le_iff₀ hc2] at hδχ
  unfold Est
  have e1 : c ^ 2 * t ^ 2 * (t ^ 2 - S) ≤ -(c ^ 2 * t ^ 2 * (2 * k * δ)) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ c ^ 2 * t ^ 2)
    linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have e2 : χ * k ^ 2 / m ^ 2 ≤ c ^ 2 * t ^ 2 * k * δ := by
    rw [div_le_iff₀ hm2]
    have hkt2 : k ^ 2 ≤ t ^ 2 := by nlinarith
    calc χ * k ^ 2 ≤ δ * (c ^ 2 * m ^ 2 * k) * k ^ 2 := by
          apply mul_le_mul_of_nonneg_right hχ (sq_nonneg k)
      _ ≤ δ * (c ^ 2 * m ^ 2 * k) * t ^ 2 := by
          apply mul_le_mul_of_nonneg_left hkt2 (by positivity)
      _ = c ^ 2 * t ^ 2 * k * δ * m ^ 2 := by ring
  linarith

end Cvs.L2a.StationaryPairMismatchSign
