import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.StationaryPairMismatchSign

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A stationary pair's mismatch, factored at its exact roots

`E(t) = c²t⁴ − c²St² + χk²/m²` (`S = k² + 1/m²`) is a quadratic in `t²`: `E = c²(t² − T₊)(t² − T₋)`,
`T± = (S ± √Δ)/2`, `Δ = S² − 4χk²/(c²m²)`. For `0 ≤ χ ≤ c²` and `mk ≥ 1`, `Δ ≥ (k² − 1/m²)²`, so `T₋ ≤ 1/m²`,
`k² + (c² − χ)/(c²m²) ≤ T₊ ≤ S`, and around `√T₊` the signs of `E` are explicit with no condition on `χ`.
-/

namespace Cvs.L2a.StationaryMismatchExactRoots

open Real Cvs.L2a.StationaryPairMismatchSign

variable {c χ k m t δ : ℝ}

/-- The discriminant `Δ = S² − 4χk²/(c²m²)`. -/
noncomputable def disc (c χ k m : ℝ) : ℝ := (k ^ 2 + 1 / m ^ 2) ^ 2 - 4 * χ * k ^ 2 / (c ^ 2 * m ^ 2)
/-- The larger root `T₊ = (S + √Δ)/2`. -/
noncomputable def Tp (c χ k m : ℝ) : ℝ := (k ^ 2 + 1 / m ^ 2 + √(disc c χ k m)) / 2
/-- The smaller root `T₋ = (S − √Δ)/2`. -/
noncomputable def Tm (c χ k m : ℝ) : ℝ := (k ^ 2 + 1 / m ^ 2 - √(disc c χ k m)) / 2

/-- `Δ − (k² − 1/m²)² = 4k²(c² − χ)/(c²m²)`. -/
theorem disc_eq (hc : 0 < c) (hm : 0 < m) :
    disc c χ k m = (k ^ 2 - 1 / m ^ 2) ^ 2 + 4 * k ^ 2 * (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := by
  unfold disc; field_simp; ring

theorem disc_ge (hc : 0 < c) (hm : 0 < m) (hχc : χ ≤ c ^ 2) : (k ^ 2 - 1 / m ^ 2) ^ 2 ≤ disc c χ k m := by
  rw [disc_eq hc hm]
  have : 0 ≤ 4 * k ^ 2 * (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := by
    apply div_nonneg _ (by positivity); have : 0 ≤ c ^ 2 - χ := by linarith
    positivity
  linarith

/-- `√Δ ≥ k² − 1/m²` for `mk ≥ 1`. -/
theorem sqrt_disc_ge (hc : 0 < c) (hm : 0 < m) (hkm : 1 ≤ m * k) (hχc : χ ≤ c ^ 2) :
    k ^ 2 - 1 / m ^ 2 ≤ √(disc c χ k m) := by
  have h0 : 0 ≤ k ^ 2 - 1 / m ^ 2 := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]; nlinarith
  rw [← sqrt_sq h0]; exact sqrt_le_sqrt (disc_ge hc hm hχc)

/-- **The factorization** `E = c²(t² − T₊)(t² − T₋)`, for `Δ ≥ 0`. -/
theorem Est_eq (hc : 0 < c) (hm : 0 < m) (hΔ : 0 ≤ disc c χ k m) :
    Est c χ k m t = c ^ 2 * (t ^ 2 - Tp c χ k m) * (t ^ 2 - Tm c χ k m) := by
  have hs := sq_sqrt hΔ
  unfold Est Tp Tm
  set r := √(disc c χ k m)
  unfold disc at hs
  have e : c ^ 2 * (t ^ 2 - (k ^ 2 + 1 / m ^ 2 + r) / 2) * (t ^ 2 - (k ^ 2 + 1 / m ^ 2 - r) / 2)
      = c ^ 2 * t ^ 2 * (t ^ 2 - (k ^ 2 + 1 / m ^ 2)) + c ^ 2 * ((k ^ 2 + 1 / m ^ 2) ^ 2 - r ^ 2) / 4 := by ring
  rw [e, hs]; field_simp; ring

theorem Tm_le (hc : 0 < c) (hm : 0 < m) (hkm : 1 ≤ m * k) (hχc : χ ≤ c ^ 2) :
    Tm c χ k m ≤ 1 / m ^ 2 := by
  have := sqrt_disc_ge hc hm hkm hχc
  unfold Tm; linarith

theorem Tm_nonneg (hc : 0 < c) (hm : 0 < m) (hχ : 0 ≤ χ) : 0 ≤ Tm c χ k m := by
  unfold Tm
  have hS : 0 ≤ k ^ 2 + 1 / m ^ 2 := by positivity
  have : √(disc c χ k m) ≤ k ^ 2 + 1 / m ^ 2 := by
    rw [sqrt_le_left hS]; unfold disc
    have : 0 ≤ 4 * χ * k ^ 2 / (c ^ 2 * m ^ 2) := by positivity
    linarith
  linarith

theorem Tp_add_Tm : Tp c χ k m + Tm c χ k m = k ^ 2 + 1 / m ^ 2 := by unfold Tp Tm; ring

theorem Tp_le (hc : 0 < c) (hm : 0 < m) (hχ : 0 ≤ χ) : Tp c χ k m ≤ k ^ 2 + 1 / m ^ 2 := by
  have := Tm_nonneg (k := k) hc hm hχ; have := Tp_add_Tm (c := c) (χ := χ) (k := k) (m := m); linarith

/-- `T₊T₋ = χk²/(c²m²)`. -/
theorem Tp_mul_Tm (hc : 0 < c) (hm : 0 < m) (hΔ : 0 ≤ disc c χ k m) :
    Tp c χ k m * Tm c χ k m = χ * k ^ 2 / (c ^ 2 * m ^ 2) := by
  have hs := sq_sqrt hΔ
  unfold Tp Tm
  have e : (k ^ 2 + 1 / m ^ 2 + √(disc c χ k m)) / 2 * ((k ^ 2 + 1 / m ^ 2 - √(disc c χ k m)) / 2)
      = ((k ^ 2 + 1 / m ^ 2) ^ 2 - √(disc c χ k m) ^ 2) / 4 := by ring
  rw [e, hs]; unfold disc; field_simp; ring

/-- `T₊ ≥ k² + (c² − χ)/(c²m²)`. -/
theorem Tp_ge (hc : 0 < c) (hk : 0 < k) (hm : 0 < m) (hkm : 1 ≤ m * k) (hχ : 0 ≤ χ) (hχc : χ ≤ c ^ 2) :
    k ^ 2 + (c ^ 2 - χ) / (c ^ 2 * m ^ 2) ≤ Tp c χ k m := by
  have hΔ : 0 ≤ disc c χ k m := le_trans (sq_nonneg _) (disc_ge hc hm hχc)
  have h1 : k ^ 2 ≤ Tp c χ k m := by
    have := sqrt_disc_ge hc hm hkm hχc; unfold Tp; linarith
  have hTp0 : 0 < Tp c χ k m := lt_of_lt_of_le (by positivity) h1
  have hprod := Tp_mul_Tm hc hm hΔ
  -- `T₋ = χk²/(c²m²T₊) ≤ χ/(c²m²)`
  have hTm : Tm c χ k m ≤ χ / (c ^ 2 * m ^ 2) := by
    have e : Tm c χ k m = χ * k ^ 2 / (c ^ 2 * m ^ 2) / Tp c χ k m := by
      rw [← hprod]; field_simp
    rw [e, div_le_iff₀ hTp0]
    have : χ * k ^ 2 / (c ^ 2 * m ^ 2) = χ / (c ^ 2 * m ^ 2) * k ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsum := Tp_add_Tm (c := c) (χ := χ) (k := k) (m := m)
  have e2 : (c ^ 2 - χ) / (c ^ 2 * m ^ 2) = 1 / m ^ 2 - χ / (c ^ 2 * m ^ 2) := by field_simp
  linarith

/-- **Right of the window** `√T₊ + δ ≤ t`: `E(t) ≥ 2c²√T₊ δ (k² − 1/m²)`. -/
theorem Est_right (hc : 0 < c) (hk : 0 < k) (hm : 0 < m) (hkm : 1 ≤ m * k) (hχ : 0 ≤ χ) (hχc : χ ≤ c ^ 2)
    (hδ : 0 < δ) (ht : √(Tp c χ k m) + δ ≤ t) :
    2 * c ^ 2 * √(Tp c χ k m) * δ * (k ^ 2 - 1 / m ^ 2) ≤ Est c χ k m t := by
  have hΔ : 0 ≤ disc c χ k m := le_trans (sq_nonneg _) (disc_ge hc hm hχc)
  have hTp := Tp_ge hc hk hm hkm hχ hχc
  have hTp0 : 0 ≤ Tp c χ k m := le_trans (by positivity) hTp
  have hsq : √(Tp c χ k m) ^ 2 = Tp c χ k m := sq_sqrt hTp0
  have hs0 : 0 ≤ √(Tp c χ k m) := sqrt_nonneg _
  have h1 : 2 * √(Tp c χ k m) * δ ≤ t ^ 2 - Tp c χ k m := by nlinarith
  have hk2 : 0 ≤ k ^ 2 - 1 / m ^ 2 := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]; nlinarith
  have hT : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have h2 : k ^ 2 - 1 / m ^ 2 ≤ t ^ 2 - Tm c χ k m := by
    have := Tm_le hc hm hkm hχc
    nlinarith
  rw [Est_eq hc hm hΔ]
  have := mul_le_mul h1 h2 hk2 (by nlinarith)
  calc 2 * c ^ 2 * √(Tp c χ k m) * δ * (k ^ 2 - 1 / m ^ 2)
      = c ^ 2 * (2 * √(Tp c χ k m) * δ * (k ^ 2 - 1 / m ^ 2)) := by ring
    _ ≤ c ^ 2 * ((t ^ 2 - Tp c χ k m) * (t ^ 2 - Tm c χ k m)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- **Left of the window** `k ≤ t ≤ √T₊ − δ`: `E(t) ≤ −2c²kδ (k² − 1/m²)`. -/
theorem Est_left (hc : 0 < c) (hk : 0 < k) (hm : 0 < m) (hkm : 1 ≤ m * k) (hχ : 0 ≤ χ) (hχc : χ ≤ c ^ 2)
    (hδ : 0 < δ) (hkt : k ≤ t) (ht : t ≤ √(Tp c χ k m) - δ) :
    Est c χ k m t ≤ -(2 * c ^ 2 * k * δ * (k ^ 2 - 1 / m ^ 2)) := by
  have hΔ : 0 ≤ disc c χ k m := le_trans (sq_nonneg _) (disc_ge hc hm hχc)
  have hTp := Tp_ge hc hk hm hkm hχ hχc
  have hTp0 : 0 ≤ Tp c χ k m := le_trans (by positivity) hTp
  have hsq : √(Tp c χ k m) ^ 2 = Tp c χ k m := sq_sqrt hTp0
  have hT : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hkT : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have h1 : 2 * k * δ ≤ Tp c χ k m - t ^ 2 := by
    have ha : δ ≤ √(Tp c χ k m) - t := by linarith
    have hb : 2 * k ≤ √(Tp c χ k m) + t := by linarith
    have : Tp c χ k m - t ^ 2 = (√(Tp c χ k m) - t) * (√(Tp c χ k m) + t) := by linear_combination -hsq
    rw [this]; nlinarith
  have hk2 : 0 ≤ k ^ 2 - 1 / m ^ 2 := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]; nlinarith
  have h2 : k ^ 2 - 1 / m ^ 2 ≤ t ^ 2 - Tm c χ k m := by
    have := Tm_le hc hm hkm hχc
    nlinarith
  rw [Est_eq hc hm hΔ]
  have := mul_le_mul h1 h2 hk2 (by nlinarith)
  calc c ^ 2 * (t ^ 2 - Tp c χ k m) * (t ^ 2 - Tm c χ k m)
      = -(c ^ 2 * ((Tp c χ k m - t ^ 2) * (t ^ 2 - Tm c χ k m))) := by ring
    _ ≤ -(c ^ 2 * (2 * k * δ * (k ^ 2 - 1 / m ^ 2))) := by
        have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ c ^ 2)
        linarith
    _ = _ := by ring

end Cvs.L2a.StationaryMismatchExactRoots
