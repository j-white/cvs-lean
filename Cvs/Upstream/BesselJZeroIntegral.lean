import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Bessel function `J₀` by its integral representation

`J₀(x) = (1/π)∫_0^π cos(x sin t) dt`, with `J₀(0) = 1` and `|J₀(x)| ≤ 1`: the explicit profile of a rung in the edge
layer, `ψ(ξ) ≈ ψ(1)J₀(σs)` with `s = c√(2(ξ − 1))`, the layer side of the explicit-layer route.
-/

namespace Cvs.Upstream.BesselJZeroIntegral

open Real MeasureTheory intervalIntegral

/-- `J₀(x) = (1/π)∫_0^π cos(x sin t) dt`. -/
noncomputable def besselJ0 (x : ℝ) : ℝ := (1 / π) * ∫ t in (0 : ℝ)..π, Real.cos (x * Real.sin t)

theorem besselJ0_zero : besselJ0 0 = 1 := by
  unfold besselJ0
  simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  field_simp

theorem abs_besselJ0_le (x : ℝ) : |besselJ0 x| ≤ 1 := by
  unfold besselJ0
  have hπ : 0 < π := Real.pi_pos
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (C := 1)
    (f := fun t => Real.cos (x * Real.sin t)) (fun t _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hπ, one_mul] at h
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  calc 1 / π * |∫ t in (0 : ℝ)..π, Real.cos (x * Real.sin t)| ≤ 1 / π * π :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := by field_simp

end Cvs.Upstream.BesselJZeroIntegral
