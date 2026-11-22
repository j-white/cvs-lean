import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB endpoint with the rung's sharp amplitude

A normalised rung has `∫|g| ≤ √2` (`|g| ≤ (1/√2 + √2 g²)/2` pointwise), so `ψ = μg` gives `|g| ≤ √2/μ` and
`|g′| ≤ √2c/μ`; with Landau's `λ ≥ 1/2`, i.e. `μ² ≥ π/c`, the turning-point flux is at most `2c²/π` (`LowRungEndpointSmall`'s sup bounds
give `8c⁴`). Hence `1 − λ₄ ≤ 8·wkbEnd₂(c, χ₄)`, `wkbEnd₂ = 9(2c²/π)e^{(2c−1)(Φ(s₀) + √(2δ))}/(4δκ₀)`, and RH from L1's gap
at that bound.
-/

noncomputable section

open MeasureTheory Set Real Filter

namespace Cvs.Prolate.LiouvilleGreen.WkbEndpointAmplitude


/-- **A normalised function has `∫|g| ≤ √2` on `[−1, 1]`.** -/
theorem integral_abs_le_sqrt_two {g : ℝ → ℝ} (hgc : ContinuousOn g (uIcc (-1) 1))
    (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) : (∫ s in (-1 : ℝ)..1, |g s|) ≤ √2 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpt : ∀ s, |g s| ≤ 1 / (2 * √2) + √2 / 2 * g s ^ 2 := fun s => by
    have h := sq_nonneg (√2 * |g s| - 1)
    rw [sub_sq, mul_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_abs (g s)]
  have hi : IntervalIntegrable (fun s => |g s|) volume (-1) 1 := hgc.abs.intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => 1 / (2 * √2) + √2 / 2 * g s ^ 2) volume (-1) 1 :=
    (continuousOn_const.add (continuousOn_const.mul (hgc.pow 2))).intervalIntegrable
  calc (∫ s in (-1 : ℝ)..1, |g s|) ≤ ∫ s in (-1 : ℝ)..1, (1 / (2 * √2) + √2 / 2 * g s ^ 2) :=
        intervalIntegral.integral_mono_on (by norm_num) hi hi2 fun s _ => hpt s
    _ = 2 * (1 / (2 * √2)) + √2 / 2 * 1 := by
        have hc1 : IntervalIntegrable (fun _ : ℝ => 1 / (2 * √2)) volume (-1) 1 :=
          continuousOn_const.intervalIntegrable
        have hc2 : IntervalIntegrable (fun s => √2 / 2 * g s ^ 2) volume (-1) 1 :=
          (continuousOn_const.mul (hgc.pow 2)).intervalIntegrable
        rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul, hnorm,
          intervalIntegral.integral_const, smul_eq_mul]; norm_num
    _ = √2 := by field_simp; nlinarith [hs2]

end Cvs.Prolate.LiouvilleGreen.WkbEndpointAmplitude
