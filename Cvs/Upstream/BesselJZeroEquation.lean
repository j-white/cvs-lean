import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Upstream.BesselJZeroIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `J₀′`, `J₀″` and Bessel's equation

Differentiating under the integral, `J₀′(x) = −(1/π)∫_0^π sin t sin(x sin t)` and
`J₀″(x) = −(1/π)∫_0^π sin²t cos(x sin t)`; since `∂_t[cos t sin(x sin t)] = −sin t sin(x sin t) + x cos²t cos(x sin t)`
vanishes in integral over `[0, π]`, `xJ₀″ + J₀′ + xJ₀ = 0`: the ODE that ties the layer profile to the rungs.
-/

namespace Cvs.Upstream.BesselJZeroEquation

open Real MeasureTheory intervalIntegral Cvs.Upstream.BesselJZeroIntegral

/-- `J₀′(x) = −(1/π)∫_0^π sin t sin(x sin t)`. -/
noncomputable def besselJ0' (x : ℝ) : ℝ := -(1 / π) * ∫ t in (0 : ℝ)..π, Real.sin t * Real.sin (x * Real.sin t)

/-- `J₀″(x) = −(1/π)∫_0^π sin²t cos(x sin t)`. -/
noncomputable def besselJ0'' (x : ℝ) : ℝ := -(1 / π) * ∫ t in (0 : ℝ)..π, Real.sin t ^ 2 * Real.cos (x * Real.sin t)

/-- Differentiation under the integral over `[0, π]` for an integrand with a derivative bounded by `1`. -/
theorem hasDerivAt_integral {F F' : ℝ → ℝ → ℝ} {x₀ : ℝ} (hFc : ∀ x, Continuous (F x))
    (hF'c : ∀ x, Continuous (F' x)) (hb : ∀ x t, |F' x t| ≤ 1)
    (hd : ∀ x t, HasDerivAt (fun x => F x t) (F' x t) x) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..π, F x t) (∫ t in (0 : ℝ)..π, F' x₀ t) x₀ :=
  (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => (1 : ℝ))
    (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall fun x => (hFc x).aestronglyMeasurable)
    ((hFc x₀).intervalIntegrable _ _) (hF'c x₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t _ x _ => by rw [Real.norm_eq_abs]; exact hb x t)
    intervalIntegrable_const (Filter.Eventually.of_forall fun t _ x _ => hd x t)).2

theorem hasDerivAt_besselJ0 (x : ℝ) : HasDerivAt besselJ0 (besselJ0' x) x := by
  have h := hasDerivAt_integral (x₀ := x) (F := fun x t => Real.cos (x * Real.sin t))
    (F' := fun x t => -(Real.sin t * Real.sin (x * Real.sin t))) (fun x => by fun_prop) (fun x => by fun_prop)
    (fun x t => by
      rw [abs_neg, abs_mul]
      exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _))
    (fun x t => by
      have := ((hasDerivAt_id x).mul_const (Real.sin t)).cos
      simpa [mul_comm] using this)
  unfold besselJ0 besselJ0'
  rw [intervalIntegral.integral_neg] at h
  exact (h.const_mul (1 / π)).congr_deriv (by ring)

theorem hasDerivAt_besselJ0' (x : ℝ) : HasDerivAt besselJ0' (besselJ0'' x) x := by
  have h := hasDerivAt_integral (x₀ := x) (F := fun x t => Real.sin t * Real.sin (x * Real.sin t))
    (F' := fun x t => Real.sin t ^ 2 * Real.cos (x * Real.sin t)) (fun x => by fun_prop) (fun x => by fun_prop)
    (fun x t => by
      rw [abs_mul, abs_pow]
      exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _)) (abs_nonneg _) (Real.abs_cos_le_one _))
    (fun x t => by
      have := (((hasDerivAt_id x).mul_const (Real.sin t)).sin).const_mul (Real.sin t)
      simp only [id] at this
      exact this.congr_deriv (by ring))
  unfold besselJ0' besselJ0''
  exact h.const_mul _

/-- **Bessel's equation**: `xJ₀″(x) + J₀′(x) + xJ₀(x) = 0`. -/
theorem bessel_ode (x : ℝ) : x * besselJ0'' x + besselJ0' x + x * besselJ0 x = 0 := by
  -- `∫_0^π (x cos²t cos(x sin t) − sin t sin(x sin t)) = [cos t sin(x sin t)]_0^π = 0`
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) π, HasDerivAt (fun t => Real.cos t * Real.sin (x * Real.sin t))
      (x * Real.cos t ^ 2 * Real.cos (x * Real.sin t) - Real.sin t * Real.sin (x * Real.sin t)) t := by
    intro t _
    have h1 := Real.hasDerivAt_cos t
    have h2 := ((Real.hasDerivAt_sin t).const_mul x).sin
    exact (h1.mul h2).congr_deriv (by ring)
  have hint : ∫ t in (0 : ℝ)..π, (x * Real.cos t ^ 2 * Real.cos (x * Real.sin t) - Real.sin t * Real.sin (x * Real.sin t)) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [Real.sin_pi]
  have i1 : IntervalIntegrable (fun t => Real.sin t ^ 2 * Real.cos (x * Real.sin t)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun t => Real.sin t * Real.sin (x * Real.sin t)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  have i3 : IntervalIntegrable (fun t => Real.cos (x * Real.sin t)) volume 0 π := by
    apply Continuous.intervalIntegrable; fun_prop
  -- `x cos² = x − x sin²`
  have hsplit : ∫ t in (0 : ℝ)..π, (x * Real.cos t ^ 2 * Real.cos (x * Real.sin t) - Real.sin t * Real.sin (x * Real.sin t))
      = x * (∫ t in (0 : ℝ)..π, Real.cos (x * Real.sin t)) - x * (∫ t in (0 : ℝ)..π, Real.sin t ^ 2 * Real.cos (x * Real.sin t))
        - ∫ t in (0 : ℝ)..π, Real.sin t * Real.sin (x * Real.sin t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (i3.const_mul x) (i1.const_mul x), ← intervalIntegral.integral_sub
        ((i3.const_mul x).sub (i1.const_mul x)) i2]
    congr 1; funext t
    have := Real.sin_sq_add_cos_sq t
    have hc : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by linarith
    rw [hc]; ring
  rw [hsplit] at hint
  unfold besselJ0 besselJ0' besselJ0''
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have : x * (-(1 / π) * ∫ t in (0 : ℝ)..π, Real.sin t ^ 2 * Real.cos (x * Real.sin t))
      + -(1 / π) * (∫ t in (0 : ℝ)..π, Real.sin t * Real.sin (x * Real.sin t))
      + x * (1 / π * ∫ t in (0 : ℝ)..π, Real.cos (x * Real.sin t))
      = (1 / π) * (x * (∫ t in (0 : ℝ)..π, Real.cos (x * Real.sin t))
          - x * (∫ t in (0 : ℝ)..π, Real.sin t ^ 2 * Real.cos (x * Real.sin t))
          - ∫ t in (0 : ℝ)..π, Real.sin t * Real.sin (x * Real.sin t)) := by ring
  rw [this, hint, mul_zero]

end Cvs.Upstream.BesselJZeroEquation
