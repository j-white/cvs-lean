import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Upstream.ConfocalEllipseDeformation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The arc integral is `O(1/t)` under the damping `e^{−t sin θ}`

Jordan's inequality gives `∫_0^π e^{−t sin θ} dθ ≤ π/t`; on the half-ellipse `a cosh(η₀ + iθ) = L cos θ + iB sin θ`,
`a sinh(η₀ + iθ) = B cos θ + iL sin θ` has modulus at most `L`, so an integrand bounded by `M e^{−t sin θ}` gives
`|∫_0^π Q(η₀ + iθ) a sinh(η₀ + iθ) dθ| ≤ MLπ/t`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral
open Complex (I)

namespace Cvs.Upstream.JordanArcIntegral

/-- `∫_0^π e^{−k θ} dθ ≤ 1/k` for `k > 0`. -/
theorem integral_exp_neg_mul_le {k : ℝ} (hk : 0 < k) : ∫ y in (0 : ℝ)..π, Real.exp (-k * y) ≤ 1 / k := by
  have hd : ∀ y ∈ uIcc (0 : ℝ) π, HasDerivAt (fun y => -Real.exp (-k * y) / k) (Real.exp (-k * y)) y := by
    intro y _
    have h1 : HasDerivAt (fun y => -k * y) (-k) y := by simpa using (hasDerivAt_id y).const_mul (-k)
    exact (h1.exp.neg.div_const k).congr_deriv (by field_simp)
  rw [integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.exp_zero]
  have := Real.exp_pos (-k * π)
  rw [show -Real.exp (-k * π) / k - -1 / k = (1 - Real.exp (-k * π)) / k by ring]
  exact div_le_div_of_nonneg_right (by linarith) hk.le

/-- **Jordan's bound** `∫_0^π e^{−t sin θ} dθ ≤ π/t` for `t > 0`. -/
theorem integral_exp_neg_sin_le {t : ℝ} (ht : 0 < t) : ∫ y in (0 : ℝ)..π, Real.exp (-t * Real.sin y) ≤ π / t := by
  set k := 2 * t / π with hk
  have hk0 : 0 < k := by positivity
  have hpt : ∀ y ∈ uIcc (0 : ℝ) π,
      Real.exp (-t * Real.sin y) ≤ Real.exp (-k * y) + Real.exp (-k * (π - y)) := by
    intro y hy
    rw [uIcc_of_le Real.pi_pos.le] at hy
    rcases le_or_gt y (π / 2) with h | h
    · have hs := Real.mul_le_sin hy.1 h
      have : Real.exp (-t * Real.sin y) ≤ Real.exp (-k * y) := by
        rw [Real.exp_le_exp, hk]
        have : 2 * t / π * y = t * (2 / π * y) := by ring
        nlinarith
      linarith [Real.exp_pos (-k * (π - y))]
    · have hs := Real.mul_le_sin (x := π - y) (by linarith [hy.2]) (by linarith)
      rw [Real.sin_pi_sub] at hs
      have : Real.exp (-t * Real.sin y) ≤ Real.exp (-k * (π - y)) := by
        rw [Real.exp_le_exp, hk]
        have : 2 * t / π * (π - y) = t * (2 / π * (π - y)) := by ring
        nlinarith
      linarith [Real.exp_pos (-k * y)]
  have h1 := integral_exp_neg_mul_le hk0
  have h2 : ∫ y in (0 : ℝ)..π, Real.exp (-k * (π - y)) = ∫ y in (0 : ℝ)..π, Real.exp (-k * y) := by
    rw [intervalIntegral.integral_comp_sub_left (fun y => Real.exp (-k * y)) π]
    simp
  calc ∫ y in (0 : ℝ)..π, Real.exp (-t * Real.sin y)
      ≤ ∫ y in (0 : ℝ)..π, (Real.exp (-k * y) + Real.exp (-k * (π - y))) :=
        integral_mono_on Real.pi_pos.le (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun y hy => hpt y (by
          rw [uIcc_of_le Real.pi_pos.le]; exact hy)
    _ = 2 * ∫ y in (0 : ℝ)..π, Real.exp (-k * y) := by
        rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _), h2]; ring
    _ ≤ 2 * (1 / k) := by linarith
    _ = π / t := by rw [hk]; field_simp

/-- The half-ellipse `a cosh(η₀ + iθ) = a cosh η₀ cos θ + i a sinh η₀ sin θ`. -/
theorem cosh_arc (a η₀ θ : ℝ) : (a : ℂ) * Complex.cosh (η₀ + θ * I) =
    ((a * Real.cosh η₀ * Real.cos θ : ℝ) : ℂ) + I * ((a * Real.sinh η₀ * Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Cvs.Upstream.ConfocalEllipseDeformation.cosh_ofReal, Cvs.Upstream.ConfocalEllipseDeformation.sinh_ofReal,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

/-- `a sinh(η₀ + iθ) = a sinh η₀ cos θ + i a cosh η₀ sin θ`. -/
theorem sinh_arc (a η₀ θ : ℝ) : (a : ℂ) * Complex.sinh (η₀ + θ * I) =
    ((a * Real.sinh η₀ * Real.cos θ : ℝ) : ℂ) + I * ((a * Real.cosh η₀ * Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Cvs.Upstream.ConfocalEllipseDeformation.cosh_ofReal, Cvs.Upstream.ConfocalEllipseDeformation.sinh_ofReal,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

theorem norm_add_I_mul_le {p q L : ℝ} (h : p ^ 2 + q ^ 2 ≤ L ^ 2) (hL : 0 ≤ L) :
    ‖(p : ℂ) + I * (q : ℂ)‖ ≤ L := by
  rw [show (p : ℂ) + I * q = (p : ℂ) + (q : ℂ) * I by ring, Complex.norm_add_mul_I]
  rw [← Real.sqrt_sq hL]
  exact Real.sqrt_le_sqrt h

/-- `|a sinh(η₀ + iθ)| ≤ a cosh η₀`. -/
theorem norm_sinh_arc_le {a η₀ : ℝ} (ha : 0 ≤ a) (θ : ℝ) :
    ‖(a : ℂ) * Complex.sinh (η₀ + θ * I)‖ ≤ a * Real.cosh η₀ := by
  rw [sinh_arc]
  refine norm_add_I_mul_le ?_ (mul_nonneg ha (Real.cosh_pos _).le)
  have h1 := Real.cosh_sq η₀
  have h2 := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (a * Real.cos θ), sq_nonneg a]

/-- `|a cosh(η₀ + iθ)| ≤ a cosh η₀`. -/
theorem norm_cosh_arc_le {a η₀ : ℝ} (ha : 0 ≤ a) (θ : ℝ) :
    ‖(a : ℂ) * Complex.cosh (η₀ + θ * I)‖ ≤ a * Real.cosh η₀ := by
  rw [cosh_arc]
  refine norm_add_I_mul_le ?_ (mul_nonneg ha (Real.cosh_pos _).le)
  have h1 := Real.cosh_sq η₀
  have h2 := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (a * Real.sin θ), sq_nonneg a]

/-- **The arc bound**: `‖Q(η₀ + iθ)‖ ≤ M e^{−t sin θ}` on `[0, π]` gives
`‖∫_0^π Q(η₀ + iθ) a sinh(η₀ + iθ) dθ‖ ≤ M (a cosh η₀) π / t`. -/
theorem norm_arc_le {a η₀ M t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) {Q : ℂ → ℂ}
    (hQ : ∀ θ ∈ Icc 0 π, ‖Q (η₀ + θ * I)‖ ≤ M * Real.exp (-t * Real.sin θ)) :
    ‖∫ θ in (0 : ℝ)..π, Q (η₀ + θ * I) * ((a : ℂ) * Complex.sinh (η₀ + θ * I))‖ ≤
      M * (a * Real.cosh η₀) * (π / t) := by
  have hM : 0 ≤ M := by
    have := (norm_nonneg _).trans (hQ 0 ⟨le_rfl, Real.pi_pos.le⟩)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  calc ‖∫ θ in (0 : ℝ)..π, Q (η₀ + θ * I) * ((a : ℂ) * Complex.sinh (η₀ + θ * I))‖
      ≤ ∫ θ in (0 : ℝ)..π, M * (a * Real.cosh η₀) * Real.exp (-t * Real.sin θ) := by
        refine norm_integral_le_of_norm_le Real.pi_pos.le (Filter.Eventually.of_forall fun θ hθ => ?_)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        rw [norm_mul]
        have h1 := hQ θ (Ioc_subset_Icc_self hθ)
        have h2 := norm_sinh_arc_le ha (η₀ := η₀) θ
        calc ‖Q (η₀ + θ * I)‖ * ‖(a : ℂ) * Complex.sinh (η₀ + θ * I)‖
            ≤ (M * Real.exp (-t * Real.sin θ)) * (a * Real.cosh η₀) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = M * (a * Real.cosh η₀) * Real.exp (-t * Real.sin θ) := by ring
    _ = M * (a * Real.cosh η₀) * ∫ θ in (0 : ℝ)..π, Real.exp (-t * Real.sin θ) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ M * (a * Real.cosh η₀) * (π / t) :=
        mul_le_mul_of_nonneg_left (integral_exp_neg_sin_le ht)
          (mul_nonneg hM (mul_nonneg ha (Real.cosh_pos _).le))

end Cvs.Upstream.JordanArcIntegral

end
