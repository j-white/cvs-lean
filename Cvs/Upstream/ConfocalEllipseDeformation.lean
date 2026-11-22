import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The real segment `[−L, L]` deforms to the confocal half-ellipse

With `z = a cosh ζ` on the rectangle `[0, η₀] × [0, π]`, the sides `θ = 0`, `η = 0`, `θ = π` map onto `[a, L]`,
`[−a, a]`, `[−L, −a]` (`L = a cosh η₀`) and `η = η₀` onto the upper half-ellipse; Cauchy's theorem gives
`∫_{−L}^{L} q = −i∫_0^π Q(η₀ + iθ) a sinh(η₀ + iθ) dθ` when `Q` is holomorphic there and matches `q` on the sides.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral
open scoped Interval
open Complex (I)

namespace Cvs.Upstream.ConfocalEllipseDeformation

theorem cosh_ofReal (x : ℝ) : Complex.cosh (x : ℂ) = (Real.cosh x : ℂ) := (Complex.ofReal_cosh x).symm

theorem sinh_ofReal (x : ℝ) : Complex.sinh (x : ℂ) = (Real.sinh x : ℂ) := (Complex.ofReal_sinh x).symm

/-- The side `θ = 0`: `∫_0^{η₀} Q(η) a sinh η dη = ∫_a^L q`. -/
theorem side_bottom {a η₀ : ℝ} (hη : 0 ≤ η₀) (ha : 0 ≤ a) {Q : ℂ → ℂ} {q : ℝ → ℂ}
    (h1 : ∀ η ∈ Icc 0 η₀, Q η = q (a * Real.cosh η)) :
    ∫ x in (0 : ℝ)..η₀, Q (x + (0 : ℝ) * I) * ((a : ℂ) * Complex.sinh (x + (0 : ℝ) * I)) =
      ∫ x in a..a * Real.cosh η₀, q x := by
  have hd : ∀ x, HasDerivAt (fun x => a * Real.cosh x) (a * Real.sinh x) x :=
    fun x => (Real.hasDerivAt_cosh x).const_mul a
  have h := integral_deriv_smul_comp_of_deriv_nonneg (g := q) (a := 0) (b := η₀)
    (f := fun x => a * Real.cosh x) (f' := fun x => a * Real.sinh x)
    ((Continuous.continuousOn (by fun_prop))) (fun x _ => hd x) (fun x hx => by
      have : 0 ≤ x := by rw [min_eq_left hη] at hx; exact hx.1.le
      exact mul_nonneg ha (Real.sinh_nonneg_iff.2 this))
  simp only [Real.cosh_zero, mul_one] at h
  rw [← h]
  refine integral_congr fun x hx => ?_
  rw [uIcc_of_le hη] at hx
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Function.comp, Complex.real_smul]
  rw [h1 x hx, sinh_ofReal]
  push_cast; ring

/-- The side `θ = π`: `∫_0^{η₀} Q(η + iπ) a sinh(η + iπ) dη = −∫_{−L}^{−a} q`. -/
theorem side_top {a η₀ : ℝ} (hη : 0 ≤ η₀) (ha : 0 ≤ a) {Q : ℂ → ℂ} {q : ℝ → ℂ}
    (h2 : ∀ η ∈ Icc 0 η₀, Q (η + π * I) = q (-(a * Real.cosh η))) :
    ∫ x in (0 : ℝ)..η₀, Q (x + (π : ℝ) * I) * ((a : ℂ) * Complex.sinh (x + (π : ℝ) * I)) =
      -∫ x in -(a * Real.cosh η₀)..-a, q x := by
  have hd : ∀ x, HasDerivAt (fun x => -(a * Real.cosh x)) (-(a * Real.sinh x)) x :=
    fun x => ((Real.hasDerivAt_cosh x).const_mul a).neg
  have h := integral_deriv_smul_comp_of_deriv_nonpos (g := q) (a := 0) (b := η₀)
    (f := fun x => -(a * Real.cosh x)) (f' := fun x => -(a * Real.sinh x))
    ((Continuous.continuousOn (by fun_prop))) (fun x _ => hd x) (fun x hx => by
      have : 0 ≤ x := by rw [min_eq_left hη] at hx; exact hx.1.le
      exact neg_nonpos.2 (mul_nonneg ha (Real.sinh_nonneg_iff.2 this)))
  simp only [Real.cosh_zero, mul_one] at h
  rw [intervalIntegral.integral_symm (-a) (-(a * Real.cosh η₀)), neg_neg, ← h]
  refine integral_congr fun x hx => ?_
  rw [uIcc_of_le hη] at hx
  simp only [Function.comp, Complex.real_smul]
  rw [Complex.sinh_add_pi_mul_I, h2 x hx, sinh_ofReal]
  push_cast; ring

/-- The side `η = 0`: `−i∫_0^π Q(iθ) a sinh(iθ) dθ = ∫_{−a}^{a} q`. -/
theorem side_left {a : ℝ} (ha : 0 ≤ a) {Q : ℂ → ℂ} {q : ℝ → ℂ}
    (h3 : ∀ y ∈ Icc 0 π, Q (y * I) = q (a * Real.cos y)) :
    -(I • ∫ y in (0 : ℝ)..π, Q ((0 : ℝ) + y * I) * ((a : ℂ) * Complex.sinh ((0 : ℝ) + y * I))) =
      ∫ x in -a..a, q x := by
  have hd : ∀ x, HasDerivAt (fun x => a * Real.cos x) (-(a * Real.sin x)) x := fun x => by
    simpa using (Real.hasDerivAt_cos x).const_mul a
  have h := integral_deriv_smul_comp_of_deriv_nonpos (g := q) (a := 0) (b := π)
    (f := fun x => a * Real.cos x) (f' := fun x => -(a * Real.sin x))
    ((Continuous.continuousOn (by fun_prop))) (fun x _ => hd x) (fun x hx => by
      rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hx
      exact neg_nonpos.2 (mul_nonneg ha (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le)))
  simp only [Real.cos_zero, mul_one, Real.cos_pi, mul_neg] at h
  rw [intervalIntegral.integral_symm a (-a), ← h, ← intervalIntegral.integral_smul,
    ← intervalIntegral.integral_neg, ← intervalIntegral.integral_neg]
  refine integral_congr fun y hy => ?_
  rw [uIcc_of_le Real.pi_pos.le] at hy
  simp only [Function.comp, Complex.real_smul, Complex.ofReal_zero, zero_add, smul_eq_mul]
  rw [Complex.sinh_mul_I, h3 y hy, ← Complex.ofReal_sin]
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- **The contour identity** `∫_{−L}^{L} q = −i∫_0^π Q(η₀ + iθ)·a sinh(η₀ + iθ) dθ`, `L = a cosh η₀`. -/
theorem integral_eq_arc {a η₀ : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η₀) {Q : ℂ → ℂ} {q : ℝ → ℂ}
    (hQ : DifferentiableOn ℂ Q ([[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]]))
    (hq : IntervalIntegrable q volume (-(a * Real.cosh η₀)) (a * Real.cosh η₀))
    (h1 : ∀ η ∈ Icc 0 η₀, Q η = q (a * Real.cosh η))
    (h2 : ∀ η ∈ Icc 0 η₀, Q (η + π * I) = q (-(a * Real.cosh η)))
    (h3 : ∀ y ∈ Icc 0 π, Q (y * I) = q (a * Real.cos y)) :
    ∫ x in -(a * Real.cosh η₀)..(a * Real.cosh η₀), q x =
      -I * ∫ y in (0 : ℝ)..π, Q (η₀ + y * I) * ((a : ℂ) * Complex.sinh (η₀ + y * I)) := by
  set G : ℂ → ℂ := fun ζ => Q ζ * ((a : ℂ) * Complex.sinh ζ) with hG
  have hGd : DifferentiableOn ℂ G ([[(0 : ℝ), η₀]] ×ℂ [[(0 : ℝ), π]]) :=
    hQ.mul ((Complex.differentiable_sinh.const_mul (a : ℂ)).differentiableOn)
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G 0 (η₀ + π * I)
    (by simpa using hGd)
  simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, zero_add, add_zero] at hc
  have hb := side_bottom hη ha h1
  have ht := side_top hη ha h2
  have hl := side_left ha h3
  simp only [hG] at hc
  simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_add] at hc hb hl
  have hL : 0 ≤ a * Real.cosh η₀ := mul_nonneg ha (Real.cosh_pos _).le
  have ha1 : a ≤ a * Real.cosh η₀ := le_mul_of_one_le_right ha (Real.one_le_cosh _)
  have hi1 : IntervalIntegrable q volume (-(a * Real.cosh η₀)) (-a) :=
    hq.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  have hi2 : IntervalIntegrable q volume (-a) a :=
    hq.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) (by linarith))
  have hi3 : IntervalIntegrable q volume a (a * Real.cosh η₀) :=
    hq.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
  rw [← integral_add_adjacent_intervals hi1 (hi2.trans hi3), ← integral_add_adjacent_intervals hi2 hi3]
  rw [← hb, ← hl]
  have ht' : ∫ x in -(a * Real.cosh η₀)..-a, q x =
      -∫ x in (0 : ℝ)..η₀, Q (x + π * I) * ((a : ℂ) * Complex.sinh (x + π * I)) := by
    rw [ht]; ring
  rw [ht']
  have hc' := hc
  simp only [smul_eq_mul] at hc' ⊢
  linear_combination hc'

end Cvs.Upstream.ConfocalEllipseDeformation

end
