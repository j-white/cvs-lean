import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# An alias above the band as an integral up the two edges

For `φ` entire with `‖φ(t)‖ ≤ K e^{b|Im t|}` on the strip `|Re t| ≤ 1`, `a > b` and `e^{ia} = 1`, Cauchy's
theorem on `[−1, 1] × [0, Y]` and `Y → ∞` give `∫_{−1}^{1} φ(t)e^{iat} dt = i∫_0^∞ e^{−ay}(φ(−1 + iy) − φ(1 + iy)) dy`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology

namespace Cvs.Prolate.Mellin.AliasAboveBandEdges

/-- `e^{ia(±1 + iy)} = e^{−ay}` when `e^{ia} = 1`. -/
theorem exp_edge {a : ℝ} (ha : Complex.exp (I * a) = 1) (y : ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    Complex.exp (I * a * ((s : ℂ) + y * I)) = (Real.exp (-(a * y)) : ℂ) := by
  have e : I * a * ((s : ℂ) + y * I) = s * (I * a) + ((-(a * y) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e, Complex.exp_add, Complex.ofReal_exp]
  rcases hs with rfl | rfl
  · simp [ha]
  · have : Complex.exp ((-1 : ℝ) * (I * a)) = 1 := by
      rw [show ((-1 : ℝ) : ℂ) * (I * a) = -(I * a) by push_cast; ring, Complex.exp_neg, ha, inv_one]
    simp only [this, one_mul]

/-- `‖e^{ia(x + iY)}‖ = e^{−aY}`. -/
theorem norm_exp_top (a x Y : ℝ) : ‖Complex.exp (I * a * ((x : ℂ) + Y * I))‖ = Real.exp (-(a * Y)) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- **The rectangle identity**: `∫_{−1}^{1} φ(x)e^{iax} = ∫_{−1}^{1} φ(x + iY)e^{ia(x + iY)} +
i∫_0^Y e^{−ay}(φ(−1 + iy) − φ(1 + iy))` for entire `φ` and `e^{ia} = 1`. -/
theorem integral_exp_eq_rect {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {a : ℝ} (ha : Complex.exp (I * a) = 1)
    (Y : ℝ) : ∫ x in (-1 : ℝ)..1, φ x * Complex.exp (I * a * x)
      = (∫ x in (-1 : ℝ)..1, φ (x + Y * I) * Complex.exp (I * a * ((x : ℂ) + Y * I)))
        + I * ∫ y in (0 : ℝ)..Y, (Real.exp (-(a * y)) : ℂ) * (φ (-1 + y * I) - φ (1 + y * I)) := by
  set f : ℂ → ℂ := fun t => φ t * Complex.exp (I * a * t) with hf
  have hfd : Differentiable ℂ f := hφ.mul ((differentiable_id.const_mul _).cexp)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (-1) (1 + Y * I)
    hfd.differentiableOn
  simp only [neg_re, one_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero, neg_im, one_im, add_im, mul_im, zero_add, neg_zero, ofReal_zero, smul_eq_mul] at h
  have hv1 : ∀ y : ℝ, f (((1 : ℝ) : ℂ) + y * I) = (Real.exp (-(a * y)) : ℂ) * φ (1 + y * I) := fun y => by
    simp only [hf]; rw [exp_edge ha y 1 (Or.inl rfl)]; push_cast; ring
  have hv2 : ∀ y : ℝ, f (((-1 : ℝ) : ℂ) + y * I) = (Real.exp (-(a * y)) : ℂ) * φ (-1 + y * I) := fun y => by
    simp only [hf]; rw [exp_edge ha y (-1) (Or.inr rfl)]; push_cast; ring
  have e1 : ∫ y in (0 : ℝ)..Y, f (1 + y * I) = ∫ y in (0 : ℝ)..Y, (Real.exp (-(a * y)) : ℂ) * φ (1 + y * I) :=
    intervalIntegral.integral_congr fun y _ => by simpa using hv1 y
  have e2 : ∫ y in (0 : ℝ)..Y, f (-1 + y * I)
      = ∫ y in (0 : ℝ)..Y, (Real.exp (-(a * y)) : ℂ) * φ (-1 + y * I) :=
    intervalIntegral.integral_congr fun y _ => by simpa using hv2 y
  have hc1 : Continuous fun y : ℝ => (Real.exp (-(a * y)) : ℂ) * φ (1 + y * I) := by
    have := hφ.continuous; fun_prop
  have hc2 : Continuous fun y : ℝ => (Real.exp (-(a * y)) : ℂ) * φ (-1 + y * I) := by
    have := hφ.continuous; fun_prop
  have eV : ∫ y in (0 : ℝ)..Y, (Real.exp (-(a * y)) : ℂ) * (φ (-1 + y * I) - φ (1 + y * I))
      = (∫ y in (0 : ℝ)..Y, (Real.exp (-(a * y)) : ℂ) * φ (-1 + y * I))
        - ∫ y in (0 : ℝ)..Y, (Real.exp (-(a * y)) : ℂ) * φ (1 + y * I) := by
    rw [← intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hc1.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  norm_num at h
  rw [e1, e2] at h
  rw [eV]
  simp only [hf] at h
  linear_combination h

end Cvs.Prolate.Mellin.AliasAboveBandEdges

end
