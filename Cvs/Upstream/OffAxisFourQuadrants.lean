import Mathlib
import Cvs.Limit.OffAxesLimit
import Cvs.Upstream.NonzeroValueConvexNotLocallyZero

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-axis set in four convex pieces

The plane off both coordinate axes is covered by four open quadrants, each convex, so a function
differentiable there and non-zero at one point of each quadrant vanishes on a neighbourhood of no
point off the axes.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Upstream.OffAxisFourQuadrants

open Cvs.Limit.OffAxesLimit

/-- The quadrant picked out by the signs of `s` and `t`. -/
def quad (s t : ℝ) : Set ℂ := {w : ℂ | 0 < s * w.re ∧ 0 < t * w.im}

theorem isOpen_quad (s t : ℝ) : IsOpen (quad s t) :=
  (isOpen_lt (continuous_const : Continuous fun _ : ℂ => (0 : ℝ))
      (continuous_const.mul Complex.continuous_re : Continuous fun w : ℂ => s * w.re)).inter
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ => (0 : ℝ))
      (continuous_const.mul Complex.continuous_im : Continuous fun w : ℂ => t * w.im))

/-- A convex combination of two positive numbers is positive. -/
theorem pos_combo {P Q a b : ℝ} (hP : 0 < P) (hQ : 0 < Q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < a * P + b * Q := by
  rcases lt_or_eq_of_le ha with ha' | ha0
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hP) (mul_nonneg hb hQ.le)
  · have hb1 : b = 1 := by linarith
    rw [← ha0, hb1]
    simpa using hQ

theorem convex_quad (s t : ℝ) : Convex ℝ (quad s t) := by
  intro x hx y hy a b ha hb hab
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp
  constructor
  · have h : s * (a * x.re + b * y.re) = a * (s * x.re) + b * (s * y.re) := by ring
    rw [hre, h]
    exact pos_combo hx.1 hy.1 ha hb hab
  · have h : t * (a * x.im + b * y.im) = a * (t * x.im) + b * (t * y.im) := by ring
    rw [him, h]
    exact pos_combo hx.2 hy.2 ha hb hab

/-- Every quadrant lies off both axes, the signs being non-zero. -/
theorem quad_subset_offAxes {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) : quad s t ⊆ offAxes := by
  rintro w ⟨hw1, hw2⟩
  exact ⟨fun h => by simp [h] at hw1, fun h => by simp [h] at hw2⟩

/-- A point off the axes lies in the quadrant its own signs pick out. -/
theorem mem_quad_self {z : ℂ} (hz : z ∈ offAxes) :
    z ∈ quad (if 0 < z.re then 1 else -1) (if 0 < z.im then 1 else -1) := by
  constructor
  · by_cases h : 0 < z.re
    · simp [h]
    · have : z.re < 0 := lt_of_le_of_ne (not_lt.mp h) hz.1
      simpa [h] using this
  · by_cases h : 0 < z.im
    · simp [h]
    · have : z.im < 0 := lt_of_le_of_ne (not_lt.mp h) hz.2
      simpa [h] using this

/-- **One non-zero value per quadrant rules out local vanishing off the axes.** -/
theorem not_eventually_zero_of_quadrants {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f offAxes)
    (hne : ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → ∃ w ∈ quad s t, f w ≠ 0)
    {z : ℂ} (hz : z ∈ offAxes) : ¬ (∀ᶠ v in 𝓝 z, f v = 0) := by
  set s : ℝ := if 0 < z.re then 1 else -1 with hs
  set t : ℝ := if 0 < z.im then 1 else -1 with ht
  have hs0 : s ≠ 0 := by rw [hs]; split <;> norm_num
  have ht0 : t ≠ 0 := by rw [ht]; split <;> norm_num
  obtain ⟨w, hw, hfw⟩ := hne s t hs0 ht0
  exact Cvs.Upstream.NonzeroValueConvexNotLocallyZero.not_eventually_zero_of_convex (isOpen_quad s t) (convex_quad s t)
    (hf.mono (quad_subset_offAxes hs0 ht0)) (mem_quad_self hz) hw hfw

end Cvs.Upstream.OffAxisFourQuadrants
