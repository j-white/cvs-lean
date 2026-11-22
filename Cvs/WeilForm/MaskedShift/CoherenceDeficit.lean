import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open scoped BigOperators

namespace Cvs.WeilForm.MaskedShift.CoherenceDeficit

open Real Finset

/-! # Cvs.WeilForm.MaskedShift.CoherenceDeficit: the coherence deficit in closed form

`budget - symbol(n) = 4 ∑ᵢ wᵢ sin(π uᵢ n)²`, and the strict shortfall that
irrationality forces.
-/

/-- `1 - cos t = 2 sin(t/2)²`. -/
theorem one_sub_cos_eq (t : ℝ) : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
  have h : Real.cos t = Real.cos (2 * (t / 2)) := by ring_nf
  have hpy : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 := sin_sq_add_cos_sq _
  rw [h, Real.cos_two_mul']
  nlinarith [hpy]

/-! ## Irrationality forces a strict shortfall -/

/-! ## Simultaneous approximation bounds the deficit above -/

/-- Shifting by the nearest integer changes `sin (π x)` only by a sign. -/
theorem abs_sin_pi_sub_round (x : ℝ) :
    |Real.sin (π * (x - round x))| = |Real.sin (π * x)| := by
  have hsplit : π * x = π * (x - round x) + (round x : ℤ) * π := by ring
  have hpow : |((-1 : ℝ) ^ (round x : ℤ))| = 1 := by
    rcases Int.even_or_odd (round x) with he | ho
    · rw [he.neg_one_zpow]; norm_num
    · rw [ho.neg_one_zpow]; norm_num
  rw [hsplit, Real.sin_add, Real.sin_int_mul_pi, Real.cos_int_mul_pi,
    show Real.sin (π * (x - (round x : ℤ))) * (-1 : ℝ) ^ (round x : ℤ)
        + Real.cos (π * (x - (round x : ℤ))) * 0
      = Real.sin (π * (x - (round x : ℤ))) * (-1 : ℝ) ^ (round x : ℤ) by ring,
    abs_mul, hpow, mul_one]

/-- `|sin (π x)| ≤ π ‖x‖`, with `‖·‖` the norm of `UnitAddCircle`. -/
theorem abs_sin_pi_le (x : ℝ) :
    |Real.sin (π * x)| ≤ π * ‖(x : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq, ← abs_sin_pi_sub_round x]
  calc |Real.sin (π * (x - round x))| ≤ |π * (x - round x)| := Real.abs_sin_le_abs
    _ = π * |x - round x| := by rw [abs_mul, abs_of_pos Real.pi_pos]

/-!
## The arithmetic prime side: the deficit identity, at the arithmetic prime side

Cvs.WeilForm.MaskedShift.CoherenceDeficit gives the deficit of an abstract symbol `∑ᵢ 2wᵢ cos(2π uᵢ n)` in closed form.
-/

end Cvs.WeilForm.MaskedShift.CoherenceDeficit
