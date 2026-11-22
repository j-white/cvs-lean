import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Inverting the variable carries the unit interval to the ray

Inversion sends the ray beyond one onto the interval below it, injectively and with derivative the
negative reciprocal square. The change of variables therefore rewrites an integral over the
interval as one over the ray, weighted by that square.
-/

noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace Cvs.Xi.InversionIntervalToRay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Inversion carries the ray beyond one onto the interval below it.** -/
theorem image_inv_Ioi_one : (fun x : ℝ => x⁻¹) '' (Ioi 1) = Ioo 0 1 := by
  have h : (Ioi (1 : ℝ))⁻¹ = Ioo 0 (1 : ℝ)⁻¹ := inv_Ioi₀ zero_lt_one
  rw [inv_one] at h
  rw [← h, ← Set.image_inv_eq_inv]

/-- **The change of variables.** -/
theorem integral_Ioo_eq_integral_Ioi_inv (g : ℝ → E) :
    ∫ x in Ioo (0 : ℝ) 1, g x = ∫ x in Ioi (1 : ℝ), (x ^ 2)⁻¹ • g x⁻¹ := by
  have hderiv : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivWithinAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) (Ioi (1 : ℝ)) x := by
    intro x hx
    exact (hasDerivAt_inv (ne_of_gt (lt_trans zero_lt_one hx))).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x⁻¹) (Ioi 1) := inv_injective.injOn
  have h := integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioi (a := (1 : ℝ))) hderiv hinj g
  rw [image_inv_Ioi_one] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hsq : (0 : ℝ) < x ^ 2 := by positivity
  rw [abs_neg, abs_of_pos (inv_pos.mpr hsq)]

end Cvs.Xi.InversionIntervalToRay
