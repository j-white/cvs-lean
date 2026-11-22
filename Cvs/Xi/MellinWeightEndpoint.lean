import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weight, and the endpoint

The weight the substitution produced is a power: dividing by the variable and multiplying by the
fourth root of it leaves the exponent `-3/4`. And the ray from one differs from the ray beyond it by
a single point, which no integral sees.
-/

noncomputable section

open Set MeasureTheory

namespace Cvs.Xi.MellinWeightEndpoint

/-- **The substitution's weight is a power.** -/
theorem weight_rpow_eq {x : ℝ} (hx : 0 < x) :
    x⁻¹ * Real.exp (Real.log x / 4) = x ^ (-3 / 4 : ℝ) := by
  have hinv : x⁻¹ = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hx]
  rw [hinv, ← Real.exp_add, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- **The endpoint does not matter.** -/
theorem setIntegral_Ici_eq_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a : ℝ) :
    ∫ x in Ici a, f x = ∫ x in Ioi a, f x :=
  (setIntegral_congr_set Ioi_ae_eq_Ici).symm

end Cvs.Xi.MellinWeightEndpoint
