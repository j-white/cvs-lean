import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

namespace Cvs.Operator

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! # B31: bounding a symmetric operator by its quadratic form

The bridge the Schur argument needs: for a symmetric operator, a uniform bound
on `|⟪T x, x⟫|` is a bound on `‖T‖`.  Mathlib supplies
`norm_eq_iSup_rayleighQuotient`; this packages it in the form the estimate
produces.
-/

omit [CompleteSpace E] in
/-- **A quadratic-form bound is a norm bound**, for symmetric operators. -/
theorem opNorm_le_of_quadForm_le {T : E →L[ℝ] E}
    (hT : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x : E, |inner ℝ (T x) x| ≤ C * ‖x‖ ^ 2) :
    ‖T‖ ≤ C := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := T) hT]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf]
    simpa using hC
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_of_pos hx2,
      div_le_iff₀ hx2]
    simpa [ContinuousLinearMap.reApplyInnerSelf] using h x

end Cvs.Operator
