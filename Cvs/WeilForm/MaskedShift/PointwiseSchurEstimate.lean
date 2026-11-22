import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Defs
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.SchurCondition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real

namespace Cvs.Operator

open Cvs.Operator

variable {β : ℝ}

/-! # B32: the pointwise Schur estimate

The weighted AM-GM that converts the Schur weight condition of B30 into a bound
on the quadratic form.  Splitting the cross term with the *ratio of weights* is
what makes the two halves reassemble, after a change of variables, into the
guarded sum B30 already bounds.
-/

/-- **Weighted AM-GM.**  Splitting a cross term with any positive ratio. -/
theorem two_mul_abs_le {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * |u * v| ≤ (b / a) * u ^ 2 + (a / b) * v ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have h1 : 2 * (a * b) * |u * v| ≤ b ^ 2 * u ^ 2 + a ^ 2 * v ^ 2 := by
    rcases abs_cases (u * v) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      nlinarith [sq_nonneg (b * u - a * v), sq_nonneg (b * u + a * v)]
  rw [← sub_nonneg]
  have heq : (b / a) * u ^ 2 + (a / b) * v ^ 2 - 2 * |u * v|
      = (b ^ 2 * u ^ 2 + a ^ 2 * v ^ 2 - 2 * (a * b) * |u * v|) / (a * b) := by
    field_simp
  rw [heq]
  exact div_nonneg (by linarith) hab.le

/-- **The pointwise estimate.**  With the chain weight as the ratio, the cross
term is split into a piece carried at `x + β` and a piece carried at `x`. -/
theorem cross_le (hβ : 0 < β) {x : ℝ} (hx1 : x < 1) (hxβ : x + β < 1) (u v : ℝ) :
    2 * |u * v|
      ≤ (chainWeight β x / chainWeight β (x + β)) * u ^ 2
        + (chainWeight β (x + β) / chainWeight β x) * v ^ 2 :=
  two_mul_abs_le (chainWeight_pos β (x + β) hβ hxβ) (chainWeight_pos β x hβ hx1)

/-- The guarded ratios sum to `ν k`, by the Schur condition of B30 divided
through by the weight. -/
theorem ratio_sum (hβ : 0 < β) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (if x + β < 1 then chainWeight β (x + β) / chainWeight β x else 0)
      + (if β ≤ x then chainWeight β (x - β) / chainWeight β x else 0)
      = Cvs.Operator.chebFactor (chainLength β (chainBase β x)) := by
  have hw : 0 < chainWeight β x := chainWeight_pos β x hβ hx1
  have hdist : (if x + β < 1 then chainWeight β (x + β) / chainWeight β x else 0)
      + (if β ≤ x then chainWeight β (x - β) / chainWeight β x else 0)
      = ((if x + β < 1 then chainWeight β (x + β) else 0)
          + (if β ≤ x then chainWeight β (x - β) else 0)) / chainWeight β x := by
    by_cases h1 : x + β < 1 <;> by_cases h2 : β ≤ x <;> simp [h1, h2] <;> ring
  rw [hdist, Cvs.Operator.chainWeight_masked_sum hβ hx0 hx1]
  field_simp

/-- And so are bounded by `ν ⌈1/β⌉`. -/
theorem ratio_sum_le (hβ : 0 < β) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (if x + β < 1 then chainWeight β (x + β) / chainWeight β x else 0)
      + (if β ≤ x then chainWeight β (x - β) / chainWeight β x else 0)
      ≤ Cvs.Operator.chebFactor (cap 1 β) := by
  rw [ratio_sum hβ hx0 hx1]
  exact Cvs.Operator.chebFactor_monotone
    (chainLength_le_cap β (chainBase β x) hβ (chainBase_nonneg β x hβ hx0))

end Cvs.Operator
