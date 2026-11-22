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
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.PointwiseSchurEstimate

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped NNReal

namespace Cvs.Operator

open Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-! # B36: the Schur estimate assembled

`|⟪W f, f⟫| ≤ ν ⌈1/β⌉ · ‖f‖²`, by chaining the pieces:
`cross_le` under the integral, `integral_fwd_eq_bwd` to fold the forward half
onto `x`, and `ratio_sum_le` to collect.
-/

/-- The `L²` norm squared as an integral. -/
theorem norm_sq_eq_integral (f : L2) :
    ‖f‖ ^ 2 = ∫ x : AddCircle (1 : ℝ), (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-- The forward-weighted majorant. -/
noncomputable def Hf (β : ℝ) (f : L2) : AddCircle (1 : ℝ) → ℝ := fun x =>
  if rep x + β < 1 then
    (chainWeight β (rep x) / chainWeight β (rep x + β))
      * (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ))) ^ 2
  else 0

/-- The backward-weighted majorant. -/
noncomputable def Hb (β : ℝ) (f : L2) : AddCircle (1 : ℝ) → ℝ := fun x =>
  if rep x + β < 1 then
    (chainWeight β (rep x + β) / chainWeight β (rep x))
      * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2
  else 0

/-- **The pointwise majorisation.**  Twice the guarded cross term is at most the
two weighted majorants, by `Cvs.Operator.cross_le`. -/
theorem two_abs_cross_le (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    2 * |(maskFwd β).indicator
          ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
        * (f : AddCircle (1 : ℝ) → ℝ) x|
      ≤ Hf β f x + Hb β f x := by
  unfold Hf Hb
  by_cases hm : rep x + β < 1
  · have hmem : x ∈ maskFwd β := hm
    rw [Set.indicator_of_mem hmem, if_pos hm, if_pos hm, Function.comp_apply]
    exact Cvs.Operator.cross_le hβ (rep_lt_one x) hm _ _
  · have hmem : x ∉ maskFwd β := hm
    rw [Set.indicator_of_notMem hmem, if_neg hm, if_neg hm]
    simp

/-- Collecting the two majorants gives `ν ⌈1/β⌉ · f²`. -/
theorem Hsum_le (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    (if β ≤ rep x then
        (chainWeight β (rep x - β) / chainWeight β (rep x))
          * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 else 0) + Hb β f x
      ≤ Cvs.Operator.chebFactor (cap 1 (β : ℝ)) * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := by
  unfold Hb
  have hratio := Cvs.Operator.ratio_sum_le hβ (rep_nonneg x) (rep_lt_one x)
  have hsq : (0 : ℝ) ≤ (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := sq_nonneg _
  by_cases h1 : rep x + β < 1 <;> by_cases h2 : β ≤ rep x <;>
    simp only [h1, h2, if_true, if_false, add_zero, zero_add] <;>
    simp only [h1, h2, if_true, if_false] at hratio <;> nlinarith [hratio, hsq]

end Cvs.Operator
