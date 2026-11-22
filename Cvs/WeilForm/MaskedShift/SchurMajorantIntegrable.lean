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
import Cvs.WeilForm.MaskedShift.ChainTestFunctionL2
import Cvs.WeilForm.MaskedShift.ChainWeightRatiosBounded
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.SchurEstimateAssembled
import Cvs.WeilForm.MaskedShift.SchurIntegrability

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

open Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-! # B37: integrability of the majorants

Each majorant is dominated by `(1/sin(π/(m+1))) · f²` or its translate, both
integrable, so `Integrable.mono'` applies.  `Cvs.Operator.ratio_le` is the domination.
-/

/-- Abbreviation for the uniform ratio bound. -/
noncomputable def RB (β : ℝ) : ℝ := 1 / Real.sin (π / ((cap 1 β : ℝ) + 1))

theorem RB_nonneg (hβ : 0 < β) : 0 ≤ RB β :=
  le_of_lt (by unfold RB; exact one_div_pos.mpr (Cvs.Operator.sin_cap_pos hβ))

/-- `Hf` is dominated by `RB · (translate of f²)`. -/
theorem abs_Hf_le (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    ‖Hf β f x‖ ≤ RB β * (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ))) ^ 2 := by
  unfold Hf
  by_cases hm : rep x + β < 1
  · rw [if_pos hm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_of_lt (div_pos (chainWeight_pos β (rep x) hβ (rep_lt_one x))
        (chainWeight_pos β (rep x + β) hβ hm))), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Cvs.Operator.ratio_le hβ (by linarith [rep_nonneg x]) hm) (sq_nonneg _)
  · rw [if_neg hm]
    simp only [norm_zero]
    exact mul_nonneg (RB_nonneg hβ) (sq_nonneg _)

/-- `Hb` is dominated by `RB · f²`. -/
theorem abs_Hb_le (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    ‖Hb β f x‖ ≤ RB β * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := by
  unfold Hb
  by_cases hm : rep x + β < 1
  · rw [if_pos hm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_of_lt (div_pos (chainWeight_pos β (rep x + β) hβ hm)
        (chainWeight_pos β (rep x) hβ (rep_lt_one x)))), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Cvs.Operator.ratio_le hβ (rep_nonneg x) (rep_lt_one x)) (sq_nonneg _)
  · rw [if_neg hm]
    simp only [norm_zero]
    exact mul_nonneg (RB_nonneg hβ) (sq_nonneg _)

/-! ## Integrability -/

/-- `Hf` as an indicator, which is the form measurability arguments want. -/
theorem Hf_eq_indicator (β : ℝ) (f : L2) :
    Hf β f = (maskFwd β).indicator
      (fun x => (chainWeight β (rep x) / chainWeight β (rep x + β))
        * (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ))) ^ 2) := by
  funext x
  unfold Hf
  by_cases hm : rep x + β < 1
  · rw [if_pos hm, Set.indicator_of_mem (show x ∈ maskFwd β from hm)]
  · rw [if_neg hm, Set.indicator_of_notMem (show x ∉ maskFwd β from hm)]

theorem Hb_eq_indicator (β : ℝ) (f : L2) :
    Hb β f = (maskFwd β).indicator
      (fun x => (chainWeight β (rep x + β) / chainWeight β (rep x))
        * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2) := by
  funext x
  unfold Hb
  by_cases hm : rep x + β < 1
  · rw [if_pos hm, Set.indicator_of_mem (show x ∈ maskFwd β from hm)]
  · rw [if_neg hm, Set.indicator_of_notMem (show x ∉ maskFwd β from hm)]

/-- The shifted weight is measurable. -/
theorem measurable_cw_shift (β : ℝ) :
    Measurable fun x : AddCircle (1 : ℝ) => chainWeight β (rep x + β) :=
  (Cvs.Operator.measurable_chainWeight β).comp (Cvs.Operator.measurable_rep.add_const β)

/-- `f` composed with the shift is a.e. strongly measurable. -/
theorem aesm_f_shift (β : ℝ) (f : L2) :
    AEStronglyMeasurable
      (fun x : AddCircle (1 : ℝ) =>
        (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ)))) volume :=
  (Lp.aestronglyMeasurable f).comp_measurePreserving
    (measurePreserving_add_right volume ((β : ℝ) : AddCircle (1 : ℝ)))

theorem aesm_Hf (β : ℝ) (f : L2) : AEStronglyMeasurable (Hf β f) volume := by
  rw [Hf_eq_indicator]
  refine AEStronglyMeasurable.indicator ?_ (measurableSet_maskFwd β)
  exact (((Cvs.Operator.measurable_circleWeight β).div
    (measurable_cw_shift β)).aestronglyMeasurable).mul ((aesm_f_shift β f).pow 2)

theorem aesm_Hb (β : ℝ) (f : L2) : AEStronglyMeasurable (Hb β f) volume := by
  rw [Hb_eq_indicator]
  refine AEStronglyMeasurable.indicator ?_ (measurableSet_maskFwd β)
  exact (((measurable_cw_shift β).div
    (Cvs.Operator.measurable_circleWeight β)).aestronglyMeasurable).mul
    ((Lp.aestronglyMeasurable f).pow 2)

/-- **`Hf` is integrable**, dominated by `RB · (translate of f²)`. -/
theorem integrable_Hf (hβ : 0 < β) (f : L2) : Integrable (Hf β f) volume :=
  Integrable.mono' (((Cvs.Operator.integrable_sq_shift f β).const_mul (RB β)))
    (aesm_Hf β f) (Filter.Eventually.of_forall (abs_Hf_le hβ f))

/-- **`Hb` is integrable**, dominated by `RB · f²`. -/
theorem integrable_Hb (hβ : 0 < β) (f : L2) : Integrable (Hb β f) volume :=
  Integrable.mono' (((Cvs.Operator.integrable_sq f).const_mul (RB β)))
    (aesm_Hb β f) (Filter.Eventually.of_forall (abs_Hb_le hβ f))

/-! ## The folded backward term -/

/-- The backward-guarded term that `Cvs.Operator.integral_fwd_eq_bwd` produces. -/
noncomputable def Bw (β : ℝ) (f : L2) : AddCircle (1 : ℝ) → ℝ := fun x =>
  if β ≤ rep x then
    (chainWeight β (rep x - β) / chainWeight β (rep x))
      * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2
  else 0

theorem abs_Bw_le (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) :
    ‖Bw β f x‖ ≤ RB β * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2 := by
  unfold Bw
  by_cases hm : β ≤ rep x
  · have hsub : rep x - β < 1 := by linarith [rep_lt_one x]
    rw [if_pos hm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_of_lt (div_pos (chainWeight_pos β (rep x - β) hβ hsub)
        (chainWeight_pos β (rep x) hβ (rep_lt_one x)))), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Cvs.Operator.ratio_le hβ (rep_nonneg x) (rep_lt_one x)) (sq_nonneg _)
  · rw [if_neg hm]
    simp only [norm_zero]
    exact mul_nonneg (RB_nonneg hβ) (sq_nonneg _)

theorem aesm_Bw (β : ℝ) (f : L2) : AEStronglyMeasurable (Bw β f) volume := by
  have hind : Bw β f = {x : AddCircle (1 : ℝ) | β ≤ rep x}.indicator
      (fun x => (chainWeight β (rep x - β) / chainWeight β (rep x))
        * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2) := by
    funext x
    unfold Bw
    by_cases hm : β ≤ rep x
    · rw [if_pos hm,
        Set.indicator_of_mem (show x ∈ {y : AddCircle (1 : ℝ) | β ≤ rep y} from hm)]
    · rw [if_neg hm,
        Set.indicator_of_notMem (show x ∉ {y : AddCircle (1 : ℝ) | β ≤ rep y} from hm)]
  rw [hind]
  refine AEStronglyMeasurable.indicator ?_
    (Cvs.Operator.measurable_rep measurableSet_Ici)
  exact ((((Cvs.Operator.measurable_chainWeight β).comp
    (Cvs.Operator.measurable_rep.add_const (-β))).div
      (Cvs.Operator.measurable_circleWeight β)).aestronglyMeasurable).mul
    ((Lp.aestronglyMeasurable f).pow 2)

theorem Bw_nonneg (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) : 0 ≤ Bw β f x := by
  unfold Bw
  by_cases hm : β ≤ rep x
  · have hsub : rep x - β < 1 := by linarith [rep_lt_one x]
    rw [if_pos hm]
    exact mul_nonneg (le_of_lt (div_pos (chainWeight_pos β (rep x - β) hβ hsub)
      (chainWeight_pos β (rep x) hβ (rep_lt_one x)))) (sq_nonneg _)
  · rw [if_neg hm]

theorem Hb_nonneg (hβ : 0 < β) (f : L2) (x : AddCircle (1 : ℝ)) : 0 ≤ Hb β f x := by
  unfold Hb
  by_cases hm : rep x + β < 1
  · rw [if_pos hm]
    exact mul_nonneg (le_of_lt (div_pos (chainWeight_pos β (rep x + β) hβ hm)
      (chainWeight_pos β (rep x) hβ (rep_lt_one x)))) (sq_nonneg _)
  · rw [if_neg hm]

theorem integrable_Bw (hβ : 0 < β) (f : L2) : Integrable (Bw β f) volume :=
  Integrable.mono' ((Cvs.Operator.integrable_sq f).const_mul (RB β))
    (aesm_Bw β f) (Filter.Eventually.of_forall (abs_Bw_le hβ f))

end Cvs.Operator
