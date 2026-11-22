import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Basic.NNReal.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Defs
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose

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

/-! # B35: integrability for the Schur estimate

Every integrand in the estimate is a bounded multiple of `f²` or of its
translate, and both are integrable because `f ∈ L²` and translation preserves
the measure.  `Cvs.Operator.ratio_le` supplies the bound.
-/

/-- `f²` is integrable for `f ∈ L²`. -/
theorem integrable_sq (f : L2) :
    Integrable (fun x : AddCircle (1 : ℝ) => (f : AddCircle (1 : ℝ) → ℝ) x ^ 2) volume :=
  (Lp.memLp f).integrable_sq

/-- Its translate is too, since translation preserves the measure. -/
theorem integrable_sq_shift (f : L2) (a : ℝ) :
    Integrable (fun x : AddCircle (1 : ℝ) =>
      (f : AddCircle (1 : ℝ) → ℝ) (x + (a : AddCircle (1 : ℝ))) ^ 2) volume := by
  have hmp : MeasurePreserving (fun x : AddCircle (1 : ℝ) => x + (a : AddCircle (1 : ℝ)))
      volume volume := measurePreserving_add_right volume ((a : ℝ) : AddCircle (1 : ℝ))
  exact (hmp.integrable_comp (integrable_sq f).aestronglyMeasurable).mpr (integrable_sq f)

/-! ## The change of variables

The forward half of the estimate carries `f(x+β)²`; translating by `-β` moves it
onto `x`, and `mem_maskFwd_sub_iff` turns the forward mask into the backward one.
-/

/-- **Folding the forward half onto `x`.**  For any bounded measurable `F`,
translation by `β` is measure preserving, so the integral of `F(x+β)` equals the
integral of `F`. -/
theorem integral_shift (F : AddCircle (1 : ℝ) → ℝ) (a : ℝ) :
    ∫ x : AddCircle (1 : ℝ), F (x + (a : AddCircle (1 : ℝ)))
      = ∫ x : AddCircle (1 : ℝ), F x :=
  (measurePreserving_add_right volume ((a : ℝ) : AddCircle (1 : ℝ))).integral_comp
    (MeasurableEquiv.addRight ((a : ℝ) : AddCircle (1 : ℝ))).measurableEmbedding F

/-- The forward-guarded weighted term, moved to `x`.  Both the mask and the
weight ratio become their backward counterparts. -/
theorem integral_fwd_eq_bwd (hβ : 0 < β) (hβ1 : β < 1) (f : L2) :
    ∫ x : AddCircle (1 : ℝ),
        (if rep x + β < 1 then
            (chainWeight β (rep x) / chainWeight β (rep x + β))
              * (f : AddCircle (1 : ℝ) → ℝ) (x + (β : AddCircle (1 : ℝ))) ^ 2
          else 0)
      = ∫ x : AddCircle (1 : ℝ),
        (if β ≤ rep x then
            (chainWeight β (rep x - β) / chainWeight β (rep x))
              * (f : AddCircle (1 : ℝ) → ℝ) x ^ 2
          else 0) := by
  rw [← integral_shift (fun y : AddCircle (1 : ℝ) => if β ≤ rep y then
      (chainWeight β (rep y - β) / chainWeight β (rep y))
        * (f : AddCircle (1 : ℝ) → ℝ) y ^ 2 else 0) β]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  by_cases hm : rep x + β < 1
  · have hrep : rep (x + (β : AddCircle (1 : ℝ))) = rep x + β :=
      rep_add_step β x hβ.le hm
    have hcond : β ≤ rep (x + (β : AddCircle (1 : ℝ))) := by
      rw [hrep]; linarith [rep_nonneg x]
    rw [ite_eq_left hm, ite_eq_left hcond, hrep]
    rw [show rep x + β - β = rep x by ring]
  · push Not at hm
    have hrep : rep (x + (β : AddCircle (1 : ℝ))) = rep x + β - 1 :=
      rep_add_wrap β x hβ1.le hm
    have hcond : ¬ (β ≤ rep (x + (β : AddCircle (1 : ℝ)))) := by
      rw [hrep]; push Not; linarith [rep_lt_one x]
    rw [ite_eq_right (not_lt.mpr hm), ite_eq_right hcond]

end Cvs.Operator
