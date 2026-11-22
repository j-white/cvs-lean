import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Defs
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

open Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-! # B33: the quadratic form of the masked rotation, as an integral

The first step of the Schur estimate: write `⟪W f, f⟫` as an integral of the
guarded cross term.  Both `S` and its adjoint contribute the same amount, since
the form is real, so the whole quadratic form is twice the forward term.
-/

/-- `⟪S f, f⟫` as an integral of the guarded cross term. -/
theorem inner_S_eq_integral (β : ℝ) (f : L2) :
    inner ℝ (S β f) f
      = ∫ x : AddCircle (1 : ℝ),
          (maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
            * (f : AddCircle (1 : ℝ) → ℝ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_S β f] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- **The quadratic form is twice the forward term.**  `S` and `S*` contribute
equally because the inner product is real. -/
theorem inner_W_eq_two_mul (β : ℝ) (f : L2) :
    inner ℝ ((S β + ContinuousLinearMap.adjoint (S β)) f) f
      = 2 * inner ℝ (S β f) f := by
  rw [add_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  ring

/-- Hence the quadratic form as a single integral. -/
theorem inner_W_eq_integral (β : ℝ) (f : L2) :
    inner ℝ ((S β + ContinuousLinearMap.adjoint (S β)) f) f
      = 2 * ∫ x : AddCircle (1 : ℝ),
          (maskFwd β).indicator
            ((f : AddCircle (1 : ℝ) → ℝ) ∘ fun y => y + (β : AddCircle (1 : ℝ))) x
            * (f : AddCircle (1 : ℝ) → ℝ) x := by
  rw [inner_W_eq_two_mul, inner_S_eq_integral]

end Cvs.Operator
