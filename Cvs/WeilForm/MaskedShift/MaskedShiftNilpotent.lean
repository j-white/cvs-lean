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

open MeasureTheory
open scoped NNReal

namespace Cvs.Operator

open Cvs.Operator Cvs.Operator

/-!
# The masked shift is nilpotent

The structural fact behind the norm law, in operator form rather than measure form: `S β` is
nilpotent of index `⌈1/β⌉`.
-/

/-- Beyond a full turn there is nothing left to shift: the mask is empty. -/
theorem maskFwd_eq_empty {β : ℝ} (hβ : 1 ≤ β) : maskFwd β = ∅ := by
  ext z
  simp only [maskFwd, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  linarith [rep_nonneg z]

/-- Hence the masked shift itself vanishes. -/
theorem S_eq_zero {β : ℝ} (hβ : 1 ≤ β) : S β = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  filter_upwards [coeFn_S β f] with x hx
  rw [hx, maskFwd_eq_empty hβ]
  simp

/-!
## What remains

`W β = S β + (S β)*` with `S β` a contraction (`‖maskCLM‖ ≤ 1`, `shift` an isometry) and `S β
^ m = 0`.
-/

end Cvs.Operator
