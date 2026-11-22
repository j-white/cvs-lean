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

namespace Cvs.Operator

open Cvs.Operator Cvs.Operator Cvs.Operator

/-!
# The test function, in `L²`
-/

/-- The representative map is measurable. -/
theorem measurable_rep : Measurable (rep : AddCircle (1 : ℝ) → ℝ) :=
  measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (T := (1 : ℝ)) 0).measurable

/-- The chain weight, transported to the circle. -/
noncomputable def circleWeight (β : ℝ) (z : AddCircle (1 : ℝ)) : ℝ :=
  chainWeight β (rep z)

/-- The points whose chain has full length. -/
def longSet (β : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {z | chainLength β (chainBase β (rep z)) = cap 1 β}

/-- The test function: the chain weight on the long chains, zero elsewhere. -/
noncomputable def testVal (β : ℝ) : AddCircle (1 : ℝ) → ℝ :=
  (longSet β).indicator (circleWeight β)

/-! ## Measurability -/

theorem measurable_chainPos (β : ℝ) : Measurable (chainPos β) := by
  unfold chainPos
  exact Measurable.nat_floor (measurable_id.div_const β)

theorem measurable_chainBase (β : ℝ) : Measurable (chainBase β) := by
  unfold chainBase
  have hj : Measurable fun y : ℝ => ((chainPos β y : ℕ) : ℝ) :=
    measurable_from_top.comp (measurable_chainPos β)
  exact measurable_id.sub (hj.mul_const β)

theorem measurable_chainLength (β : ℝ) : Measurable (chainLength β) := by
  unfold chainLength
  exact Measurable.nat_ceil ((measurable_const.sub measurable_id).div_const β)

theorem measurableSet_longSet (β : ℝ) : MeasurableSet (longSet β) :=
  ((measurable_chainLength β).comp
    ((measurable_chainBase β).comp measurable_rep)) (measurableSet_singleton _)

/-- The chain weight is measurable as a function on `ℝ`. -/
theorem measurable_chainWeight (β : ℝ) : Measurable (chainWeight β) := by
  unfold chainWeight
  have hj : Measurable fun y : ℝ => ((chainPos β y : ℕ) : ℝ) :=
    measurable_from_top.comp (measurable_chainPos β)
  have hk : Measurable fun y : ℝ => ((chainLength β (chainBase β y) : ℕ) : ℝ) :=
    measurable_from_top.comp ((measurable_chainLength β).comp (measurable_chainBase β))
  exact Real.measurable_sin.comp (((hj.add_const 1).mul_const π).div (hk.add_const 1))

theorem measurable_circleWeight (β : ℝ) : Measurable (circleWeight β) := by
  unfold circleWeight chainWeight
  have hj : Measurable fun z : AddCircle (1:ℝ) => ((chainPos β (rep z) : ℕ) : ℝ) :=
    measurable_from_top.comp ((measurable_chainPos β).comp measurable_rep)
  have hk : Measurable fun z : AddCircle (1:ℝ) =>
      ((chainLength β (chainBase β (rep z)) : ℕ) : ℝ) :=
    measurable_from_top.comp
      ((measurable_chainLength β).comp ((measurable_chainBase β).comp measurable_rep))
  exact Real.measurable_sin.comp
    (((hj.add_const 1).mul_const π).div (hk.add_const 1))

theorem measurable_testVal (β : ℝ) : Measurable (testVal β) :=
  (measurable_circleWeight β).indicator (measurableSet_longSet β)

/-! ## Boundedness, hence `L²` -/

/-- The chain weight is a sine, so the test function is bounded by one. -/
theorem abs_testVal_le_one (β : ℝ) (z : AddCircle (1 : ℝ)) : |testVal β z| ≤ 1 := by
  unfold testVal
  by_cases h : z ∈ longSet β
  · rw [Set.indicator_of_mem h]
    unfold circleWeight chainWeight
    exact Real.abs_sin_le_one _
  · rw [Set.indicator_of_notMem h]
    simp

/-- **The test function lies in `L²`.**  Bounded and measurable on a finite
measure space. -/
theorem memLp_testVal (β : ℝ) :
    MemLp (testVal β) 2 (volume : Measure (AddCircle (1 : ℝ))) :=
  MemLp.of_bound (measurable_testVal β).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using abs_testVal_le_one β z)

/-- The test function as an element of `L²(𝕋)`. -/
noncomputable def testFun (β : ℝ) : L2 := (memLp_testVal β).toLp _

theorem coeFn_testFun (β : ℝ) :
    (testFun β : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] testVal β :=
  MemLp.coeFn_toLp _

end Cvs.Operator
