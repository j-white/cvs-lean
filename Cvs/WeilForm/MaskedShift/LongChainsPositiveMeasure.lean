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
# The long chains have positive measure

`testFun β ≠ 0` needs `longSet β` to be non-null.
-/

variable {β : ℝ}

/-- The width of the initial interval of long chains. -/
noncomputable def initWidth (β : ℝ) : ℝ := min β (1 - ((cap 1 β : ℝ) - 1) * β)

theorem initWidth_pos (hβ : 0 < β) : 0 < initWidth β := by
  have hcap : 1 ≤ cap 1 β := by
    unfold cap; rw [Nat.one_le_ceil_iff]; positivity
  refine lt_min hβ ?_
  -- `m - 1 < 1/β`, since `m = ⌈1/β⌉`
  have hlt : ((cap 1 β : ℝ) - 1) < 1 / β := by
    have h := Nat.ceil_lt_add_one (a := 1 / β) (by positivity)
    unfold cap at *
    linarith
  rw [sub_pos, ← lt_div_iff₀ hβ]
  simpa using hlt

/-- A point of the initial interval starts a long chain. -/
theorem mem_longSet_of_lt (hβ : 0 < β) (hβ1 : β < 1) {x : ℝ}
    (hx0 : 0 < x) (hxδ : x < initWidth β) :
    ((x : ℝ) : AddCircle (1 : ℝ)) ∈ longSet β := by
  have hcap : 1 ≤ cap 1 β := by
    unfold cap; rw [Nat.one_le_ceil_iff]; positivity
  have hxβ : x < β := lt_of_lt_of_le hxδ (min_le_left _ _)
  have hx1 : x < 1 := lt_trans hxβ hβ1
  -- the representative of `x` is `x`
  have hrep : rep ((x : ℝ) : AddCircle (1 : ℝ)) = x := rep_coe x hx0.le hx1
  -- it is the first point of its own chain
  have hpos : chainPos β x = 0 := by
    unfold chainPos
    rw [Nat.floor_eq_zero]
    exact (div_lt_one hβ).mpr hxβ
  have hbase : chainBase β x = x := by
    unfold chainBase; rw [hpos]; simp
  show chainLength β (chainBase β (rep ((x : ℝ) : AddCircle (1 : ℝ)))) = cap 1 β
  rw [hrep, hbase]
  refine (chainLength_eq_cap_iff β x hβ hx0.le hcap).mpr ?_
  have := lt_of_lt_of_le hxδ (min_le_right _ _)
  linarith

/-- **The long chains have positive measure.** -/
theorem volume_longSet_ne_zero (hβ : 0 < β) (hβ1 : β < 1) :
    (volume : Measure (AddCircle (1 : ℝ))) (longSet β) ≠ 0 := by
  intro hzero
  -- pull back along the covering map, which is measure preserving on `Ioc 0 1`
  have hmp := AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0
  have hpre : (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)))
      (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' longSet β) = 0 := by
    rw [← hmp.measure_preimage (measurableSet_longSet β).nullMeasurableSet] at hzero
    exact hzero
  -- but the preimage contains an interval of positive length
  have hsub : Set.Ioo (0 : ℝ) (min (initWidth β) 1)
      ⊆ Set.Ioc (0 : ℝ) (0 + 1) ∩ (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' longSet β) := by
    intro x hx
    obtain ⟨hx0, hxlt⟩ := hx
    refine ⟨⟨hx0, by simpa using (lt_of_lt_of_le hxlt (min_le_right _ _)).le⟩, ?_⟩
    exact mem_longSet_of_lt hβ hβ1 hx0 (lt_of_lt_of_le hxlt (min_le_left _ _))
  have hwpos : 0 < min (initWidth β) 1 := lt_min (initWidth_pos hβ) one_pos
  have hmeas : volume (Set.Ioo (0 : ℝ) (min (initWidth β) 1)) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp only [sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hwpos
  refine hmeas (measure_mono_null hsub ?_)
  rw [Measure.restrict_apply' measurableSet_Ioc] at hpre
  rwa [Set.inter_comm] at hpre

/-! ## Hence the test function is non-zero -/

/-- The chain weight is strictly positive on the circle. -/
theorem circleWeight_pos (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    0 < circleWeight β z :=
  chainWeight_pos β (rep z) hβ (rep_lt_one z)

/-- **The test function is not zero.**  It is strictly positive on `longSet`,
which has positive measure. -/
theorem testFun_ne_zero (hβ : 0 < β) (hβ1 : β < 1) : Cvs.Operator.testFun β ≠ 0 := by
  intro hzero
  refine volume_longSet_ne_zero hβ hβ1 ?_
  -- if `testFun = 0` then `testVal = 0` a.e., so `longSet` is null
  have hae : testVal β =ᵐ[volume] 0 := by
    have h1 := Cvs.Operator.coeFn_testFun β
    rw [hzero] at h1
    filter_upwards [h1.symm, Lp.coeFn_zero ℝ 2 (volume : Measure (AddCircle (1:ℝ)))]
      with x hx hz
    simp [hx]
  have hnull : volume {z | testVal β z ≠ 0} = 0 := by
    have := hae
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  refine measure_mono_null (fun z hz => ?_) hnull
  have : testVal β z = circleWeight β z := by
    unfold testVal; rw [Set.indicator_of_mem hz]
  simp only [Set.mem_ofPred_eq, this]
  exact (circleWeight_pos hβ z).ne'

end Cvs.Operator
