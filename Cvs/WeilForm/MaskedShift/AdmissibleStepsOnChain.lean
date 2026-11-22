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
import Cvs.WeilForm.MaskedShift.ChainWeightEigenvector
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
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

variable {β : ℝ}

/-! # B27: admissible steps stay on the chain

The join between the pointwise identity (B24) and the operator (B20).  An
admissible hop preserves `chainBase`, hence preserves membership in `longSet`
and the value of the test function.
-/

/-- Being at or beyond `β` means being past the first point of a chain. -/
theorem one_le_chainPos_of_le (hβ : 0 < β) {x : ℝ} (h : β ≤ x) :
    1 ≤ chainPos β x := by
  unfold chainPos
  rw [Nat.one_le_floor_iff]
  exact (one_le_div hβ).mpr h

/-- **A forward hop stays on the same chain.** -/
theorem longSet_add (hβ : 0 < β) {z : AddCircle (1 : ℝ)} (h : rep z + β < 1) :
    (z + (β : AddCircle (1 : ℝ)) ∈ longSet β) ↔ (z ∈ longSet β) := by
  have hrep : rep (z + (β : AddCircle (1 : ℝ))) = rep z + β :=
    rep_add_step β z hβ.le h
  simp only [longSet, Set.mem_ofPred_eq, hrep,
    chainBase_add_step β (rep z) hβ (rep_nonneg z)]

/-- **A backward hop stays on the same chain.** -/
theorem longSet_sub (hβ : 0 < β) {z : AddCircle (1 : ℝ)} (h : β ≤ rep z) :
    (z - (β : AddCircle (1 : ℝ)) ∈ longSet β) ↔ (z ∈ longSet β) := by
  have hrep : rep (z - (β : AddCircle (1 : ℝ))) = rep z - β :=
    rep_sub_step β z hβ.le h
  have hpos : 1 ≤ chainPos β (rep z) := one_le_chainPos_of_le hβ h
  simp only [longSet, Set.mem_ofPred_eq, hrep,
    chainBase_sub_step β (rep z) hβ hpos]

/-! ## The test function transported along a hop -/

/-- On a long chain, a forward hop lands on the chain weight. -/
theorem testVal_add (hβ : 0 < β) {z : AddCircle (1 : ℝ)} (h : rep z + β < 1)
    (hz : z ∈ longSet β) :
    testVal β (z + (β : AddCircle (1 : ℝ))) = chainWeight β (rep z + β) := by
  have hmem : z + (β : AddCircle (1 : ℝ)) ∈ longSet β := (longSet_add hβ h).mpr hz
  unfold testVal circleWeight
  rw [Set.indicator_of_mem hmem, rep_add_step β z hβ.le h]

/-- On a long chain, a backward hop lands on the chain weight. -/
theorem testVal_sub (hβ : 0 < β) {z : AddCircle (1 : ℝ)} (h : β ≤ rep z)
    (hz : z ∈ longSet β) :
    testVal β (z - (β : AddCircle (1 : ℝ))) = chainWeight β (rep z - β) := by
  have hmem : z - (β : AddCircle (1 : ℝ)) ∈ longSet β := (longSet_sub hβ h).mpr hz
  unfold testVal circleWeight
  rw [Set.indicator_of_mem hmem, rep_sub_step β z hβ.le h]

/-- Off the long chains, a hop stays off them, so the test function vanishes. -/
theorem testVal_add_of_notMem (hβ : 0 < β) {z : AddCircle (1 : ℝ)}
    (h : rep z + β < 1) (hz : z ∉ longSet β) :
    testVal β (z + (β : AddCircle (1 : ℝ))) = 0 := by
  unfold testVal
  exact Set.indicator_of_notMem (fun hc => hz ((longSet_add hβ h).mp hc)) _

theorem testVal_sub_of_notMem (hβ : 0 < β) {z : AddCircle (1 : ℝ)}
    (h : β ≤ rep z) (hz : z ∉ longSet β) :
    testVal β (z - (β : AddCircle (1 : ℝ))) = 0 := by
  unfold testVal
  exact Set.indicator_of_notMem (fun hc => hz ((longSet_sub hβ h).mp hc)) _

/-!
## The pointwise eigenvector equation

The masked rotation acts on `testVal` at a point as
-/

/-- **Off the long chains the masked rotation gives zero.** -/
theorem masked_apply_of_notMem (hβ : 0 < β) {z : AddCircle (1 : ℝ)}
    (hz : z ∉ longSet β) :
    (if rep z + β < 1 then testVal β (z + (β : AddCircle (1 : ℝ))) else 0)
      + (if β ≤ rep z then testVal β (z - (β : AddCircle (1 : ℝ))) else 0) = 0 := by
  by_cases h1 : rep z + β < 1 <;> by_cases h2 : β ≤ rep z
  · rw [if_pos h1, if_pos h2, testVal_add_of_notMem hβ h1 hz,
      testVal_sub_of_notMem hβ h2 hz]; ring
  · rw [if_pos h1, if_neg h2, testVal_add_of_notMem hβ h1 hz]; ring
  · rw [if_neg h1, if_pos h2, testVal_sub_of_notMem hβ h2 hz]; ring
  · rw [if_neg h1, if_neg h2]; ring

/-- **On a long chain, the first point.**  The backward hop is masked off and the
forward hop alone gives `ν m · w`. -/
theorem masked_apply_first (hβ : 0 < β) {z : AddCircle (1 : ℝ)}
    (hz : z ∈ longSet β) (h0 : chainPos β (rep z) = 0)
    (hfwd : rep z + β < 1) :
    (if rep z + β < 1 then testVal β (z + (β : AddCircle (1 : ℝ))) else 0)
      + (if β ≤ rep z then testVal β (z - (β : AddCircle (1 : ℝ))) else 0)
      = Cvs.Operator.chebFactor (cap 1 β) * testVal β z := by
  -- `chainPos = 0` means `rep z < β`, so the backward hop is masked off
  have hlt : rep z < β := by
    by_contra hc
    push Not at hc
    have := one_le_chainPos_of_le hβ hc
    omega
  rw [if_pos hfwd, if_neg (by linarith), add_zero,
    testVal_add hβ hfwd hz]
  have hval : testVal β z = chainWeight β (rep z) := by
    unfold testVal circleWeight; rw [Set.indicator_of_mem hz]
  rw [hval]
  have hk : chainLength β (chainBase β (rep z)) = cap 1 β := hz
  rw [← hk]
  exact Cvs.Operator.chainWeight_first β (rep z) hβ (rep_nonneg z) h0

end Cvs.Operator
