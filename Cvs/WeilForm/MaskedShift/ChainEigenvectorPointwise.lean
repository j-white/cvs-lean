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
import Cvs.WeilForm.MaskedShift.AdmissibleStepsOnChain
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

open Cvs.Operator Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-! # B28: the eigenvector equation, pointwise

The mask condition and the chain position are the same condition: a forward hop
is admissible exactly when the point is not the last of its chain.  With that,
the four cases of B24 close the pointwise identity.
-/

/-- **The forward mask is the chain condition.**  `rep z + β < 1` exactly when
the position is not the last on the chain. -/
theorem fwd_iff (hβ : 0 < β) {x : ℝ} :
    x + β < 1 ↔ chainPos β x + 1 < chainLength β (chainBase β x) := by
  have hbase := chainBase_add β x
  rw [chainLength, Nat.lt_ceil]
  constructor
  · intro h
    rw [lt_div_iff₀ hβ]
    push_cast
    nlinarith [hbase]
  · intro h
    rw [lt_div_iff₀ hβ] at h
    push_cast at h
    nlinarith [hbase]

/-- **Interior of a long chain.**  Both hops are admissible and the recurrence
gives `ν m · w`. -/
theorem masked_apply_interior (hβ : 0 < β) {z : AddCircle (1 : ℝ)}
    (hz : z ∈ longSet β) (hpos : 1 ≤ chainPos β (rep z))
    (hfwd : rep z + β < 1) :
    (if rep z + β < 1 then testVal β (z + (β : AddCircle (1 : ℝ))) else 0)
      + (if β ≤ rep z then testVal β (z - (β : AddCircle (1 : ℝ))) else 0)
      = Cvs.Operator.chebFactor (cap 1 β) * testVal β z := by
  have hbwd : β ≤ rep z := by
    by_contra hc
    push Not at hc
    have : chainPos β (rep z) = 0 := by
      unfold chainPos; rw [Nat.floor_eq_zero]; exact (div_lt_one hβ).mpr hc
    omega
  rw [if_pos hfwd, if_pos hbwd, testVal_add hβ hfwd hz, testVal_sub hβ hbwd hz]
  have hval : testVal β z = chainWeight β (rep z) := by
    unfold testVal circleWeight; rw [Set.indicator_of_mem hz]
  rw [hval, ← (hz : chainLength β (chainBase β (rep z)) = cap 1 β)]
  have hrec := chainWeight_recurrence β (rep z) hβ (rep_nonneg z) hpos
  unfold Cvs.Operator.chebFactor
  linarith [hrec]

/-- **Last point of a long chain.**  The forward hop is masked off and the
backward hop alone gives `ν m · w`. -/
theorem masked_apply_last (hβ : 0 < β) {z : AddCircle (1 : ℝ)}
    (hz : z ∈ longSet β) (hpos : 1 ≤ chainPos β (rep z))
    (hfwd : ¬ (rep z + β < 1)) :
    (if rep z + β < 1 then testVal β (z + (β : AddCircle (1 : ℝ))) else 0)
      + (if β ≤ rep z then testVal β (z - (β : AddCircle (1 : ℝ))) else 0)
      = Cvs.Operator.chebFactor (cap 1 β) * testVal β z := by
  have hbwd : β ≤ rep z := by
    by_contra hc
    push Not at hc
    have : chainPos β (rep z) = 0 := by
      unfold chainPos; rw [Nat.floor_eq_zero]; exact (div_lt_one hβ).mpr hc
    omega
  -- not admissible forward means last on the chain
  have hlast : chainPos β (rep z) + 1 = chainLength β (chainBase β (rep z)) := by
    have h1 := chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)
    have h2 := (fwd_iff (x := rep z) hβ).not.mpr
    have h3 : ¬ (chainPos β (rep z) + 1 < chainLength β (chainBase β (rep z))) := by
      intro hc
      exact hfwd ((fwd_iff (x := rep z) hβ).mpr hc)
    omega
  rw [if_neg hfwd, if_pos hbwd, zero_add, testVal_sub hβ hbwd hz]
  have hval : testVal β z = chainWeight β (rep z) := by
    unfold testVal circleWeight; rw [Set.indicator_of_mem hz]
  rw [hval, ← (hz : chainLength β (chainBase β (rep z)) = cap 1 β)]
  exact Cvs.Operator.chainWeight_last β (rep z) hβ hpos hlast

/-- **The eigenvector equation, pointwise.**  At every point of the circle,
`(admissible forward) + (admissible backward) = ν ⌈1/β⌉ · testVal`. -/
theorem masked_apply (hβ : 0 < β) (hβ1 : β < 1) (z : AddCircle (1 : ℝ)) :
    (if rep z + β < 1 then testVal β (z + (β : AddCircle (1 : ℝ))) else 0)
      + (if β ≤ rep z then testVal β (z - (β : AddCircle (1 : ℝ))) else 0)
      = Cvs.Operator.chebFactor (cap 1 β) * testVal β z := by
  by_cases hz : z ∈ longSet β
  · by_cases hpos : 1 ≤ chainPos β (rep z)
    · by_cases hfwd : rep z + β < 1
      · exact masked_apply_interior hβ hz hpos hfwd
      · exact masked_apply_last hβ hz hpos hfwd
    · -- first point: `chainPos = 0`, and the chain is long so the hop is allowed
      have h0 : chainPos β (rep z) = 0 := by omega
      have hcap2 : 2 ≤ cap 1 β := by
        unfold cap
        have : (1 : ℝ) < 1 / β := by rw [lt_div_iff₀ hβ]; linarith
        exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr (by simpa using this))
      have hfwd : rep z + β < 1 := by
        refine (fwd_iff (x := rep z) hβ).mpr ?_
        rw [h0, (hz : chainLength β (chainBase β (rep z)) = cap 1 β)]
        omega
      exact masked_apply_first hβ hz h0 hfwd
  · rw [masked_apply_of_notMem hβ hz]
    have : testVal β z = 0 := Set.indicator_of_notMem hz _
    rw [this, mul_zero]

end Cvs.Operator
