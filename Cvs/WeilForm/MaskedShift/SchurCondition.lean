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
import Cvs.WeilForm.MaskedShift.ChainEigenvectorPointwise
import Cvs.WeilForm.MaskedShift.ChainWeightEigenvector
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real

namespace Cvs.Operator

open Cvs.Operator Cvs.Operator Cvs.Operator

variable {β : ℝ}

/-!
# The Schur condition

The recurrence that produced the lower bound is also an upper-bound certificate.
-/

/-- **The masked hops of the chain weight sum to `ν k · w`.**  The same four
cases as `Cvs.Operator.masked_apply`, but for the bare weight, so no restriction to
long chains is needed. -/
theorem chainWeight_masked_sum (hβ : 0 < β) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (if x + β < 1 then chainWeight β (x + β) else 0)
      + (if β ≤ x then chainWeight β (x - β) else 0)
      = Cvs.Operator.chebFactor (chainLength β (chainBase β x)) * chainWeight β x := by
  by_cases hpos : 1 ≤ chainPos β x
  · have hbwd : β ≤ x := by
      by_contra hc
      push Not at hc
      have : chainPos β x = 0 := by
        unfold chainPos; rw [Nat.floor_eq_zero]; exact (div_lt_one hβ).mpr hc
      omega
    by_cases hfwd : x + β < 1
    · rw [if_pos hfwd, if_pos hbwd]
      have hrec := chainWeight_recurrence β x hβ hx0 hpos
      unfold Cvs.Operator.chebFactor
      linarith [hrec]
    · rw [if_neg hfwd, if_pos hbwd, zero_add]
      have hlast : chainPos β x + 1 = chainLength β (chainBase β x) := by
        have h1 := chainPos_lt_chainLength β x hβ hx1
        have h3 : ¬ (chainPos β x + 1 < chainLength β (chainBase β x)) := fun hc =>
          hfwd ((fwd_iff hβ).mpr hc)
        omega
      exact chainWeight_last β x hβ hpos hlast
  · -- first point of its chain
    have h0 : chainPos β x = 0 := by omega
    have hlt : x < β := by
      by_contra hc
      push Not at hc
      have : 1 ≤ chainPos β x := by
        unfold chainPos; rw [Nat.one_le_floor_iff]; exact (one_le_div hβ).mpr hc
      omega
    by_cases hfwd : x + β < 1
    · rw [if_pos hfwd, if_neg (by linarith), add_zero]
      exact chainWeight_first β x hβ hx0 h0
    · -- a chain of length one: both hops blocked, and `ν 1 = 0`
      rw [if_neg hfwd, if_neg (by linarith), add_zero]
      have hlen : chainLength β (chainBase β x) = 1 := by
        have h1 := chainPos_lt_chainLength β x hβ hx1
        have h3 : ¬ (chainPos β x + 1 < chainLength β (chainBase β x)) := fun hc =>
          hfwd ((fwd_iff hβ).mpr hc)
        omega
      rw [hlen]
      unfold Cvs.Operator.chebFactor
      norm_num

end Cvs.Operator
