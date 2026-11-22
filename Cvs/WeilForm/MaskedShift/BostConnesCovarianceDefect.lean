import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.AddCircle.Defs
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.WalkLinkEdgeStrips

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window satisfies the Bost–Connes covariance relation away from its edges

The defect `S b* S a − S a S b*` of `μ_n* μ_m = μ_m μ_n*` is `−X a b` (B5): by Cvs.WeilForm.MaskedShift.WalkLinkEdgeStrips the walk by `a − b` times
`1_{[1−a, 1−a+b)} − 1_{[0, b)}` for `0 ≤ b ≤ a`, `a + b ≤ 1`, zero on the interior `b ≤ rep < 1 − a`. Each walk fails
to be an isometry exactly at an edge: `S a* S a = 1_{rep ≥ a}`, against `μ_n* μ_n = 1`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Cvs.WeilForm.MaskedShift.BostConnesCovarianceDefect
open Cvs.Operator

open Cvs.Operator Cvs.WeilForm.MaskedShift.WalkLinkEdgeStrips

/-- The Bost–Connes defect of two walks: `S b* S a − S a S b*`. -/
def bcDefect (a b : ℝ≥0) : L2 →L[ℝ] L2 :=
  (ContinuousLinearMap.adjoint (Snn b)).comp (Snn a) - (Snn a).comp (ContinuousLinearMap.adjoint (Snn b))

/-- The defect is minus the commutator piece `X a b` of B5. -/
theorem bcDefect_eq_neg_X (a b : ℝ≥0) : bcDefect a b = -X Snn a b := by
  unfold bcDefect X
  rw [neg_sub]

/-- **The defect in coordinates**: for `0 ≤ b ≤ a`, `a + b ≤ 1`, it is the walk by the beat `a − b` times
`1_{[1−a, 1−a+b)} − 1_{[0, b)}`. -/
theorem coeFn_bcDefect {a b : ℝ≥0} (hba : (b : ℝ) ≤ a) (hab : (a : ℝ) + b ≤ 1) (f : L2) :
    (bcDefect a b f : T1 → ℝ) =ᵐ[volume] fun x =>
      ((if 1 - (a : ℝ) ≤ rep x ∧ rep x < 1 - a + b then 1 else 0) - (if rep x < b then 1 else 0))
        * (f : T1 → ℝ) (x + (((a : ℝ) - b : ℝ) : T1)) := by
  rw [bcDefect_eq_neg_X]
  have h1 := coeFn_X a b f
  have h2 := Lp.coeFn_neg (X Snn a b f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [neg_apply, hx2, Pi.neg_apply, hx1,
    linkMask_eq_edges b.coe_nonneg hba hab x]
  ring

/-- **Bost–Connes holds in the interior**: the defect vanishes almost everywhere on `b ≤ rep < 1 − a`. -/
theorem bcDefect_interior {a b : ℝ≥0} (hba : (b : ℝ) ≤ a) (hab : (a : ℝ) + b ≤ 1) (f : L2) :
    ∀ᵐ x ∂volume, (b : ℝ) ≤ rep x → rep x < 1 - a → (bcDefect a b f : T1 → ℝ) x = 0 := by
  filter_upwards [coeFn_bcDefect hba hab f] with x hx hb1 hb2
  rw [hx, if_neg (fun h => by linarith [h.1]), if_neg (by linarith)]
  ring

/-- The isometry defect of one walk: `S a* S a` is multiplication by `1_{rep ≥ a}`. -/
theorem coeFn_adjoint_S_comp_S {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (f : L2) :
    (((ContinuousLinearMap.adjoint (S a)).comp (S a)) f : T1 → ℝ) =ᵐ[volume] fun x =>
      (if a ≤ rep x then 1 else 0) * (f : T1 → ℝ) x := by
  have h1 := coeFn_adjoint_S a (S a f)
  have h2 := (quasi_shift (-a)).ae_eq_comp (coeFn_S a f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [ContinuousLinearMap.comp_apply, hx1]
  simp only [Function.comp_apply] at hx2
  have hneg : x + ((-a : ℝ) : T1) = x - (a : T1) := by rw [AddCircle.coe_neg, ← sub_eq_add_neg]
  have hback : x + ((-a : ℝ) : T1) + (a : T1) = x := by rw [hneg, sub_add_cancel]
  by_cases h : a ≤ rep x
  · have hr := rep_sub_step a x ha h
    have hm : x + ((-a : ℝ) : T1) ∈ maskFwd a := by
      rw [hneg]; simp only [maskFwd, Set.mem_ofPred_eq, hr]; linarith [rep_lt_one x]
    rw [Set.indicator_of_mem hm, hx2, Set.indicator_of_mem hm]
    simp only [Function.comp_apply, hback, if_pos h, one_mul]
  · push Not at h
    have hr := rep_sub_wrap a x ha1 h
    have hm : x + ((-a : ℝ) : T1) ∉ maskFwd a := by
      rw [hneg]; simp only [maskFwd, Set.mem_ofPred_eq, hr, not_lt]; linarith [rep_nonneg x]
    rw [Set.indicator_of_notMem hm, if_neg (not_le.2 h), zero_mul]

end Cvs.WeilForm.MaskedShift.BostConnesCovarianceDefect
