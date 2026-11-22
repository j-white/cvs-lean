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

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The link between two walks: the beat, on two edge strips

For masked shifts `S a`, `S b`, the commutator piece `X a b = S a S b* − S b* S a` is a multiplication operator times
the translation by the beat `a − b`: `X a b f = linkMask a b · f(· + (a − b))`. For `0 ≤ b ≤ a` with `a + b ≤ 1` the
mask is `1_{[0, b)} − 1_{[1 − a, 1 − a + b)}`: the two walks interact only on two strips of width `b` at the edges.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Cvs.WeilForm.MaskedShift.WalkLinkEdgeStrips
open Cvs.Operator

open Cvs.Operator

/-- The link mask: `1_{F_a}(x)·1_{F_b}(x + a − b) − 1_{F_b}(x − b)·1_{F_a}(x − b)`, `F_β = maskFwd β`. -/
def linkMask (a b : ℝ) (x : T1) : ℝ :=
  (maskFwd a).indicator 1 x * (maskFwd b).indicator 1 (x + ((a - b : ℝ) : T1))
    - (maskFwd b).indicator 1 (x + ((-b : ℝ) : T1)) * (maskFwd a).indicator 1 (x + ((-b : ℝ) : T1))

/-- **The link is the beat on a mask**: `X a b f = linkMask a b · f(· + (a − b))`. -/
theorem coeFn_X (a b : ℝ≥0) (f : L2) :
    (X Snn a b f : T1 → ℝ) =ᵐ[volume]
      fun x => linkMask a b x * (f : T1 → ℝ) (x + (((a : ℝ) - b : ℝ) : T1)) := by
  have h1 := coeFn_S (a : ℝ) (ContinuousLinearMap.adjoint (S (b : ℝ)) f)
  have h2 := (quasi_shift (a : ℝ)).ae_eq_comp (coeFn_adjoint_S (b : ℝ) f)
  have h3 := coeFn_adjoint_S (b : ℝ) (S (a : ℝ) f)
  have h4 := (quasi_shift (-(b : ℝ))).ae_eq_comp (coeFn_S (a : ℝ) f)
  have h5 := Lp.coeFn_sub ((S (a : ℝ)).comp (ContinuousLinearMap.adjoint (S (b : ℝ))) f)
    ((ContinuousLinearMap.adjoint (S (b : ℝ))).comp (S (a : ℝ)) f)
  have hX : X Snn a b f = (S (a : ℝ)).comp (ContinuousLinearMap.adjoint (S (b : ℝ))) f
      - (ContinuousLinearMap.adjoint (S (b : ℝ))).comp (S (a : ℝ)) f := rfl
  rw [hX]
  filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
  rw [hx5, Pi.sub_apply]
  rw [show ((S (a : ℝ)).comp (ContinuousLinearMap.adjoint (S (b : ℝ))) f : T1 → ℝ) x
      = (S (a : ℝ) (ContinuousLinearMap.adjoint (S (b : ℝ)) f) : T1 → ℝ) x from rfl, hx1]
  rw [show ((ContinuousLinearMap.adjoint (S (b : ℝ))).comp (S (a : ℝ)) f : T1 → ℝ) x
      = (ContinuousLinearMap.adjoint (S (b : ℝ)) (S (a : ℝ) f) : T1 → ℝ) x from rfl, hx3]
  simp only [Function.comp_apply] at hx2 hx4
  have e1 : x + ((a : ℝ) : T1) + ((-(b : ℝ) : ℝ) : T1) = x + (((a : ℝ) - b : ℝ) : T1) := by
    rw [add_assoc, ← AddCircle.coe_add]; ring_nf
  have e2 : x + ((-(b : ℝ) : ℝ) : T1) + ((a : ℝ) : T1) = x + (((a : ℝ) - b : ℝ) : T1) := by
    rw [add_assoc, ← AddCircle.coe_add]; ring_nf
  rw [e1] at hx2
  unfold linkMask
  classical
  simp only [Set.indicator_apply] at hx2
  simp only [Set.indicator_apply, Function.comp_apply] at hx4
  simp only [Set.indicator_apply, Function.comp_apply, Pi.one_apply]
  rw [e2] at hx4
  rw [hx2, hx4]
  split_ifs <;> ring

/-- **The link mask in coordinates**: for `0 ≤ b ≤ a ≤ 1`,
`linkMask a b x = 1{rep x + a < 1} − 1{b ≤ rep x ∧ rep x − b + a < 1}`. -/
theorem linkMask_eq {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) (x : T1) :
    linkMask a b x = (if rep x + a < 1 then 1 else 0)
      - (if b ≤ rep x ∧ rep x - b + a < 1 then 1 else 0) := by
  have hd : 0 ≤ a - b := by linarith
  unfold linkMask
  congr 1
  · by_cases h : rep x + a < 1
    · have hstep : rep x + (a - b) < 1 := by linarith
      have hr := rep_add_step (a - b) x hd hstep
      have hxa : x ∈ maskFwd a := by simp [maskFwd, h]
      have hxb : x + ((a - b : ℝ) : T1) ∈ maskFwd b := by
        simp only [maskFwd, Set.mem_ofPred_eq, hr]; linarith
      rw [Set.indicator_of_mem hxa, Set.indicator_of_mem hxb]; simp [h]
    · have hxa : x ∉ maskFwd a := by simp [maskFwd, h]
      simp [Set.indicator_of_notMem hxa, h]
  · by_cases hbr : b ≤ rep x
    · have hr := rep_sub_step b x hb hbr
      have hneg : x + ((-b : ℝ) : T1) = x - (b : T1) := by
        rw [AddCircle.coe_neg, ← sub_eq_add_neg]
      have hxb : x + ((-b : ℝ) : T1) ∈ maskFwd b := by
        rw [hneg]; simp only [maskFwd, Set.mem_ofPred_eq, hr]; linarith [rep_lt_one x]
      by_cases h : rep x - b + a < 1
      · have hxa : x + ((-b : ℝ) : T1) ∈ maskFwd a := by
          rw [hneg]; simp only [maskFwd, Set.mem_ofPred_eq, hr]; exact h
        rw [Set.indicator_of_mem hxa, Set.indicator_of_mem hxb]; simp [hbr, h]
      · have hxa : x + ((-b : ℝ) : T1) ∉ maskFwd a := by
          rw [hneg]; simp only [maskFwd, Set.mem_ofPred_eq, hr]; exact h
        rw [Set.indicator_of_notMem hxa]; simp [hbr, h]
    · push Not at hbr
      have hr := rep_sub_wrap b x (by linarith) hbr
      have hneg : x + ((-b : ℝ) : T1) = x - (b : T1) := by
        rw [AddCircle.coe_neg, ← sub_eq_add_neg]
      have hxb : x + ((-b : ℝ) : T1) ∉ maskFwd b := by
        rw [hneg]; simp only [maskFwd, Set.mem_ofPred_eq, hr, not_lt]; linarith [rep_nonneg x]
      rw [Set.indicator_of_notMem hxb]; simp [not_le.2 hbr]

/-- **The link lives on two edge strips**: for `0 ≤ b ≤ a` and `a + b ≤ 1`,
`linkMask a b = 1_{[0, b)} − 1_{[1 − a, 1 − a + b)}` in the coordinate `rep`. -/
theorem linkMask_eq_edges {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) (x : T1) :
    linkMask a b x = (if rep x < b then 1 else 0)
      - (if 1 - a ≤ rep x ∧ rep x < 1 - a + b then 1 else 0) := by
  rw [linkMask_eq hb hba (by linarith)]
  rcases lt_or_ge (rep x) b with h1 | h1
  · rw [if_pos (by linarith), if_neg (fun h => by linarith [h.1]), if_pos h1,
      if_neg (fun h => by linarith [h.1])]
  · rcases lt_or_ge (rep x) (1 - a) with h2 | h2
    · rw [if_pos (by linarith), if_pos ⟨h1, by linarith⟩, if_neg (by linarith),
        if_neg (fun h => by linarith [h.1])]
      norm_num
    · rcases lt_or_ge (rep x) (1 - a + b) with h3 | h3
      · rw [if_neg (by linarith), if_pos ⟨h1, by linarith⟩, if_neg (by linarith),
          if_pos ⟨h2, h3⟩]
      · rw [if_neg (by linarith), if_neg (fun h => by linarith [h.2]), if_neg (by linarith),
          if_neg (fun h => by linarith [h.2])]

end Cvs.WeilForm.MaskedShift.WalkLinkEdgeStrips
