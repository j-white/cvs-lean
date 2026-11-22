import Mathlib
import Cvs.Prolate.GevreyTailCircle
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.WindowVacuumRieszMean

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Two walks in the vacuum: the connected correlation in closed form

For `0 ≤ a, b ≤ 1` and `W β = S β + S β*`, `⟨1, W a W b 1⟩ = 2(1 − a − b)₊ + 2(1 − max a b)` and `⟨1, W β 1⟩ = 2(1 − β)`,
so the connected correlation is `2(1 − a − b)₊ + 2(1 − max a b) − 4(1 − a)(1 − b)`, which is `2(min a b − 2ab)` when
`a + b ≤ 1`: with `a = log p/log c`, `b = log q/log c`, how the window's edges correlate two prime walks.
-/

noncomputable section

open MeasureTheory Real

namespace Cvs.WeilForm.VacuumTwoWalkCorrelation

open Cvs.Operator Cvs.WeilForm.WindowVacuumRieszMean

/-- The integral of the indicator of `{β ≤ rep}` is `1 − β`. -/
theorem integral_indicator_ge {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∫ z : T1, (if β ≤ rep z then (1 : ℝ) else 0) = 1 - β := by
  have h : (fun z : T1 => if β ≤ rep z then (1 : ℝ) else 0)
      = fun z => 1 - (maskFwd (1 - β)).indicator (fun _ => (1 : ℝ)) z := by
    funext z
    by_cases hz : β ≤ rep z
    · rw [if_pos hz, Set.indicator_of_notMem (show z ∉ maskFwd (1 - β) by
        simp only [maskFwd, Set.mem_ofPred_eq, not_lt]; linarith)]; ring
    · rw [if_neg hz, Set.indicator_of_mem (show z ∈ maskFwd (1 - β) by
        simp only [maskFwd, Set.mem_ofPred_eq]; linarith)]; ring
  rw [h, integral_sub (integrable_const _), integral_indicator_maskFwd (by linarith) (by linarith)]
  · rw [integral_const, measureReal_def, AddCircle.measure_univ]; simp
  · exact (integrable_const (1 : ℝ)).indicator (measurableSet_maskFwd _)

/-- `S β 1 = 1_{rep < 1 − β}`. -/
theorem coeFn_S_vac (β : ℝ) :
    (S β vac : T1 → ℝ) =ᵐ[volume] fun z => if rep z + β < 1 then 1 else 0 := by
  have h2 := (quasi_shift β).ae_eq_comp coeFn_vac
  filter_upwards [coeFn_S β vac, h2] with x hx hx2
  rw [hx]
  simp only [Function.comp_apply] at hx2
  by_cases hm : x ∈ maskFwd β
  · rw [Set.indicator_of_mem hm, Function.comp_apply, hx2, if_pos (show rep x + β < 1 from hm)]
  · rw [Set.indicator_of_notMem hm, if_neg (show ¬ rep x + β < 1 from hm)]

/-- `S β* 1 = 1_{β ≤ rep}` for `0 ≤ β ≤ 1`. -/
theorem coeFn_adjS_vac {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (ContinuousLinearMap.adjoint (S β) vac : T1 → ℝ) =ᵐ[volume]
      fun z => if β ≤ rep z then 1 else 0 := by
  have h2 := (quasi_shift (-β)).ae_eq_comp coeFn_vac
  filter_upwards [coeFn_adjoint_S β vac, h2] with x hx hx2
  rw [hx]
  have hneg : x + ((-β : ℝ) : T1) = x - (β : T1) := by rw [AddCircle.coe_neg, ← sub_eq_add_neg]
  simp only [Function.comp_apply] at hx2
  by_cases hm : β ≤ rep x
  · have hmem : x + ((-β : ℝ) : T1) ∈ maskFwd β := by
      rw [hneg]; exact (mem_maskFwd_sub_iff hβ0 hβ1 x).2 hm
    rw [Set.indicator_of_mem hmem, hx2, if_pos hm]
  · have hmem : x + ((-β : ℝ) : T1) ∉ maskFwd β := by
      rw [hneg]; exact fun h => hm ((mem_maskFwd_sub_iff hβ0 hβ1 x).1 h)
    rw [Set.indicator_of_notMem hmem, if_neg hm]

/-- `⟨S a 1, S b 1⟩ = 1 − max a b`. -/
theorem inner_S_vac_S_vac {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (_hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    inner ℝ (S a vac) (S b vac) = 1 - max a b := by
  rw [L2.inner_def, ← integral_indicator_maskFwd (le_max_of_le_left ha0) (max_le ha1 hb1)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_S_vac a, coeFn_S_vac b] with x hx1 hx2
  rw [hx1, hx2]
  have key : rep x + max a b < 1 ↔ (rep x + a < 1 ∧ rep x + b < 1) := by
    constructor
    · intro h; exact ⟨by linarith [le_max_left a b], by linarith [le_max_right a b]⟩
    · rintro ⟨h1, h2⟩
      rcases le_total a b with hab | hab
      · rw [max_eq_right hab]; exact h2
      · rw [max_eq_left hab]; exact h1
  have hmem : x ∈ maskFwd (max a b) ↔ (rep x + a < 1 ∧ rep x + b < 1) := key
  simp only [RCLike.inner_apply, conj_trivial]
  split_ifs <;> simp_all

/-- `⟨S a* 1, S b* 1⟩ = 1 − max a b`. -/
theorem inner_adjS_vac_adjS_vac {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    inner ℝ (ContinuousLinearMap.adjoint (S a) vac) (ContinuousLinearMap.adjoint (S b) vac)
      = 1 - max a b := by
  rw [L2.inner_def, ← integral_indicator_ge (le_max_of_le_left ha0) (max_le ha1 hb1)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_adjS_vac ha0 ha1, coeFn_adjS_vac hb0 hb1] with x hx1 hx2
  rw [hx1, hx2]
  simp only [RCLike.inner_apply, conj_trivial, max_le_iff]
  split_ifs <;> simp_all

end Cvs.WeilForm.VacuumTwoWalkCorrelation
