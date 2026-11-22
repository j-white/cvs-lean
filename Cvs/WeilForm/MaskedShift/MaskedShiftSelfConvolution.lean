import Mathlib
import Cvs.WeilForm.MaskedShift.MaskedLiftToLine
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped InnerProductSpace NNReal

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.Operator Cvs.PrimeOperator Cvs.PrimeOperator

/-!
# The transfer

`⟪S β f, f⟫` is the self-convolution of the lift, evaluated at `β`.
-/

/-- The integrands agree pointwise on the fundamental domain: the forward mask
and the support of the shifted lift are the same condition. -/
theorem integrand_coe (f : L2) {β : ℝ} (hβ : 0 ≤ β) {y : ℝ} (hy : y ∈ Set.Ico (0:ℝ) 1) :
    (maskFwd β).indicator ((f : T1 → ℝ) ∘ (fun z => z + (β : T1))) (y : T1)
        * (f : T1 → ℝ) (y : T1)
      = lift f y * lift f (y + β) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hcast : ((y : T1) + (β : T1)) = ((y + β : ℝ) : T1) := (AddCircle.coe_add _ _ _).symm
  rw [lift_of_mem f hy0 hy1]
  by_cases hm : (y : T1) ∈ maskFwd β
  · have hlt : y + β < 1 := (mem_maskFwd_coe hy0 hy1).mp hm
    rw [Set.indicator_of_mem hm]
    simp only [Function.comp_apply, hcast]
    rw [lift_of_mem f (by linarith) hlt]
    ring
  · have hge : ¬ (y + β < 1) := fun h => hm ((mem_maskFwd_coe hy0 hy1).mpr h)
    rw [Set.indicator_of_notMem hm,
      lift_of_notMem f (fun hc => hge (Set.mem_Ico.mp hc).2)]
    ring

/-- **N1.  The transfer.**  The operator's forward quadratic form is the
self-convolution of the lift. -/
theorem inner_S_eq_selfConvolution (f : L2) {β : ℝ} (hβ : 0 ≤ β) :
    ⟪S β f, f⟫_ℝ = selfConvolution (lift f) β := by
  classical
  set F : T1 → ℝ := fun x =>
    (maskFwd β).indicator ((f : T1 → ℝ) ∘ (fun z => z + (β : T1))) x * (f : T1 → ℝ) x with hF
  have h1 : ⟪S β f, f⟫_ℝ = ∫ x : T1, F x := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_S β f] with x hx
    simp [hF, hx, RCLike.inner_apply, mul_comm]
  have h2 : ∫ x : T1, F x = ∫ y in Set.Ioc (0:ℝ) 1, F (y : T1) := by
    have h := AddCircle.integral_preimage (1:ℝ) 0 F
    rw [zero_add] at h
    exact h.symm
  have h3 : ∫ y in Set.Ioc (0:ℝ) 1, F (y : T1) = ∫ y in Set.Ico (0:ℝ) 1, F (y : T1) := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [show (∫ y in Set.Ico (0:ℝ) 1, F (y : T1)) = ∫ y in Set.Ioo (0:ℝ) 1, F (y : T1) from
      integral_Ico_eq_integral_Ioo]
  have h4 : ∫ y in Set.Ico (0:ℝ) 1, F (y : T1)
      = ∫ y in Set.Ico (0:ℝ) 1, lift f y * lift f (y + β) :=
    setIntegral_congr_fun measurableSet_Ico (fun y hy => integrand_coe f hβ hy)
  have h5 : ∫ y in Set.Ico (0:ℝ) 1, lift f y * lift f (y + β)
      = ∫ y : ℝ, lift f y * lift f (y + β) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [lift_of_notMem f hy, zero_mul])
  rw [h1, h2, h3, h4, h5]
  rfl

end Cvs.PrimeOperator
