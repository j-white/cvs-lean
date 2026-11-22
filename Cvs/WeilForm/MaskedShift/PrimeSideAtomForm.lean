import Mathlib
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedLiftToLine
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftSelfConvolution
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimePowerAtomWeight
import Cvs.WeilForm.MaskedShift.PrimePowerRotationNumber
import Cvs.Zeta.PrimePowerSideTruncated
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

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator

/-!
# The prime side is the atom form

The terminal node.
-/

/-- The two-sided form doubles the forward one: `W = S + S*` and the real inner
product is symmetric. -/
theorem inner_W_eq (f : L2) (β : ℝ≥0) :
    ⟪Cvs.Operator.W Snn β f, f⟫_ℝ = 2 * selfConvolution (lift f) (β : ℝ) := by
  have hadj : ⟪ContinuousLinearMap.adjoint (Snn β) f, f⟫_ℝ = ⟪Snn β f, f⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  rw [show Cvs.Operator.W Snn β = Snn β + ContinuousLinearMap.adjoint (Snn β) from rfl,
    add_apply, inner_add_left, hadj,
    show Snn β = S (β : ℝ) from rfl, inner_S_eq_selfConvolution f β.coe_nonneg]
  ring

/-- **The atom's quadratic form.** -/
theorem inner_atom_eq (c q : ℕ) (f : L2) :
    ⟪atom c q f, f⟫_ℝ = wt q * (2 * selfConvolution (lift f) ((rot c q : ℝ≥0) : ℝ)) := by
  rw [atom_eq, smul_apply, real_inner_smul_left, inner_W_eq]

/-- The test function: the self-convolution of the lift, read in the scale
`log c`.  A displacement of `u` in the explicit formula is a rotation of
`u / log c` on the circle. -/
noncomputable def testFn (c : ℕ) (f : L2) : ℝ → ℝ :=
  fun u => selfConvolution (lift f) (u / Real.log c)

/-- One term of the prime side is one atom's quadratic form. -/
theorem term_eq {c : ℕ} (hc : 1 < c) (f : L2) {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    primePowerWeight p r * (testFn c f (r * Real.log p) + testFn c f (-(r * Real.log p)))
      = ⟪atom c (p ^ r) f, f⟫_ℝ := by
  have hrot : ((rot c (p ^ r) : ℝ≥0) : ℝ) = r * Real.log p / Real.log c :=
    coe_rot_prime_pow hc
  have heven : testFn c f (-(r * Real.log p)) = testFn c f (r * Real.log p) := by
    unfold testFn
    rw [show (-(r * Real.log p) / Real.log c) = -((r * Real.log p) / Real.log c) by ring]
    exact selfConvolution_neg _ _
  rw [inner_atom_eq, hrot, heven, ← Cvs.PrimeOperator.wt_prime_pow hp hr]
  unfold testFn
  ring

/-- **The terminal node.**  The explicit formula's truncated prime side, paired
against the self-convolution of the lift, is the sum of the atoms' quadratic
forms over the same index set. -/
theorem primePowerSide_eq_atomForm {c : ℕ} (hc : 1 < c) (f : L2) (P R : ℕ) :
    primePowerSideTruncated P R (testFn c f)
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
          ∑ r ∈ Finset.Icc 1 R, ⟪atom c (p ^ r) f, f⟫_ℝ := by
  unfold primePowerSideTruncated
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun r hr => ?_
  exact term_eq hc f (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp hr).1

end Cvs.PrimeOperator
