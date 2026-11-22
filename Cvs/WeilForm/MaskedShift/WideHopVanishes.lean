import Mathlib
import Cvs.WeilForm.MaskedShift.AtomNormLaw
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftNilpotent
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.MaskedShift.PrimePowerRotationNumber
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped InnerProductSpace NNReal

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.Operator Cvs.Operator Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator

/-!
# A hop wider than the box does nothing

Physically the mask is a hard wall: `S β` moves a state right by `β` and deletes whatever
leaves the interval.
-/

variable {β : ℝ}

-- `maskFwd_eq_empty` and `S_eq_zero` are `Cvs.Operator`'s; not restated here.

/-- A single-site chain cannot hop. -/
theorem chebFactor_one : Cvs.Operator.chebFactor 1 = 0 := by
  unfold Cvs.Operator.chebFactor
  norm_num

/-- At or above the scale the chain has one site. -/
theorem cap_eq_one {c q : ℕ} (hc : 1 < c) (hq : c ≤ q) :
    cap (Real.log c) (Real.log q) = 1 := by
  have hlc : 0 < Real.log c := log_pos_of_one_lt hc
  have hlq : Real.log c ≤ Real.log q :=
    Real.log_le_log (by positivity) (by exact_mod_cast hq)
  have hlq0 : 0 < Real.log q := lt_of_lt_of_le hlc hlq
  unfold cap
  refine le_antisymm (Nat.ceil_le.mpr ?_) (Nat.ceil_pos.mpr (div_pos hlc hlq0))
  rw [Nat.cast_one, div_le_one hlq0]
  exact hlq

/-- **The atom vanishes at or above the scale.** -/
theorem atom_eq_zero {c q : ℕ} (hc : 1 < c) (hq : c ≤ q) : atom c q = 0 := by
  have hlc : 0 < Real.log c := log_pos_of_one_lt hc
  have hlq : Real.log c ≤ Real.log q :=
    Real.log_le_log (by positivity) (by exact_mod_cast hq)
  have hrot : (1 : ℝ) ≤ ((rot c q : ℝ≥0) : ℝ) := by
    unfold rot
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [le_div_iff₀ hlc]
    linarith
  rw [atom_eq, show Cvs.Operator.W Snn (rot c q) = Snn (rot c q)
      + ContinuousLinearMap.adjoint (Snn (rot c q)) from rfl,
    show Snn (rot c q) = S ((rot c q : ℝ≥0) : ℝ) from rfl, S_eq_zero hrot]
  simp

/-- **The norm law, with no hypothesis on the scale.**  Above the scale both
sides are zero: the atom vanishes, and the one-site chain has `ν(1) = 0`. -/
theorem norm_atom_of_one_lt {c q : ℕ} (hc : 1 < c) (h1 : 1 < q) :
    ‖atom c q‖ = Cvs.Operator.chebFactor (cap (Real.log c) (Real.log q)) * wt q := by
  rcases lt_or_ge q c with h | h
  · exact Cvs.Operator.norm_atom h1 h
  · rw [atom_eq_zero hc h, norm_zero, cap_eq_one hc h, chebFactor_one, zero_mul]

/-- **The explicit bound, unconditionally.**  B56's version required every prime
power below the scale; those terms are zero, so the requirement was vacuous. -/
theorem norm_primeOperator_le_atomBudget {c : ℕ} (hc : 1 < c) (P R : ℕ) :
    ‖primeOperator c P R‖ ≤ atomBudget c P R := by
  refine norm_sum_le_of_le _ fun p hp => ?_
  refine norm_sum_le_of_le _ fun r hr => ?_
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have h1 : 1 < p ^ r := Nat.one_lt_pow (by omega) hprime.one_lt
  exact le_of_eq (norm_atom_of_one_lt hc h1)

end Cvs.PrimeOperator
