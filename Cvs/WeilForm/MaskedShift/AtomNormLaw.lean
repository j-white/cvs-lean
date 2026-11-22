import Mathlib
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedRotationUpperBound
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped NNReal

namespace Cvs.Operator

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.Operator

/-!
# The norm law at the arithmetic parameters

`‖A_q‖ = ν(m_q) · Λ(q)/√q` with `m_q = ⌈log c / log q⌉`, for `1 < q < c`.
-/

variable {c q : ℕ}

theorem log_pos_of_one_lt (h : 1 < q) : 0 < Real.log q :=
  Real.log_pos (by exact_mod_cast h)

/-- The rotation number lies strictly between `0` and `1`. -/
theorem rot_mem (h1 : 1 < q) (h2 : q < c) :
    0 < ((rot c q : ℝ≥0) : ℝ) ∧ ((rot c q : ℝ≥0) : ℝ) < 1 := by
  have hq : 0 < Real.log q := log_pos_of_one_lt h1
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hqc : Real.log q < Real.log c :=
    Real.log_lt_log hq0 (by exact_mod_cast h2)
  have hc : 0 < Real.log c := lt_trans hq hqc
  have hpos : 0 < Real.log q / Real.log c := div_pos hq hc
  have hval : Real.log q / Real.log c < 1 := (div_lt_one hc).mpr hqc
  rw [rot, Real.coe_toNNReal _ hpos.le]
  exact ⟨hpos, hval⟩

/-- The coercion, at these parameters. -/
theorem coe_rot_eq (h1 : 1 < q) (h2 : q < c) :
    ((rot c q : ℝ≥0) : ℝ) = Real.log q / Real.log c := by
  have hq : 0 < Real.log q := log_pos_of_one_lt h1
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hqc : Real.log q < Real.log c :=
    Real.log_lt_log hq0 (by exact_mod_cast h2)
  have hc : 0 < Real.log c := lt_trans hq hqc
  rw [rot, Real.coe_toNNReal _ (div_pos hq hc).le]

/-- **The norm law at the arithmetic parameters.**  `‖A_q‖ = ν(m_q) · Λ(q)/√q`
with `m_q = ⌈log c / log q⌉`. -/
theorem norm_atom (h1 : 1 < q) (h2 : q < c) :
    ‖atom c q‖
      = Cvs.Operator.chebFactor (cap (Real.log c) (Real.log q)) * wt q := by
  obtain ⟨hpos, hlt⟩ := rot_mem h1 h2
  rw [atom_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg q),
    show ‖Cvs.Operator.W Snn (rot c q)‖
      = Cvs.Operator.chebFactor (cap 1 ((rot c q : ℝ≥0) : ℝ)) from Cvs.Operator.norm_W hpos hlt,
    coe_rot_eq h1 h2, cap_one_div, mul_comm]

end Cvs.Operator
