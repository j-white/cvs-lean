import Mathlib
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real ArithmeticFunction
open scoped NNReal

namespace Cvs.PrimeOperator

open Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

/-!
# The rotation number at a prime power

`rot c q` is `log q / log c` truncated at zero.
-/

/-- The scale is positive whenever `1 < c`. -/
theorem log_pos_of_one_lt {c : ℕ} (hc : 1 < c) : 0 < Real.log c :=
  Real.log_pos (by exact_mod_cast hc)

/-- **N3a.**  `rot c (pʳ) = r · log p / log c`, with no truncation. -/
theorem coe_rot_prime_pow {c p r : ℕ} (hc : 1 < c) :
    ((rot c (p ^ r) : ℝ≥0) : ℝ) = r * Real.log p / Real.log c := by
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hlc : 0 < Real.log c := log_pos_of_one_lt hc
  have hsplit : Real.log ((p ^ r : ℕ) : ℝ) = r * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  unfold rot
  rw [Real.coe_toNNReal _ (by rw [hsplit]; positivity), hsplit]

end Cvs.PrimeOperator
