import Mathlib
import Cvs.Finite.SymmetricModeSet

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The modes are bounded by the truncation

A mode is zero at the constant index and plus or minus a position below the truncation at a pair,
so its size never exceeds the truncation and the poles never exceed the truncation's frequency
squared, which is the bound the decay estimate asks for.
-/

noncomputable section

open Real

namespace Cvs.Finite.ModeTruncationBound

open Cvs.Finite.SymmetricModeSet

/-- **A mode's size never exceeds the truncation.** -/
theorem abs_mode_le (N : ℕ) (i : Idx N) : |mode N i| ≤ (N : ℤ) := by
  cases i with
  | none => simp [mode]
  | some p =>
    obtain ⟨k, b⟩ := p
    have hk : ((k : ℕ) : ℤ) + 1 ≤ (N : ℤ) := by exact_mod_cast k.is_lt
    have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) + 1 := by positivity
    cases b <;> simp only [mode, if_true] <;> rw [abs_le] <;> constructor <;> omega

end Cvs.Finite.ModeTruncationBound
