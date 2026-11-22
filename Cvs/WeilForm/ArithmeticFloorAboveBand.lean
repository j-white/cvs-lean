import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# An actual arithmetic floor above a finite frequency band

The growing archimedean symbol dominates the fixed finite prime budgets on every
even vector supported above a frequency threshold, uniformly in mode order.
-/

noncomputable section

open Real Matrix Finset

namespace Cvs.WeilForm.ArithmeticFloorAboveBand


/-- The explicit digamma lower envelope at frequency `T`. -/
def archLower (T : ℝ) : ℝ := log (T / 2) - 57 / T - log π

/-- The explicit envelope bounds the arch symbol at every frequency beyond its threshold. -/
theorem archLower_le_archSymbol {T ω : ℝ} (hT : 2 ≤ T) (hω : T ≤ |ω|) :
    archLower T ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol ω := by
  have hs : T ^ 2 ≤ ω ^ 2 := by
    nlinarith [sq_abs ω, abs_nonneg ω]
  exact (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge hT).trans (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono hs)

/-- The finite positive-mode order containing all frequencies below `T`. -/
def cutoffOrder (L T : ℝ) : ℕ := ⌈T * L / (2 * π)⌉₊

/-- Every integer mode at or beyond the cutoff order lies above the frequency threshold. -/
theorem cutoffOrder_frequency {L : ℝ} (hL : 0 < L) (T : ℝ) (m : ℤ)
    (hm : cutoffOrder L T ≤ m.natAbs) : T ≤ |2 * π * (m : ℝ) / L| := by
  have hc : T * L / (2 * π) ≤ (m.natAbs : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have ha : (m.natAbs : ℝ) = |(m : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [ha] at hc
  have hpi : 0 < 2 * π := by positivity
  have hn := (div_le_iff₀ hpi).mp hc
  rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hL]
  exact (le_div_iff₀ hL).mpr (by nlinarith [hn])

end Cvs.WeilForm.ArithmeticFloorAboveBand
