import Mathlib
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaRealSegment

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The real segment, closed
-/

namespace Cvs.GaussKernel

/-- A zero with zero ordinate is a real number in the strip, where `ζ` does not vanish. -/
theorem noRealOffLineZero : Cvs.Zeta.GaussKernel.AdmissibleKernel.NoRealOffLineZero := by
  intro ρ _ him
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hreal : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hreal] at hz
  exact Cvs.Zeta.riemannZeta_ne_zero_of_mem_Ioo h0 h1 hz

end Cvs.GaussKernel
