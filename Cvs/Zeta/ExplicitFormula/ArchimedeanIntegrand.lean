import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.ExplicitFormula.ArchimedeanBoundTestFree
import Cvs.Zeta.GammaRLogDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The filter bank's weight is the explicit formula's archimedean integrand
-/

namespace Cvs.Detection

open Complex

/-- The archimedean score: the log-derivative of `Γ_ℝ` on the critical line. -/
noncomputable def archScore (u : ℝ) : ℝ := (logDeriv Gammaℝ (1 / 2 + I * u)).re

theorem half_add_I_div_two (u : ℝ) :
    ((1 : ℂ) / 2 + I * u) / 2 = Cvs.Zeta.digammaArg u 0 := by
  rw [Cvs.Zeta.digammaArg]
  push_cast
  ring

theorem half_add_I_ne_neg_nat (u : ℝ) (m : ℕ) : ((1 : ℂ) / 2 + I * u) / 2 ≠ -m := by
  rw [half_add_I_div_two]
  exact Cvs.Zeta.ne_neg_nat_of_re_pos (Cvs.Zeta.digammaArg_re_pos u) m

/-- **The score in terms of the digamma point the bank is built at.** -/
theorem archScore_eq (u : ℝ) :
    archScore u
      = -(Real.log Real.pi) / 2
        + (Complex.digamma (Cvs.Zeta.digammaArg u 0)).re / 2 := by
  rw [archScore, Cvs.Zeta.logDeriv_gammaR (half_add_I_ne_neg_nat u), half_add_I_div_two]
  simp [Complex.log_ofReal_re]

/-- **The bridge.**  `W` is the archimedean integrand, relative to its value at
the centre of the critical line. -/
theorem W_eq_archScore_sub (u : ℝ) : Cvs.Detection.W u = archScore u - archScore 0 := by
  rw [archScore_eq, archScore_eq, Cvs.Detection.W]
  ring

end Cvs.Detection
