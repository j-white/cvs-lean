import Mathlib
import Cvs.Zeta.CriticalParam

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# On the critical line the test becomes a real, nonnegative density
-/

namespace Cvs.Detection

open Complex

/-- **`ofCritical` collapses onto the real axis** at `Re s = ½`. -/
theorem ofCritical_half (h : ℂ → ℂ) (y : ℝ) :
    Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = h (y : ℂ) := by
  rw [Cvs.Zeta.ofCritical]
  congr 1
  have : ((1 : ℂ) / 2 + (y : ℂ) * I) - 1 / 2 = (y : ℂ) * I := by ring
  rw [this]
  rw [show -I * ((y : ℂ) * I) = -(I * I) * (y : ℂ) from by ring, Complex.I_mul_I]
  ring

end Cvs.Detection
