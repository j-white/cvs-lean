import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaCriticalAsymptotic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean symbol on the tail

`|a(t) − log(t/2π)| ≤ 57/t` for `t ≥ 2`, with `a = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol`; at frequency `z` and scale `c > 0`,
`log(z/2π) = log(c/π) + log(z/2c)`.
-/

noncomputable section

namespace Cvs.WeilForm.Archimedean.ArchSymbolOnTail

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

/-- **The archimedean symbol is `log(t/2π) + O(1/t)`.** -/
theorem abs_archSymbol_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |archSymbol t - Real.log (t / (2 * Real.pi))| ≤ 57 / t := by
  have h := DigammaAsym.abs_re_digamma_sub_log_le t ht
  have e : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [← Real.log_div (by positivity) Real.pi_pos.ne', div_div]
  unfold archSymbol
  rw [e, show (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re - Real.log Real.pi - (Real.log (t / 2)
    - Real.log Real.pi) = (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re - Real.log (t / 2) by ring]
  exact h

/-- `log(z/2π) = log(c/π) + log(z/2c)`. -/
theorem log_split {c z : ℝ} (hc : 0 < c) (hz : 0 < z) :
    Real.log (z / (2 * Real.pi)) = Real.log (c / Real.pi) + Real.log (z / (2 * c)) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **At scale `c`**: `|a(z) − log(c/π) − log(z/2c)| ≤ 57/z` for `z ≥ 2`, `c > 0`. -/
theorem abs_archSymbol_sub_le {c z : ℝ} (hc : 0 < c) (hz : 2 ≤ z) :
    |archSymbol z - Real.log (c / Real.pi) - Real.log (z / (2 * c))| ≤ 57 / z := by
  have := abs_archSymbol_sub_log_le hz
  rw [log_split hc (by linarith)] at this
  rwa [sub_sub]

end Cvs.WeilForm.Archimedean.ArchSymbolOnTail
