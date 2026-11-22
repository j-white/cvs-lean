import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.FourierShift

/-!
# The assembly, for any admissible test

`an earlier result` assembled `an earlier result`'s four channels into a lower bound on the zero side, for `gaussAmp`.
-/

namespace Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly

open Complex MeasureTheory ArithmeticFunction
open scoped Real

/-- The second pole integrand, over an arbitrary test. -/
noncomputable def poleTwo (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 / (z - 1) * Cvs.Zeta.ofCritical h z

/-- The prime channel, as `guinand_weil_classical` states it. -/
noncomputable def primeSide (h : ℂ → ℂ) : ℂ :=
  ∑' n : ℕ, (Λ n : ℂ) * (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
    * Cvs.Zeta.fourierReal h (Real.log n)

end Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
