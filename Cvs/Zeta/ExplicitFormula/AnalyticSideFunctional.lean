import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.FourierShift

/-!
# The explicit formula's analytic side, as one functional of the kernel

    analyticSide h = two pole integrals + the archimedean integral − the prime sum

spelled as `CompactTestAdmissibility` spells it, so restating `guinand_weil_of_windowTransform` against it is
the identity on its conclusion.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex MeasureTheory
open scoped Real ArithmeticFunction

namespace Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional

/-- **The analytic side of the explicit formula**, at an arbitrary kernel. -/
def analyticSide (h : ℂ → ℂ) : ℂ :=
  (∫ y : ℝ, 1 / ((2 : ℂ) + y * I) * Cvs.Zeta.ofCritical h ((2 : ℂ) + y * I))
    + (∫ y : ℝ, 1 / (((2 : ℂ) + y * I) - 1)
        * Cvs.Zeta.ofCritical h ((2 : ℂ) + y * I))
    + (∫ y : ℝ, logDeriv Gammaℝ ((2 : ℂ) + y * I)
        * Cvs.Zeta.ofCritical h ((2 : ℂ) + y * I))
    - ∑' n : ℕ, (Λ n : ℂ) * (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
        * Cvs.Zeta.fourierReal h (Real.log n)

end Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional
