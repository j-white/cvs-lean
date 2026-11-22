import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound
import Cvs.Zeta.RiemannSiegelPhase

/-!
# The archimedean symbol is twice the detection score

    archSymbol t = 2 · Detection.archScore t = 2 · Re (logDeriv Γ_ℝ (½ + it))

`Cvs.WeilForm.Archimedean.ArchimedeanCoercive` normalises the symbol against `Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound`'s score, `RiemannSiegelPhase` identifies that score with
`Detection`'s, and `Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound` writes it as a logarithmic derivative on the critical line.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.WeilForm.Archimedean.SymbolTwiceScore

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-- **The symbol is twice the detection score.** -/
theorem archSymbol_eq_two_mul_archScore (t : ℝ) :
    archSymbol t = 2 * Cvs.Detection.archScore t := by
  rw [Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_eq_two_mul, ← Cvs.ArchScore.archScore_eq]

/-- **And twice the logarithmic derivative of `Γ_ℝ` on the critical line.** -/
theorem archSymbol_eq_two_mul_logDeriv (t : ℝ) :
    archSymbol t
      = 2 * (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
  rw [Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_eq_two_mul,
    Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore_eq_logDeriv]

end Cvs.WeilForm.Archimedean.SymbolTwiceScore
