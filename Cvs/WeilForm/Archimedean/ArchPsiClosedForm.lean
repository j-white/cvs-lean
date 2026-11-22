import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyImaginaryHalf
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged

/-!
# The archimedean `ψ`, in closed form

    ψ_arch(x) = (1/π)·[ sin(2πx)·archSymbol(2πx/L) + cos(2πx)·archSymbolIm(2πx/L) ]

The archimedean `𝒟` is a Lévy functional, not a function, so `CvS`'s `ψ` pairs it against
`sin(2πx(1−y/L))` directly — well defined because `h 0 − h(u/2)` is `O(u)`, the Lévy condition.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Cvs.Zeta

namespace Cvs.WeilForm.Archimedean.ArchPsiClosedForm

open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf Cvs.WeilForm.Archimedean.LevyImaginaryHalf

/-- **The archimedean `ψ`.** -/
def psiArch (L x : ℝ) : ℝ :=
  (1 / Real.pi) * (Real.sin (2 * Real.pi * x)
      * Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * Real.pi * x / L)
    + Real.cos (2 * Real.pi * x) * archSymbolIm (2 * Real.pi * x / L))

/-- **The Lévy integrand splits**, which is the whole of the derivation. -/
theorem levy_integrand_split {L : ℝ} (hL : L ≠ 0) (x u : ℝ) :
    Real.sin (2 * Real.pi * x) - Real.sin (2 * Real.pi * x * (1 - u / (2 * L)))
      = Real.sin (2 * Real.pi * x) * (1 - Real.cos ((2 * Real.pi * x / L) / 2 * u))
        + Real.cos (2 * Real.pi * x) * Real.sin ((2 * Real.pi * x / L) / 2 * u) := by
  have harg : 2 * Real.pi * x * (1 - u / (2 * L))
      = 2 * Real.pi * x - (2 * Real.pi * x / L) / 2 * u := by
    field_simp
  rw [harg, Real.sin_sub]
  ring

/-- **It is the Lévy pairing**, term by term. -/
theorem psiArch_eq_levy (L x : ℝ) :
    psiArch L x
      = (1 / Real.pi) * (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * Real.sin (2 * Real.pi * x)
        + (Real.sin (2 * Real.pi * x)
            * (∫ u in Ioi (0:ℝ), (1 - Real.cos ((2 * Real.pi * x / L) / 2 * u))
                * Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
          + Real.cos (2 * Real.pi * x)
            * (∫ u in Ioi (0:ℝ), Real.sin ((2 * Real.pi * x / L) / 2 * u)
                * Cvs.WeilForm.Archimedean.LevyDensity.densityU u))) := by
  rw [Cvs.Zeta.DigammaLimitDischarged.integral_rep, integral_rep_im, psiArch, archSymbolIm,
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol]
  ring

end Cvs.WeilForm.Archimedean.ArchPsiClosedForm
