import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.TruncationBelowSymbol
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaEulerLimitInstance
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrandDiff

/-!
# The archimedean form is integrable

`DigammaEulerLimitInstance` bounds the symbol above by a quadratic and `Cvs.WeilForm.Archimedean.TruncationBelowSymbol` bounds it below by its value at zero, so
against a Schwartz-decaying density the pairing converges and `an earlier result`'s side condition discharges.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace Cvs.WeilForm.Archimedean.ArchFormIntegrable

/-- The quadratic majorant's coefficient, from `DigammaEulerLimitInstance`. -/
def growth : ℝ := ∑' k : ℕ, 1 / (4 * (1 / 4 + (k : ℝ)) ^ 3)

theorem growth_nonneg : 0 ≤ growth :=
  tsum_nonneg fun k => by positivity

/-- **The symbol is squeezed between its value at zero and a quadratic.** -/
theorem archSymbol_bounds (t : ℝ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t ∧
      Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
        ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + growth * t ^ 2 := by
  have hlo := Cvs.WeilForm.Archimedean.TruncationBelowSymbol.remainder_nonneg t 0
  have hhi := Cvs.Transform.re_digamma_sub_le t
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  constructor
  · linarith
  · rw [show growth * t ^ 2 = t ^ 2 * growth from mul_comm _ _]
    unfold growth
    linarith

/-- **The symbol grows at most quadratically.** -/
theorem abs_archSymbol_le (t : ℝ) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t|
      ≤ |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + growth * t ^ 2 := by
  obtain ⟨hlo, hhi⟩ := archSymbol_bounds t
  have h0 := le_abs_self (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
  have h0' := neg_abs_le (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
  have hg : 0 ≤ growth * t ^ 2 := by
    have := growth_nonneg; positivity
  rw [abs_le]
  constructor <;> linarith

/-- **The symbol is continuous**, since `digamma` is differentiable on the right half-plane. -/
theorem continuous_archSymbol : Continuous Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol := by
  have harg : Continuous fun t : ℝ => Cvs.Zeta.digammaArg t 0 := by
    unfold Cvs.Zeta.digammaArg
    fun_prop
  have hdig : Continuous fun t : ℝ => Complex.digamma (Cvs.Zeta.digammaArg t 0) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.comp
      (Cvs.Detection.differentiableAt_digamma (Cvs.Zeta.digammaArg_re_pos t)).continuousAt
      harg.continuousAt
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  exact (Complex.continuous_re.comp hdig).sub continuous_const

end Cvs.WeilForm.Archimedean.ArchFormIntegrable
