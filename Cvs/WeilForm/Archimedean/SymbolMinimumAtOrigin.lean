import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged
import Cvs.Zeta.WeilPositivityStatement

/-!
# The symbol is least at the origin, so the spectral form charges its tail

    archSymbol 0 ≤ archSymbol t,   and   ∫ W·archSymbol ≥ archSymbol 0·∫W + (c − archSymbol 0)·∫_{|t|≥T} W

whenever `archSymbol ≥ c` past `T`.  Mass at high frequency is charged `c`; everything else
is charged the symbol's floor.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-- **The symbol is least at the origin.**  `Cvs.Zeta.DigammaLimitDischarged`'s Lévy representation has a nonnegative
integrand, so its integral — the symbol's increment — never turns negative. -/
theorem archSymbol_min_at_zero (t : ℝ) : archSymbol 0 ≤ archSymbol t := by
  have h := Cvs.Zeta.DigammaLimitDischarged.sub_nonneg t
  unfold archSymbol
  linarith

/-- The frequencies past a threshold. -/
def tailSet (T : ℝ) : Set ℝ := {t : ℝ | T ≤ |t|}

theorem measurableSet_tailSet (T : ℝ) : MeasurableSet (tailSet T) :=
  measurableSet_le measurable_const (measurable_id.abs)

/-- **The spectral form charges its tail.**  Whatever floor the symbol has past `T`, the
form pays it on the mass sitting there, and the symbol's own floor everywhere. -/
theorem arch_ge_tail {W : ℝ → ℝ} (hW : ∀ t, 0 ≤ W t) (hWi : Integrable W)
    (hWA : Integrable fun t : ℝ => W t * archSymbol t)
    {T c : ℝ} (hc : ∀ t : ℝ, t ∈ tailSet T → c ≤ archSymbol t) :
    archSymbol 0 * (∫ t : ℝ, W t)
        + (c - archSymbol 0) * (∫ t in tailSet T, W t)
      ≤ ∫ t : ℝ, W t * archSymbol t := by
  have hSm := measurableSet_tailSet T
  have hind : Integrable ((tailSet T).indicator W) := hWi.indicator hSm
  have hle : ∀ t : ℝ, W t * archSymbol 0 + (c - archSymbol 0) * (tailSet T).indicator W t
      ≤ W t * archSymbol t := by
    intro t
    by_cases ht : t ∈ tailSet T
    · rw [Set.indicator_of_mem ht]
      nlinarith [hW t, hc t ht]
    · rw [Set.indicator_of_notMem ht, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (archSymbol_min_at_zero t) (hW t)
  have hint := integral_mono ((hWi.mul_const _).add (hind.const_mul _)) hWA hle
  simp only [Pi.add_apply] at hint
  rw [integral_add (hWi.mul_const _) (hind.const_mul _), integral_mul_const,
    integral_const_mul, integral_indicator hSm] at hint
  linarith [hint]

/-- **The density's total mass is the norm.**  `Cvs.WeilForm.SelfConvolutionCosine` at the origin. -/
theorem integral_specDensity {f : ℝ → ℝ} (hfint : Integrable f)
    (hgint : Integrable fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
    (hcont : ContinuousAt (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) 0)
    (hFsq : Integrable fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) :
    (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) = selfConvolution f 0 := by
  have h := Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hFsq hcont
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp

end Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
