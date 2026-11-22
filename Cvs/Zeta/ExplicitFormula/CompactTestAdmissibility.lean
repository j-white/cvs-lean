import Mathlib
import Cvs.Zeta.ContourShift
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# An admissibility criterion for compactly supported tests

`DecayHypothesisShape` and `WindowTransformEntire` discharged three of `Cvs.Zeta.guinand_weil_classical`'s four hypotheses for
any compactly supported continuous test.
-/

namespace Cvs.Detection

open Complex MeasureTheory ArithmeticFunction
open scoped Real

/-- The squared window transform — the Weil test built from a compactly supported `f`. -/
noncomputable def sqTransform (L : ℝ) (f : ℝ → ℂ) (ξ : ℂ) : ℂ :=
  Cvs.Detection.windowTransform L f ξ * Cvs.Detection.windowTransform L f (-ξ)

/-- **Cubic decay on the strip implies `StripDecayRe`.**  The half-strip sits
inside the strip, and `1 + |Re w| ≥ 1` turns the cubic bound into a quadratic
one. -/
theorem stripDecayRe_of_decay {A : ℝ} (hA : 0 ≤ A) {W : ℂ → ℂ}
    (h : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖W ξ * W (-ξ)‖ ≤ A / (1 + |ξ.re|) ^ 3) :
    Cvs.Zeta.StripDecayRe (fun ξ => W ξ * W (-ξ)) A (3 / 2) := by
  intro w h1 h2
  have hstrip : |w.im| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith
  refine (h w hstrip).trans ?_
  have habs : (0 : ℝ) ≤ |w.re| := abs_nonneg _
  have hsq : (0 : ℝ) < (1 + |w.re|) ^ 2 := by positivity
  have hcu : (0 : ℝ) < (1 + |w.re|) ^ 3 := by positivity
  rw [div_le_div_iff₀ hcu hsq]
  have hle : (1 + |w.re|) ^ 2 ≤ (1 + |w.re|) ^ 3 := by nlinarith [habs]
  nlinarith [hA, hle, hsq]

end Cvs.Detection
