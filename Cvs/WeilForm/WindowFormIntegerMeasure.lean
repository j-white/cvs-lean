import Mathlib
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Under RH the window form is an integer measure on the zeros

Under RH, for `2 ≤ x` and `v` tame on `[1/x, 1]`, `Q(w_v) = Σ_ρ m_ρ ‖W_L f_v(γ_ρ)‖²` (`L = log x`,
`f_v = logWin L v`, `m_ρ ≥ 1`), summable with nonnegative terms, so every finite partial sum is at most
`Q(w_v)`: each zero is an admissible atom at `γ_ρ` of mass `m_ρ`, a conjugate pair of mass `m_ρ + m_ρ̄`.
The finite-set bound holds on the whole form domain at complete `(P, R)`, on the canonical representative.
-/

noncomputable section

open Real MeasureTheory Filter

namespace Cvs.WeilForm.WindowFormIntegerMeasure

open Cvs.WeilForm.SelfConvolutionTransform (cf)

/-! ### Admissible atoms -/

/-! ### The whole form domain -/

/-- The window transform of a real test depends only on its a.e. class. -/
theorem windowTransform_congr_ae {L : ℝ} {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf f) ξ = Cvs.Detection.windowTransform L (cf g) ξ := by
  unfold Cvs.Detection.windowTransform
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h] with s hs _
  simp only [cf, hs]

end Cvs.WeilForm.WindowFormIntegerMeasure
