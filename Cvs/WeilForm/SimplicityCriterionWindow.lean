import Mathlib
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# The simplicity criterion, instantiated at the window's form

    no plane of `window L` sits at or below `β` for `weilQW`, and an odd vector cannot
    sit there either

the two hypotheses left being `μ₂` for the truncation and `μ_odd` for the odd sector.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SimplicityCriterionWindow

variable {L : ℝ}

/-- **The truncated form on the window's subspace.** -/
def weilQWTrunc (N P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  Cvs.WeilForm.TruncatedFormL2Below.weilQTrunc N P R (φ : Lp ℝ 2 (volume : Measure ℝ))

end Cvs.WeilForm.SimplicityCriterionWindow
