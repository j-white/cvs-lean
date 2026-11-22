import Mathlib
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The form and the transform's zeros do not see a sign

    weilForm P R (−f) = weilForm P R f,  −f in the window if `f` is,
    and `−f`'s transform has the same zeros

so a minimiser is determined at best up to sign, and either sign serves the terminal.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.FormSignInvariant

variable {L : ℝ}

/-- **The transform flips sign, so its zeros are unchanged.** -/
theorem fourierLaplace_neg (f : ℝ → ℝ) (z : ℂ) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (fun x => -f x)) z
      = -FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z := by
  rw [FourierLaplace.fourierLaplace, FourierLaplace.fourierLaplace, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ((-f t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))
    = -(((f t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ)))
  push_cast
  ring

end Cvs.WeilForm.FormSignInvariant
