import Mathlib
import Cvs.WeilForm.GaussianRegulariser

/-!
# The regulariser's transform, and its integrability

    𝓕 (gauss c) = gaussHat c

identifying `Cvs.WeilForm.GaussianRegulariser`'s kernel as the transform of its multiplier, in the normalisation
Mathlib's `fourier_gaussian_pi` uses.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Cvs.WeilForm.RegulariserTransform

/-- The multiplier, complexified. -/
def gaussC (c : ℝ) : ℝ → ℂ := fun x => ((Cvs.WeilForm.GaussianRegulariser.gauss c x : ℝ) : ℂ)

/-- **The kernel is the multiplier's transform.** -/
theorem fourier_gaussC {c : ℝ} (hc : 0 < c) (t : ℝ) :
    𝓕 (gaussC c) t = ((Cvs.WeilForm.GaussianRegulariser.gaussHat c t : ℝ) : ℂ) := by
  have hb : (0:ℝ) < ((c : ℂ)).re := by simpa using hc
  have hlhs : gaussC c = fun x : ℝ => Complex.exp (-π * (c:ℂ) * (x:ℂ) ^ 2) := by
    funext x
    rw [gaussC, Cvs.WeilForm.GaussianRegulariser.gauss, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hlhs, fourier_gaussian_pi hb]
  simp only
  have hsq : ((c : ℂ)) ^ (1/2 : ℂ) = ((Real.sqrt c : ℝ) : ℂ) := by
    rw [show ((1:ℂ)/2) = (((1/2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_cpow hc.le,
      ← Real.sqrt_eq_rpow]
  rw [hsq, show (-(π:ℂ) / (c:ℂ) * (t:ℂ) ^ 2) = (((-π * t ^ 2 / c : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  rw [Cvs.WeilForm.GaussianRegulariser.gaussHat]
  push_cast
  ring

/-- **The multiplier is integrable.** -/
theorem integrable_gaussC {c : ℝ} (hc : 0 < c) : Integrable (gaussC c) (volume : Measure ℝ) := by
  have hb : (0:ℝ) < ((c : ℂ)).re := by simpa using hc
  have h := integrable_cexp_quadratic (b := (π : ℂ) * (c : ℂ)) (by simpa using by positivity) 0 0
  have hfun : gaussC c = fun x : ℝ => Complex.exp (-((π : ℂ) * (c : ℂ)) * (x:ℂ) ^ 2 + 0 * x + 0) := by
    funext x
    rw [gaussC, Cvs.WeilForm.GaussianRegulariser.gauss, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hfun]
  exact h

end Cvs.WeilForm.RegulariserTransform
