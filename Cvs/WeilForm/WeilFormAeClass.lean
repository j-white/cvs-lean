import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Weil form sees only the a.e. class

    f =ᵐ g  ⟹  weilForm P R f = weilForm P R g

which is what lets the window's form descend to `L²`.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormAeClass

/-- **Translation preserves a.e. equality.**  Lebesgue measure is translation invariant, so the
shifted factor inside the self-convolution cannot see a null set. -/
theorem ae_eq_shift {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (t : ℝ) :
    (fun x => f (x + t)) =ᵐ[volume] fun x => g (x + t) := by
  have hmeas : AEMeasurable (fun x : ℝ => x + t) volume :=
    (measurable_add_const t).aemeasurable
  have hmap : (volume : Measure ℝ).map (fun x : ℝ => x + t) = volume :=
    map_add_right_eq_self volume t
  exact MeasureTheory.ae_eq_comp hmeas (by rw [hmap]; exact h)

/-- **The self-convolution only sees the class.** -/
theorem selfConvolution_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (t : ℝ) :
    selfConvolution f t = selfConvolution g t := by
  unfold selfConvolution
  refine integral_congr_ae ?_
  filter_upwards [h, ae_eq_shift h t] with x hx hxt
  rw [hx, hxt]

/-- The self-convolution, as a function, only sees the class. -/
theorem selfConvolution_eq_of_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    selfConvolution f = selfConvolution g :=
  funext fun t => selfConvolution_congr_ae h t

/-- **A weighted integral only sees the class.**  This is the pole side. -/
theorem integral_mul_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (w : ℝ → ℝ) :
    (∫ s : ℝ, f s * w s) = ∫ s : ℝ, g s * w s := by
  refine integral_congr_ae ?_
  filter_upwards [h] with s hs
  rw [hs]

/-- **The Weil form is a functional of the class.**  Every piece — pole, archimedean Lévy
energy, truncated prime side — is an integral in `f`, so none of them sees a null set. -/
theorem weilForm_congr_ae (P R : ℕ) {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g := by
  unfold Cvs.WeilForm.SelfConvolutionFunctional.weilForm
  rw [integral_mul_congr_ae h (fun s => Real.exp (s / 2)),
    integral_mul_congr_ae h (fun s => Real.exp (-(s / 2))),
    selfConvolution_eq_of_ae h]

end Cvs.WeilForm.WeilFormAeClass
