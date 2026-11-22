import Mathlib
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# The window transform of a cosine mode, in closed form

`∫₀^L cos(ωy) e^{−iξy} dy = −iξ(e^{−iξL} − 1)/(ω² − ξ²)` whenever `ξ² ≠ ω²` and `ωL ∈ 2πℤ`; at
`ω = 0` this is the constant's transform `i(e^{−iξL} − 1)/ξ`. The resonance at `ξ = ±ω` is
cancelled by the factor `e^{−iξL} − 1`, which vanishes there.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex
open Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.CosineModeTransform

/-- The antiderivative of `e^{−iξs} cos(ωs)`. -/
def cosAnti (ω : ℝ) (ξ : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (-((s : ℂ) * ξ) * I) * (-I * ξ * (Real.cos (ω * s) : ℂ) + (ω : ℂ) * (Real.sin (ω * s) : ℂ))
    / ((ω : ℂ) ^ 2 - ξ ^ 2)

theorem hasDerivAt_cosAnti (ω : ℝ) {ξ : ℂ} (hξ : (ω : ℂ) ^ 2 - ξ ^ 2 ≠ 0) (s : ℝ) :
    HasDerivAt (cosAnti ω ξ)
      (Complex.exp (-((s : ℂ) * ξ) * I) * (Real.cos (ω * s) : ℂ)) s := by
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * I))
      (Complex.exp (-((s : ℂ) * ξ) * I) * (-ξ * I)) s := by
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * ξ) * I) (-ξ * I) s := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ξ).neg.mul_const I
      simpa using this
    exact (Complex.hasDerivAt_exp _).comp s h1
  have hcos : HasDerivAt (fun s : ℝ => (Real.cos (ω * s) : ℂ))
      (((-Real.sin (ω * s) * ω : ℝ) : ℂ)) s := by
    have h := ((hasDerivAt_mul_const ω).cos (x := s))
    have h' : HasDerivAt (fun y => Real.cos (ω * y)) (-Real.sin (ω * s) * ω) s := by
      simpa [mul_comm] using h
    exact h'.ofReal_comp
  have hsin : HasDerivAt (fun s : ℝ => (Real.sin (ω * s) : ℂ))
      (((Real.cos (ω * s) * ω : ℝ) : ℂ)) s := by
    have h := ((hasDerivAt_mul_const ω).sin (x := s))
    have h' : HasDerivAt (fun y => Real.sin (ω * y)) (Real.cos (ω * s) * ω) s := by
      simpa [mul_comm] using h
    exact h'.ofReal_comp
  have hin : HasDerivAt (fun s : ℝ => -I * ξ * (Real.cos (ω * s) : ℂ) + (ω : ℂ) * (Real.sin (ω * s) : ℂ))
      (-I * ξ * (((-Real.sin (ω * s) * ω : ℝ) : ℂ)) + (ω : ℂ) * (((Real.cos (ω * s) * ω : ℝ) : ℂ))) s :=
    (hcos.const_mul _).add (hsin.const_mul _)
  have hprod := (hexp.mul hin).div_const ((ω : ℂ) ^ 2 - ξ ^ 2)
  refine hprod.congr_deriv ?_
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **The window transform of a cosine mode, in closed form.** -/
theorem windowTransform_cos_eq {L : ℝ} (ω : ℝ) {ξ : ℂ} (hξ : (ω : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.windowTransform L (cf fun y => Real.cos (ω * y)) ξ
      = cosAnti ω ξ L - cosAnti ω ξ 0 := by
  unfold Cvs.Detection.windowTransform
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_cosAnti ω hξ s) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine Continuous.continuousOn ?_
  unfold cf
  fun_prop

/-- **At an integer mode**, `ωL ∈ 2πℤ` and the boundary terms collapse. -/
theorem windowTransform_cos_eq_of_int {L : ℝ} (hL : 0 < L) (m : ℤ) {ξ : ℂ}
    (hξ : ((2 * π * m / L : ℝ) : ℂ) ^ 2 - ξ ^ 2 ≠ 0) :
    Cvs.Detection.windowTransform L (cf fun y => Real.cos (2 * π * m / L * y)) ξ
      = -I * ξ * (Complex.exp (-((L : ℂ) * ξ) * I) - 1) / (((2 * π * m / L : ℝ) : ℂ) ^ 2 - ξ ^ 2) := by
  rw [windowTransform_cos_eq _ hξ]
  unfold cosAnti
  have hcos : Real.cos (2 * π * m / L * L) = 1 := by
    rw [show 2 * π * m / L * L = (m : ℝ) * (2 * π) by rw [div_mul_cancel₀ _ hL.ne']; ring,
      Real.cos_int_mul_two_pi]
  have hsin : Real.sin (2 * π * m / L * L) = 0 := by
    rw [show 2 * π * m / L * L = ((2 * m : ℤ) : ℝ) * π by
      push_cast; rw [div_mul_cancel₀ _ hL.ne']; ring, Real.sin_int_mul_pi]
  rw [hcos, hsin]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, Complex.ofReal_zero, Complex.ofReal_one,
    Complex.ofReal_zero, zero_mul, mul_one, add_zero, neg_zero, Complex.exp_zero, one_mul]
  field_simp
  ring

end Cvs.Finite.CosineModeTransform
