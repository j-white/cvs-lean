import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zero-side sample of a window test is its Mellin transform at `1 − ρ`

For `0 ≤ L`, `v` vanishing off `[e^{−L}, 1]` and `f(s) = v(e^{s−L})e^{(s−L)/2}` (`SpineCouplingTailPairing`'s `fv` at `L = log x`), every `ξ ∈ ℂ`
gives `W_L f(ξ) = e^{−iLξ} M[v](½ − iξ)`; at `zPoint ρ` this is `e^{L(½−ρ)} M[v](1 − ρ)`, at the grid `2πk/L` it is
`M[v](½ − 2πik/L)` (so `∫₀^L f cos(2πks/L) = Re M[v](½ − 2πik/L)`), and `sqTransform(zPoint ρ) = M[v](1 − ρ) M[v](ρ)`. For `v = k_G`, `a = e^{−L}`, G C¹ with `∫₀¹G = 0`
and `ρ` a zero in the strip: `W_L f(zPoint ρ) = −e^{L(½−ρ)} M[1_{(1,∞)}E_G](1 − ρ)`, `sqTransform = M[ext](1 − ρ) M[ext](ρ)`.
-/

noncomputable section

open Real Set MeasureTheory Complex
open Cvs.Xi.EImageWindowPoisson (window window_of_notMem)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)

namespace Cvs.WeilForm.ZeroSideSampleMellin

/-- **The Mellin transform in the additive variable**: `M[f](s) = ∫_ℝ e^{su} f(eᵘ) du`. -/
theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, Complex.exp (s * u) * f (Real.exp u) := by
  have himg : Real.exp '' univ = Ioi (0 : ℝ) := by rw [image_univ, Real.range_exp]
  rw [mellin, ← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [abs_of_pos (Real.exp_pos u), Complex.real_smul, smul_eq_mul]
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_pos.le), ← mul_assoc,
    ← Complex.exp_add]
  congr 2; ring

/-- The window test in the log variable: `f(s) = v(e^{s−L}) e^{(s−L)/2}`. -/
def logWin (L : ℝ) (v : ℝ → ℝ) (s : ℝ) : ℝ := Cvs.L2a.TailLogScaleTest.logScale v (s - L)

theorem fv_eq_logWin (x : ℕ) (v : ℝ → ℝ) :
    Cvs.Approximant.SpineCouplingTailPairing.fv x v = logWin (Real.log x) v := rfl

/-- **The window transform of a window test is its Mellin transform on the line**, up to the phase
`e^{−iLξ}`: for `0 ≤ L`, `v` vanishing off `[e^{−L}, 1]` and every `ξ ∈ ℂ`,
`W_L f(ξ) = e^{−iLξ} M[v](½ − iξ)`. -/
theorem windowTransform_logWin {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℝ}
    (hv : ∀ θ ∉ Icc (Real.exp (-L)) 1, v θ = 0) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (logWin L v)) ξ
      = Complex.exp (-((L : ℂ) * ξ) * I) * mellinR v (1 / 2 - ξ * I) := by
  set w : ℂ := 1 / 2 - ξ * I
  set g : ℝ → ℂ := fun u => Complex.exp (w * u) * (v (Real.exp u) : ℂ)
  have hzero : ∀ u ∉ Icc (-L) 0, g u = 0 := by
    intro u hu
    have : Real.exp u ∉ Icc (Real.exp (-L)) 1 := by
      rintro ⟨h1, h2⟩
      exact hu ⟨Real.exp_le_exp.1 h1, by rw [← Real.exp_zero] at h2; exact Real.exp_le_exp.1 h2⟩
    simp [g, hv _ this]
  have hM : mellinR v w = ∫ t in (0 : ℝ)..L, g (t - L) := by
    unfold mellinR
    rw [mellin_eq_integral_exp, intervalIntegral.integral_comp_sub_right, zero_sub, sub_self,
      intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [hM, ← intervalIntegral.integral_const_mul]
  unfold Cvs.Detection.windowTransform
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [g, w, Cvs.WeilForm.SelfConvolutionTransform.cf, logWin, Cvs.L2a.TailLogScaleTest.logScale]
  push_cast
  have e : Complex.exp (-((L : ℂ) * ξ) * I) * (Complex.exp ((1 / 2 - ξ * I) * ((t : ℂ) - L)))
      = Complex.exp (-((t : ℂ) * ξ) * I) * Complex.exp (((t : ℂ) - L) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  linear_combination (-(v (Real.exp (t - L)) : ℂ)) * e

/-- `½ − i·zPoint ρ = 1 − ρ`. -/
theorem half_sub_zPoint (ρ : ℂ) : (1 : ℂ) / 2 - (-I * (ρ - 1 / 2)) * I = 1 - ρ := by
  ring_nf; rw [Complex.I_sq]; ring

/-- `½ + i·zPoint ρ = ρ`. -/
theorem half_sub_neg_zPoint (ρ : ℂ) : (1 : ℂ) / 2 - (-(-I * (ρ - 1 / 2))) * I = ρ := by
  ring_nf; rw [Complex.I_sq]; ring

/-- **The zero-side sample**: `W_L f(zPoint ρ) = e^{L(½−ρ)} M[v](1 − ρ)` for every `ρ ∈ ℂ`. -/
theorem windowTransform_logWin_zPoint {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℝ}
    (hv : ∀ θ ∉ Icc (Real.exp (-L)) 1, v θ = 0) (ρ : ℂ) :
    Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (logWin L v)) (-I * (ρ - 1 / 2))
      = Complex.exp ((L : ℂ) * (1 / 2 - ρ)) * mellinR v (1 - ρ) := by
  rw [windowTransform_logWin hL hv, half_sub_zPoint]
  congr 2; ring_nf; rw [Complex.I_sq]; ring

/-- At the reflected point, `W_L f(−zPoint ρ) = e^{L(ρ−½)} M[v](ρ)`. -/
theorem windowTransform_logWin_neg_zPoint {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℝ}
    (hv : ∀ θ ∉ Icc (Real.exp (-L)) 1, v θ = 0) (ρ : ℂ) :
    Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (logWin L v)) (-(-I * (ρ - 1 / 2)))
      = Complex.exp ((L : ℂ) * (ρ - 1 / 2)) * mellinR v ρ := by
  rw [windowTransform_logWin hL hv, half_sub_neg_zPoint]
  congr 2; ring_nf; rw [Complex.I_sq]; ring

/-- **The square transform at a zero point is a Mellin product**, the phases cancelling:
`sqTransform(zPoint ρ) = M[v](1 − ρ) · M[v](ρ)`. -/
theorem sqTransform_logWin_zPoint {L : ℝ} (hL : 0 ≤ L) {v : ℝ → ℝ}
    (hv : ∀ θ ∉ Icc (Real.exp (-L)) 1, v θ = 0) (ρ : ℂ) :
    Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (logWin L v)) (-I * (ρ - 1 / 2))
      = mellinR v (1 - ρ) * mellinR v ρ := by
  unfold Cvs.Detection.sqTransform
  rw [windowTransform_logWin_zPoint hL hv, windowTransform_logWin_neg_zPoint hL hv]
  have : Complex.exp ((L : ℂ) * (1 / 2 - ρ)) * Complex.exp ((L : ℂ) * (ρ - 1 / 2)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  linear_combination (mellinR v (1 - ρ) * mellinR v ρ) * this

end Cvs.WeilForm.ZeroSideSampleMellin
