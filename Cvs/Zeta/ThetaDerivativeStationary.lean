import Mathlib
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound
import Cvs.Zeta.RiemannSiegelPhase

/-!
# `θ'` is a derivative, branch-free, and the stationary point is unique

`RiemannSiegelPhase`–`an earlier result` proved facts about `archScore` as a *series*: it is `θ'` numerically, it is
strictly monotone, it grows at rate `1/t`, it is unbounded.
-/

open Complex

namespace Cvs.Zeta.ThetaDerivativeStationary
open Cvs.ArchScore

/-- The critical line as a map `ℝ → ℂ`, in the argument shape `ArchimedeanIntegrand.archScore` uses. -/
noncomputable def gline (t : ℝ) : ℂ := Gammaℝ (1 / 2 + I * t)

theorem re_crit (t : ℝ) : ((1 : ℂ) / 2 + I * t).re = 1 / 2 := by simp

theorem gline_ne_zero (t : ℝ) : gline t ≠ 0 := by
  refine Gammaℝ_ne_zero_of_re_pos ?_
  rw [re_crit]; norm_num

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hinv : DifferentiableAt ℂ (fun z => (Gammaℝ z)⁻¹) s :=
    (differentiable_Gammaℝ_inv s)
  have h2 : DifferentiableAt ℂ (fun z => ((Gammaℝ z)⁻¹)⁻¹) s :=
    hinv.inv (by simpa using hs)
  simpa [inv_inv] using h2

/-- The inner map `t ↦ ½ + i t` has derivative `i`. -/
theorem hasDerivAt_crit (t : ℝ) :
    HasDerivAt (fun x : ℝ => (1 : ℂ) / 2 + I * x) I t := by
  have h0 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  simpa using ((h0.const_mul I).const_add ((1 : ℂ) / 2))

theorem hasDerivAt_gline (t : ℝ) :
    HasDerivAt gline (I * deriv Gammaℝ (1 / 2 + I * t)) t := by
  have hg : HasDerivAt Gammaℝ (deriv Gammaℝ (1 / 2 + I * t)) (1 / 2 + I * t) :=
    (differentiableAt_Gammaℝ (gline_ne_zero t)).hasDerivAt
  have h : HasDerivAt (Gammaℝ ∘ fun x : ℝ => (1 : ℂ) / 2 + I * x)
      (deriv Gammaℝ (1 / 2 + I * t) * I) t :=
    HasDerivAt.comp (𝕜 := ℝ) (𝕜' := ℂ) t hg (hasDerivAt_crit t)
  rw [mul_comm] at h
  exact h

/-- **The logarithmic derivative along the line is `i` times the one across it.** -/
theorem logDeriv_gline (t : ℝ) :
    logDeriv gline t = I * logDeriv Gammaℝ (1 / 2 + I * t) := by
  rw [logDeriv_apply, logDeriv_apply, (hasDerivAt_gline t).deriv, mul_div_assoc]
  rfl

/-- **`θ' = archScore`, branch-free.**  `θ = arg ∘ gline` is only locally defined, but
`Im (gline'/gline)` is global, and it is what `θ'` means. -/
theorem im_logDeriv_gline (t : ℝ) :
    (logDeriv gline t).im = Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore t := by
  rw [logDeriv_gline, ← Cvs.ArchScore.archScore_eq, Cvs.Detection.archScore]
  simp [Complex.mul_im]

theorem isOpen_rePos : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem crit_mem (t : ℝ) : ((1 : ℂ) / 2 + I * t) ∈ {s : ℂ | 0 < s.re} := by
  simp only [Set.mem_ofPred_eq, re_crit]; norm_num

theorem continuous_crit : Continuous (fun t : ℝ => (1 : ℂ) / 2 + I * t) :=
  continuous_const.add (continuous_const.mul Complex.continuous_ofReal)

theorem differentiableOn_Gammaℝ_rePos : DifferentiableOn ℂ Gammaℝ {s : ℂ | 0 < s.re} :=
  fun _ hs => (differentiableAt_Gammaℝ (Gammaℝ_ne_zero_of_re_pos hs)).differentiableWithinAt

theorem continuous_gline : Continuous gline :=
  differentiableOn_Gammaℝ_rePos.continuousOn.comp_continuous continuous_crit crit_mem

theorem continuous_deriv_gline : Continuous (fun t : ℝ => deriv Gammaℝ (1 / 2 + I * t)) :=
  (((differentiableOn_Gammaℝ_rePos.analyticOnNhd isOpen_rePos).deriv_of_isOpen
      isOpen_rePos).continuousOn).comp_continuous continuous_crit crit_mem

/-- **`archScore` is continuous.**  It is the imaginary part of `deriv gline / gline`; the
numerator is continuous because `Gammaℝ` is analytic on `re > 0`, the denominator because it is
continuous and nonvanishing there. -/
theorem continuous_archScore : Continuous Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore := by
  have hq : Continuous (fun t : ℝ => (I * deriv Gammaℝ (1 / 2 + I * t)) / gline t) :=
    (continuous_const.mul continuous_deriv_gline).div continuous_gline gline_ne_zero
  refine (Complex.continuous_im.comp hq).congr (fun t => ?_)
  rw [Function.comp_apply, ← im_logDeriv_gline t, logDeriv_apply, (hasDerivAt_gline t).deriv]

/-! ### The twisted phase -/

end Cvs.Zeta.ThetaDerivativeStationary
