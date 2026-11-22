import Mathlib
import Cvs.Zeta.ArchimedeanChannelShift
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound
import Cvs.Zeta.RiemannSiegelPhase
import Cvs.Zeta.RiemannSiegelTheta

/-!
# The archimedean channel *is* `θ`

`ArchimedeanChannelShift` shifted the archimedean integral from `Re = 2` to the critical line.
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta

namespace Cvs.ZeroCounting

/-- The two spellings of the critical-line point agree. -/
theorem crit_point (y : ℝ) : (((1/2 : ℝ) : ℂ) + (y : ℂ) * I) = (1 : ℂ) / 2 + I * (y : ℂ) := by
  push_cast; ring

/-- The contour's archimedean integrand on the critical line is `Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound`'s `archScore`. -/
theorem re_logDeriv_crit (y : ℝ) :
    (logDeriv Gammaℝ (((1/2 : ℝ) : ℂ) + (y : ℂ) * I)).re = Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore y := by
  rw [crit_point, ← Cvs.Detection.archScore, Cvs.ArchScore.archScore_eq]

/-- `Γ_ℝ'/Γ_ℝ` is continuous along the critical line. -/
theorem continuous_logDeriv_gammaR_crit :
    Continuous fun y : ℝ => logDeriv Gammaℝ (((1/2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hpath : Continuous fun y : ℝ => (((1/2 : ℝ) : ℂ) + (y : ℂ) * I) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun y => ?_
  refine ContinuousAt.comp (f := fun t : ℝ => (((1/2 : ℝ) : ℂ) + (t : ℂ) * I)) ?_
    hpath.continuousAt
  refine (Cvs.ZeroCounting.differentiableAt_logDeriv_gammaR ?_).continuousAt
  show (0 : ℝ) < (((1/2 : ℝ) : ℂ) + (y : ℂ) * I).re
  simp

/-- **The critical-line archimedean integral is `θ`.** -/
theorem re_integral_crit_eq_theta (T : ℝ) :
    (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ (((1/2 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = Cvs.ZeroCounting.theta T := by
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
    (continuous_logDeriv_gammaR_crit.intervalIntegrable (μ := volume) 0 T)
  simp only [Complex.reCLM_apply] at hcomm
  rw [← hcomm]
  simp_rw [re_logDeriv_crit]
  rw [Cvs.ZeroCounting.theta]

/-- **The archimedean channel at `Re = 2`, in closed form.**  `θ(T)` plus one `T`-dependent
correction and one constant. -/
theorem re_integral_two_eq_theta_add {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re
      = Cvs.ZeroCounting.theta T
        + (∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ) + (T : ℂ) * I)).im
        - (∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ))).im := by
  have h := Cvs.ZeroCounting.re_vertical_shift hT
  rw [re_integral_crit_eq_theta T] at h
  linarith

end Cvs.ZeroCounting
