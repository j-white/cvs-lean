import Mathlib
import Cvs.Zeta.PoleTermsExact
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVerticalLimit
import Cvs.Zeta.XiZetaBridge
import Cvs.Zeta.ZetaZeroCount

/-!
# The vertical, split into its four channels
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta

namespace Cvs.ZeroCounting

/-- The line `Re s = 2` avoids `1`, and `ζ` does not vanish there. -/
theorem zeta_ne_zero_line (y : ℝ) : riemannZeta ((2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp

theorem line_ne_one (y : ℝ) : ((2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
  intro hc
  have h : ((2 : ℂ) + (y : ℂ) * I).re = 1 := by rw [hc]; simp
  simp at h

theorem line_re (y : ℝ) : (0 : ℝ) < ((2 : ℂ) + (y : ℂ) * I).re := by simp

/-- `ζ'/ζ` is continuous along `Re s = 2`. -/
theorem continuous_logDeriv_zeta_line :
    Continuous fun y : ℝ => logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) := by
  have hpath : Continuous fun y : ℝ => ((2 : ℂ) + (y : ℂ) * I) := by fun_prop
  have hd : Continuous fun y : ℝ => deriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact ContinuousAt.comp (f := fun t : ℝ => ((2 : ℂ) + (t : ℂ) * I))
      (((analyticAt_riemannZeta (line_ne_one y)).deriv).continuousAt) hpath.continuousAt
  have hz : Continuous fun y : ℝ => riemannZeta ((2 : ℂ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact ContinuousAt.comp (f := fun t : ℝ => ((2 : ℂ) + (t : ℂ) * I))
      ((analyticAt_riemannZeta (line_ne_one y)).continuousAt) hpath.continuousAt
  simp only [logDeriv_apply]
  exact hd.div hz zeta_ne_zero_line

/-- The two pole channels are continuous along the line. -/
theorem continuous_pole_two :
    Continuous fun y : ℝ => (1 : ℂ) / (((2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  refine continuous_const.div₀ (by fun_prop) (fun y hc => ?_)
  have : (((2 : ℝ) : ℂ) + (y : ℂ) * I).re = 0 := by rw [hc]; simp
  simp at this

theorem continuous_pole_one :
    Continuous fun y : ℝ => (1 : ℂ) / (((1 : ℝ) : ℂ) + (y : ℂ) * I) := by
  refine continuous_const.div₀ (by fun_prop) (fun y hc => ?_)
  have : (((1 : ℝ) : ℂ) + (y : ℂ) * I).re = 0 := by rw [hc]; simp
  simp at this

/-- The archimedean channel is continuous — as the difference of the other four, so no
analyticity of `Γ_ℝ` is needed. -/
theorem continuous_logDeriv_gammaR_line :
    Continuous fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I) := by
  have heq : (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I))
      = fun y : ℝ => logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)
          - (1 : ℂ) / (((2 : ℝ) : ℂ) + (y : ℂ) * I)
          - (1 : ℂ) / (((1 : ℝ) : ℂ) + (y : ℂ) * I)
          - logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I) := by
    funext y
    have h := logDeriv_riemannXi_eq_zeta (line_re y) (line_ne_one y) (zeta_ne_zero_line y)
    have hs : ((2 : ℂ) + (y : ℂ) * I) - 1 = ((1 : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
    rw [hs] at h
    push_cast at h ⊢
    linear_combination -h
  rw [heq]
  exact ((continuous_logDeriv_riemannXi_vertical.sub continuous_pole_two).sub
    continuous_pole_one).sub continuous_logDeriv_zeta_line

/-- **The vertical, split.**  Pole channel in closed form, the other two named. -/
theorem re_vertical_split (T : ℝ) :
    (∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).re
      = 2 * Real.arctan (T / 2) + 2 * Real.arctan T
        + (∫ y in (-T)..T, logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re
        + (∫ y in (-T)..T, logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
  have hpt : ∀ y : ℝ, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)
      = ((1 : ℂ) / (((2 : ℝ) : ℂ) + (y : ℂ) * I)
          + (1 : ℂ) / (((1 : ℝ) : ℂ) + (y : ℂ) * I))
        + (logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)
          + logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)) := by
    intro y
    have h := logDeriv_riemannXi_eq_zeta (line_re y) (line_ne_one y) (zeta_ne_zero_line y)
    have hs : ((2 : ℂ) + (y : ℂ) * I) - 1 = ((1 : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
    rw [hs] at h
    push_cast at h ⊢
    linear_combination h
  have iP2 := continuous_pole_two.intervalIntegrable (μ := volume) (-T) T
  have iP1 := continuous_pole_one.intervalIntegrable (μ := volume) (-T) T
  have iG := continuous_logDeriv_gammaR_line.intervalIntegrable (μ := volume) (-T) T
  have iZ := continuous_logDeriv_zeta_line.intervalIntegrable (μ := volume) (-T) T
  calc (∫ y in (-T)..T, logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).re
      = (∫ y in (-T)..T, (((1 : ℂ) / (((2 : ℝ) : ℂ) + (y : ℂ) * I)
            + (1 : ℂ) / (((1 : ℝ) : ℂ) + (y : ℂ) * I))
          + (logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)
            + logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)))).re := by
        simp_rw [← hpt]
    _ = 2 * Real.arctan (T / 2) + 2 * Real.arctan T
          + (∫ y in (-T)..T, logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re
          + (∫ y in (-T)..T, logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
        rw [intervalIntegral.integral_add (iP2.add iP1) (iG.add iZ),
          intervalIntegral.integral_add iP2 iP1,
          intervalIntegral.integral_add iG iZ]
        simp only [Complex.add_re]
        rw [Cvs.ZeroCounting.re_integral_poles T]
        ring

end Cvs.ZeroCounting
