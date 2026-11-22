import Mathlib
import Cvs.Zeta.DigammaStrip
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ZetaLowerBound
import Cvs.Zeta.ZetaZeroCount

/-!
# Splitting the vertical integral into its four summands

`Cvs.Zeta.XiPrimeSide` identifies `∫ (ζ'/ζ)·φ` with the von Mangoldt sum.
-/

open Complex Real MeasureTheory Set

namespace Cvs.Zeta

theorem vline_ne_one (y : ℝ) : ((2 : ℂ) + y * I) ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem vline_ne_zero' (y : ℝ) : ((2 : ℂ) + y * I) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem continuous_logDeriv_riemannZeta_vline :
    Continuous fun y : ℝ => logDeriv riemannZeta ((2 : ℂ) + y * I) := by
  have hpath : Continuous fun y : ℝ => ((2 : ℂ) + y * I) := by fun_prop
  have hana : ∀ y : ℝ, AnalyticAt ℂ riemannZeta ((2 : ℂ) + y * I) :=
    fun y => analyticAt_riemannZeta (vline_ne_one y)
  have hd : Continuous fun y : ℝ => deriv riemannZeta ((2 : ℂ) + y * I) :=
    continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (x := y) (f := fun t : ℝ => ((2 : ℂ) + t * I))
        ((hana y).deriv.continuousAt) hpath.continuousAt
  have hz : Continuous fun y : ℝ => riemannZeta ((2 : ℂ) + y * I) :=
    continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.comp (x := y) (f := fun t : ℝ => ((2 : ℂ) + t * I))
        ((hana y).continuousAt) hpath.continuousAt
  simp only [logDeriv_apply]
  exact hd.div hz fun y => riemannZeta_ne_zero_of_re_eq_two (by simp)

/-! ### The four bounds, in the shape `integrableOn_vline` consumes -/

/-! ### The archimedean summand -/

/-- Solving `logDeriv_riemannXi_eq_zeta_of_im_ne_zero` for the archimedean term.  This is
how the `Γ_ℝ` bound is obtained: by subtraction from three things already bounded, rather
than by re-deriving the digamma estimate. -/
theorem logDeriv_gammaR_eq {s : ℂ} (hs : s.im ≠ 0) (hζ : riemannZeta s ≠ 0) :
    logDeriv Gammaℝ s
      = logDeriv riemannXi s - 1 / s - 1 / (s - 1) - logDeriv riemannZeta s := by
  have h := logDeriv_riemannXi_eq_zeta_of_im_ne_zero hs hζ
  linear_combination -h

/-! ### Each summand is integrable, and the integral splits -/

section Split

variable {φ : ℂ → ℂ} {A : ℝ}

end Split

end Cvs.Zeta
