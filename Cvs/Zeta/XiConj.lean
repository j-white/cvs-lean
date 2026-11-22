import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiZetaBridge

/-!
# `ξ` commutes with conjugation, and the bottom horizontal is the mirror of the top

The contour's rectangle is symmetric, `[−1,2] × [−T',T']`, but the `O(log²T)` bound of
`Cvs.Zeta.XiLogSqFull` is proved at `+T'` only — it comes from a zero-free height near `+T`.
-/

open Complex Real

namespace Cvs.Zeta

/-- `Γ_ℝ` commutes with conjugation.  `π` is real so `cpow_conj` applies to the power, and
`Gamma_conj` handles the rest. -/
theorem gammaR_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have harg : ((π : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact fun h => Real.pi_ne_zero h.symm
  have hcpow : ((π : ℂ)) ^ (-(starRingEnd ℂ) s / 2)
      = (starRingEnd ℂ) (((π : ℂ)) ^ (-s / 2)) := by
    have h : -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2) := by
      rw [map_div₀, map_neg, map_ofNat]
    rw [h, Complex.cpow_conj _ _ harg]
    simp
  rw [Gammaℝ_def, Gammaℝ_def, hcpow, map_mul]
  congr 1
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [h2, Complex.Gamma_conj]

/-- **`ξ` commutes with conjugation** — `ξ` is real on the real axis. -/
theorem riemannXi_conj (s : ℂ) :
    riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannXi s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (riemannXi ((starRingEnd ℂ) z)) with hg
  have hgdiff : Differentiable ℂ g := by
    intro x
    have h := ((differentiable_riemannXi ((starRingEnd ℂ) x)).hasDerivAt).conj_conj
    simp only [Function.comp_def, Complex.conj_conj] at h
    exact h.differentiableAt
  have hgana : AnalyticOnNhd ℂ g Set.univ := fun z _ => hgdiff.analyticAt z
  have hxi : ∀ z : ℂ, 1 < z.re → g z = riemannXi z := by
    intro z hz
    have hz1 : z ≠ 1 := by intro hc; rw [hc] at hz; simp at hz
    have hzc1 : (starRingEnd ℂ) z ≠ 1 := by
      intro hc
      apply hz1
      have := congrArg (starRingEnd ℂ) hc
      simpa using this
    have hzcre : ((starRingEnd ℂ) z).re = z.re := by simp
    rw [hg]
    simp only
    rw [riemannXi_eq_gammaR_mul_zeta_of_re_pos hzc1 (by rw [hzcre]; linarith),
      gammaR_conj, riemannZeta_conj,
      riemannXi_eq_gammaR_mul_zeta_of_re_pos hz1 (by linarith)]
    simp [map_div₀, map_ofNat]
  have hev : g =ᶠ[nhds (2 : ℂ)] riemannXi := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by simp)] with z hz using hxi z hz
  have := hgana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_riemannXi
    (isPreconnected_univ) (Set.mem_univ (2 : ℂ)) hev (Set.mem_univ s)
  have h2 := congrArg (starRingEnd ℂ) this
  simpa [hg] using h2

theorem deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv riemannXi s) := by
  have h := (differentiable_riemannXi s).hasDerivAt.conj_conj
  have hfun : (starRingEnd ℂ) ∘ riemannXi ∘ (starRingEnd ℂ) = riemannXi := by
    funext z
    simp [Function.comp_def, riemannXi_conj]
  rw [hfun] at h
  exact h.deriv

theorem logDeriv_riemannXi_conj (s : ℂ) :
    logDeriv riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv riemannXi s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]

/-- **The bottom horizontal is the mirror of the top.**  This is what lets the rectangle stay
symmetric: the `O(log²T)` bound is proved at `+T'` only, and reflection carries it to `−T'`
with no second zero-free height and no second Landau estimate. -/
theorem norm_logDeriv_riemannXi_reflect (x T : ℝ) :
    ‖logDeriv riemannXi ((x : ℂ) - T * I)‖ = ‖logDeriv riemannXi ((x : ℂ) + T * I)‖ := by
  have hc : ((x : ℂ) - T * I) = (starRingEnd ℂ) ((x : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [hc, logDeriv_riemannXi_conj, Complex.norm_conj]

end Cvs.Zeta
