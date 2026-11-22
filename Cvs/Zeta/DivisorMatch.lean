import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Cvs.Zeta.ZetaPolyGrowth
import Cvs.Zeta.ZetaZeroCount

/-!
# Matching the Landau zero set against the zero count

`Cvs.Zeta.XiPoleSum` needs `Σ_σ m_σ ≤ N`, where `S` is a set of **offsets** `σ` with `c + σ` a
zero of `ζ₁`, while the count bounds a divisor sum for `ζ`.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

/-- **Analytic order is translation invariant.** -/
theorem analyticOrderAt_comp_add (f : ℂ → ℂ) (c σ : ℂ) :
    analyticOrderAt (fun w : ℂ => f (c + w)) σ = analyticOrderAt f (c + σ) := by
  have hg : AnalyticAt ℂ (fun w : ℂ => c + w) σ := analyticAt_const.add analyticAt_id
  have hg' : deriv (fun w : ℂ => c + w) σ ≠ 0 := by
    rw [deriv_const_add']
    simp
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg hg'
  simp only [Function.comp_def] at h
  exact h

/-- **`ζ₁` and `ζ` have the same analytic order away from `s = 1`.**

`ζ₁ = (s−1)ζ` on a punctured neighbourhood, and `s − 1` has order `0` there. -/
theorem analyticOrderAt_riemannZeta₁_eq {u : ℂ} (hu : u ≠ 1) :
    analyticOrderAt riemannZeta₁ u = analyticOrderAt riemannZeta u := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => w - 1) u := (differentiable_id.sub_const 1).analyticAt u
  have hz : AnalyticAt ℂ riemannZeta u := analyticAt_riemannZeta hu
  have hev : riemannZeta₁ =ᶠ[nhds u] fun w : ℂ => (w - 1) * riemannZeta w := by
    filter_upwards [(isOpen_compl_singleton (x := (1 : ℂ))).mem_nhds hu] with w hw
    exact riemannZeta₁_eq_mul hw
  have hlin0 : analyticOrderAt (fun w : ℂ => w - 1) u = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr (sub_ne_zero.mpr hu)
  have hfun : (fun w : ℂ => (w - 1) * riemannZeta w)
      = (fun w : ℂ => w - 1) * riemannZeta := rfl
  rw [analyticOrderAt_congr hev, hfun, analyticOrderAt_mul hlin hz, hlin0, zero_add]

end Cvs.Zeta
