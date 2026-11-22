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
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.GammaRLogDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean integrand is differentiable on the strip
-/

namespace Cvs.Detection

open Complex
open scoped Real

theorem ne_neg_nat_of_re_pos' {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -m := by
  intro h
  rw [h] at hz
  simp at hz
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- `Γ` is analytic on the right half-plane. -/
theorem analyticOnNhd_Gamma :
    AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) ?_
  · exact (Complex.differentiableAt_Gamma z (ne_neg_nat_of_re_pos' hz)).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

/-- **`digamma` is differentiable on the right half-plane.**  `logDeriv` is a
quotient involving `deriv Γ`, so this needs `Γ` analytic, not merely
differentiable. -/
theorem differentiableAt_digamma {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z := by
  have hmem : z ∈ {w : ℂ | 0 < w.re} := hz
  have hA : AnalyticAt ℂ Complex.Gamma z := analyticOnNhd_Gamma z hmem
  have hd : DifferentiableAt ℂ (deriv Complex.Gamma) z := hA.deriv.differentiableAt
  have hG : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (ne_neg_nat_of_re_pos' hz)
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (ne_neg_nat_of_re_pos' hz)
  rw [Complex.digamma_def]
  show DifferentiableAt ℂ (fun w => deriv Complex.Gamma w / Complex.Gamma w) z
  exact hd.div hG hne

/-- **`logDeriv Γ_ℝ` is differentiable on the right half-plane**, so in
particular on the strip `½ ≤ Re z ≤ 2`. -/
theorem differentiableAt_logDeriv_gammaR {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (logDeriv Gammaℝ) z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z ∈ {w : ℂ | 0 < w.re} := hz
  have heq : ∀ w ∈ {w : ℂ | 0 < w.re},
      logDeriv Gammaℝ w = -(Complex.log (π : ℂ)) / 2 + Complex.digamma (w / 2) / 2 := by
    intro w hw
    have hw' : 0 < w.re := hw
    refine Cvs.Zeta.logDeriv_gammaR fun m => ?_
    refine ne_neg_nat_of_re_pos' ?_ m
    simp only [Complex.div_re]
    simp
    linarith
  have hev : logDeriv Gammaℝ =ᶠ[nhds z]
      fun w => -(Complex.log (π : ℂ)) / 2 + Complex.digamma (w / 2) / 2 :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) heq
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hhalf : (0 : ℝ) < (z / 2).re := by
    simp only [Complex.div_re]
    simp
    linarith
  have h1 : DifferentiableAt ℂ (fun w : ℂ => w / 2) z := (differentiableAt_id).div_const 2
  exact ((differentiableAt_digamma hhalf).comp z h1).div_const 2 |>.const_add _

end Cvs.Detection
