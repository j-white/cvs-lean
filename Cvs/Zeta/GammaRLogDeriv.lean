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

/-!
# The archimedean logarithmic derivative

`Cvs.Zeta.logDeriv_riemannXi_eq_zeta` expresses `ξ'/ξ` as `1/s + 1/(s−1) + (Γ_ℝ)'/Γ_ℝ + ζ'/ζ`,
with the third term opaque.
-/

open Complex Real

namespace Cvs.Zeta

theorem pi_cpow_eq_exp (z : ℂ) :
    ((π : ℂ)) ^ (-z / 2) = Complex.exp (Complex.log (π : ℂ) * (-z / 2)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]

theorem hasDerivAt_pi_cpow (s : ℂ) :
    HasDerivAt (fun z : ℂ => ((π : ℂ)) ^ (-z / 2))
      (((π : ℂ)) ^ (-s / 2) * (Complex.log (π : ℂ) * (-1 / 2))) s := by
  have hlin : HasDerivAt (fun z : ℂ => Complex.log (π : ℂ) * (-z / 2))
      (Complex.log (π : ℂ) * (-1 / 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    simpa using h1.const_mul (Complex.log (π : ℂ))
  have hfun : (fun z : ℂ => ((π : ℂ)) ^ (-z / 2))
      = fun z : ℂ => Complex.exp (Complex.log (π : ℂ) * (-z / 2)) := funext pi_cpow_eq_exp
  rw [hfun]
  have h := hlin.cexp
  rwa [← pi_cpow_eq_exp s] at h

theorem logDeriv_pi_cpow (s : ℂ) :
    logDeriv (fun z : ℂ => ((π : ℂ)) ^ (-z / 2)) s = -(Complex.log (π : ℂ)) / 2 := by
  have hne : ((π : ℂ)) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro hc
    exact absurd hc (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [logDeriv_apply, (hasDerivAt_pi_cpow s).deriv]
  field_simp

theorem logDeriv_gamma_half {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hs
  have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hchain : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := hd.hasDerivAt.comp s h1
  rw [logDeriv_apply, hchain.deriv, Complex.digamma, logDeriv_apply]
  field_simp

/-- **`(Γ_ℝ)'/Γ_ℝ = −½ log π + ½ ψ(s/2)`.** The archimedean log-derivative in closed form. -/
theorem logDeriv_gammaR {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    logDeriv Gammaℝ s = -(Complex.log (π : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have hpi : ((π : ℂ)) ^ (-s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro hc
    exact absurd hc (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => ((π : ℂ)) ^ (-z / 2)) s :=
    (hasDerivAt_pi_cpow s).differentiableAt
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact ((Complex.differentiableAt_Gamma _ hs).hasDerivAt.comp s h1).differentiableAt
  have hfun : Gammaℝ = fun z : ℂ => ((π : ℂ)) ^ (-z / 2) * Complex.Gamma (z / 2) := rfl
  rw [hfun, logDeriv_fun_mul s hpi hΓ hd1 hd2, logDeriv_pi_cpow, logDeriv_gamma_half hs]

end Cvs.Zeta
