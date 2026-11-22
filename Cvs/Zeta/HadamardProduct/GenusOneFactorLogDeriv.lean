import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Hadamard
import Cvs.Zeta.Weierstrass

/-!
# The genus-1 logarithmic derivative, per factor

(d/dz) log E₁(z/a) = 1/(z-a) + 1/a , and its derivative is -(z-a)^{-2} .
-/

open Complex

namespace Cvs.ZeroFree

/-- **The genus-1 logarithmic derivative.** (d/dz) log E₁(z/a) = 1/(z-a) + 1/a . -/
theorem logDeriv_weierstrassE1_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun u : ℂ => Cvs.Zeta.weierstrassE1 (u / a)) z = 1 / (z - a) + 1 / a := by
  have hd := Cvs.Zeta.hasDerivAt_weierstrassE1_div a z
  rw [logDeriv_apply, hd.deriv]
  have hexp : Complex.exp (z / a) ≠ 0 := Complex.exp_ne_zero _
  rw [Cvs.Zeta.weierstrassE1]
  have hsub : (1 : ℂ) - z / a ≠ 0 := by
    intro hc
    apply hz
    field_simp at hc
    linear_combination -hc
  have hza : z - a ≠ 0 := sub_ne_zero_of_ne hz
  field_simp
  ring

/-- **And its derivative is the square term.**  `(1/(z-a) + 1/a)' = -(z-a)^{-2}`: the constant
`1/a` differentiates away, which is why `(φ'/φ)'` is the clean sum `-Σ_ρ (z-ρ)^{-2}` with no
genus correction left. -/
theorem hasDerivAt_logDeriv_term {a z : ℂ} (hz : z ≠ a) :
    HasDerivAt (fun u : ℂ => 1 / (u - a) + 1 / a) (-(1 / (z - a) ^ 2)) z := by
  have hza : z - a ≠ 0 := sub_ne_zero_of_ne hz
  have hsub : HasDerivAt (fun u : ℂ => u - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have hinv : HasDerivAt (fun u : ℂ => (u - a)⁻¹) (-1 / (z - a) ^ 2) z := hsub.inv hza
  have hone : HasDerivAt (fun u : ℂ => 1 / (u - a)) (-1 / (z - a) ^ 2) z := by
    simpa [one_div] using hinv
  have := hone.add_const (1 / a)
  refine this.congr_deriv ?_
  ring

end Cvs.ZeroFree
