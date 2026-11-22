import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The second Gaussian moment, by improper parts

`PolyGaussianIntegrable` made `y^{2m}e^{−λy²}` integrable; this evaluates the first case beyond
`integral_gaussian`.
-/

namespace Cvs.Moments

open MeasureTheory Filter Topology
open scoped Real

/-- `e^{−λy²/2} → 0` as `y → ∞`. -/
theorem tendsto_gauss_half {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun y : ℝ => Real.exp (-(lam / 2) * y ^ 2)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun y : ℝ => (lam / 2) * y ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith) (tendsto_pow_atTop two_ne_zero)
  have h1 : Tendsto (fun y : ℝ => -(lam / 2) * y ^ 2) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp h0
    simpa [Function.comp_def, neg_mul] using h
  exact Real.tendsto_exp_atBot.comp h1

end Cvs.Moments
