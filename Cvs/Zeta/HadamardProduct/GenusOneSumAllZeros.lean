import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.XiExceptionalSet
import Cvs.Zeta.HadamardProduct.XiLogDerivExpansion
import Cvs.Zeta.RiemannXi

/-!
# The closed form, simplified: one genus-1 sum over all zeros

`XiLogDerivExpansion` states `ξ'/ξ` with the zeros split in two, by modulus:
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.ZeroFree

/-- The small zeros, in the same genus-1 shape as the others. -/
def smallGenus (z : ℂ) : ℂ :=
  ∑ u ∈ Cvs.ZeroFree.smallS, (Cvs.ZeroFree.mult u : ℂ) * (1 / (z - u) + 1 / u)

/-- **The closed form, simplified.**  `ξ'/ξ` minus its value at the origin is a single
genus-1 sum over all the zeros. -/
theorem logDeriv_sub_logDeriv_zero {z : ℂ} (hz : riemannXi z ≠ 0) :
    logDeriv riemannXi z - logDeriv riemannXi 0
      = smallGenus z
        + ∑' n : zeroIndex riemannXi,
            (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n) := by
  have hexp := Cvs.ZeroFree.logDeriv_riemannXi_expansion hz
  have hmerge : smallGenus z
      = Cvs.ZeroFree.smallSum z + ∑ u ∈ Cvs.ZeroFree.smallS, (Cvs.ZeroFree.mult u : ℂ) / u := by
    rw [smallGenus, Cvs.ZeroFree.smallSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hmerge]
  linear_combination hexp

end Cvs.ZeroFree
