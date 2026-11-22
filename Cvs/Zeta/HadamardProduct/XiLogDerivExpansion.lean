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
import Cvs.Zeta.HadamardProduct.GenusOneTermwiseDeriv
import Cvs.Zeta.HadamardProduct.HadamardXiSplit
import Cvs.Zeta.HadamardProduct.XiAffineExponent
import Cvs.Zeta.HadamardProduct.XiExceptionalSet
import Cvs.Zeta.RiemannXi

/-!
# The constant, evaluated: rung 3 without an existential

`XiAffineExponent` gives `ξ'/ξ = (small poles) + (genus-1 series) + a` with `a` existentially quantified.
-/

noncomputable section

open Complex Filter Topology Finset Cvs.Zeta

namespace Cvs.ZeroFree

/-- **Everything exceptional is a zero** — the converse of `XiExceptionalSet.mem_xiExceptional_of_zero`,
so the two sets coincide. -/
theorem zero_of_mem_xiExceptional {z : ℂ} (hz : z ∈ Cvs.ZeroFree.xiExceptional) :
    riemannXi z = 0 := by
  rcases hz with h | h
  · obtain ⟨n, rfl⟩ := h
    exact Cvs.ZeroFree.riemannXi_zeroSeq n
  · rw [Cvs.ZeroFree.smallS, Finset.mem_coe, Set.Finite.mem_toFinset] at h
    by_contra hc
    refine h.2 ?_
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (Set.mem_univ z)]
    have hord : analyticOrderAt riemannXi z = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr hc
    rw [hord]
    simp

/-- `ξ(0) = 1/2`, so the origin is not exceptional. -/
theorem zero_notMem_xiExceptional : (0 : ℂ) ∉ Cvs.ZeroFree.xiExceptional := by
  intro hc
  have := zero_of_mem_xiExceptional hc
  rw [riemannXi_zero] at this
  norm_num at this

/-- The small-zero poles at the origin. -/
theorem smallSum_zero :
    Cvs.ZeroFree.smallSum 0 = -∑ u ∈ Cvs.ZeroFree.smallS, (Cvs.ZeroFree.mult u : ℂ) / u := by
  simp only [Cvs.ZeroFree.smallSum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [zero_sub, div_neg]

/-- **The genus-1 series vanishes at the origin** — term by term. -/
theorem tsum_genus_one_zero :
    (∑' n : zeroIndex riemannXi,
      (1 / ((0 : ℂ) - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n)) = 0 := by
  simpa only [Cvs.ZeroFree.genus_one_at_zero] using tsum_zero

/-- **Rung 3 with nothing quantified away.** -/
theorem logDeriv_riemannXi_expansion {z : ℂ} (hz : riemannXi z ≠ 0) :
    logDeriv riemannXi z
      = Cvs.ZeroFree.smallSum z
        + ((∑' n : zeroIndex riemannXi,
            (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n))
          + (logDeriv riemannXi 0 + ∑ u ∈ Cvs.ZeroFree.smallS, (Cvs.ZeroFree.mult u : ℂ) / u)) := by
  obtain ⟨B, hB⟩ := Cvs.ZeroFree.exists_const_logDeriv_riemannXi
  have h0 := hB 0 zero_notMem_xiExceptional
  rw [smallSum_zero, tsum_genus_one_zero] at h0
  have hBval : B = logDeriv riemannXi 0 + ∑ u ∈ Cvs.ZeroFree.smallS, (Cvs.ZeroFree.mult u : ℂ) / u := by
    linear_combination -h0
  have hznot : z ∉ Cvs.ZeroFree.xiExceptional := fun hc => hz (zero_of_mem_xiExceptional hc)
  rw [← hBval]
  exact hB z hznot

end Cvs.ZeroFree
