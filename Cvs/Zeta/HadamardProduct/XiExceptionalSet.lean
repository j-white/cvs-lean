import Mathlib.Analysis.Calculus.LogDeriv
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
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.HadamardXiSplit
import Cvs.Zeta.HadamardProduct.XiZerosCountable
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.Weierstrass

/-!
# Instantiating the criterion at `ξ`: the exceptional set and Hadamard
-/

noncomputable section

open Complex Filter Topology Finset Cvs.Zeta

namespace Cvs.ZeroFree

/-- The zeros of `ξ` inside the unit disc, as a `Finset`. -/
def smallS : Finset ℂ := finite_xiSmallZeros.toFinset

/-- The multiplicity of a zero of `ξ`. -/
def mult (u : ℂ) : ℕ := ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat

/-- Where the criterion's identities are allowed to fail: every zero of `ξ`. -/
def xiExceptional : Set ℂ := Set.range (zeroSeq riemannXi) ∪ (smallS : Set ℂ)

/-- The finite factor's contribution to `ξ'/ξ` — bare poles, no genus-1 correction. -/
def smallSum (z : ℂ) : ℂ := ∑ u ∈ smallS, (mult u : ℂ) / (z - u)

/-- What the criterion calls `D`: `ξ'/ξ` with the small zeros' poles removed. -/
def xiD (z : ℂ) : ℂ := logDeriv riemannXi z - smallSum z

/-- A zero of `ξ` has nonzero divisor. -/
theorem divisor_ne_zero_of_zero {z : ℂ} (hz : riemannXi z = 0) :
    ((MeromorphicOn.divisor riemannXi Set.univ z : ℤ)) ≠ 0 := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (Set.mem_univ z)]
  intro hc
  have hord : analyticOrderAt riemannXi z = 0 := by
    have hne := analyticOrderAt_riemannXi_ne_top z
    lift analyticOrderAt riemannXi z to ℕ using hne with k hk
    simpa using hc
  rw [analyticOrderAt_eq_zero] at hord
  rcases hord with h | h
  · exact h ((analyticOnNhd_riemannXi z (Set.mem_univ z)))
  · exact h hz

/-- **Every zero of `ξ` is exceptional.** -/
theorem mem_xiExceptional_of_zero {z : ℂ} (hz : riemannXi z = 0) : z ∈ xiExceptional := by
  have hd := divisor_ne_zero_of_zero hz
  rcases lt_or_ge ‖z‖ 1 with h | h
  · refine Or.inr ?_
    rw [smallS, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨h, hd⟩
  · refine Or.inl ⟨⟨⟨z, h⟩, ⟨0, ?_⟩⟩, rfl⟩
    show 0 < ((MeromorphicOn.divisor riemannXi Set.univ z : ℤ)).toNat
    have hnn : (0 : ℤ) ≤ ((MeromorphicOn.divisor riemannXi Set.univ z : ℤ)) := by
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg analyticOnNhd_riemannXi z
    omega

/-- Off the exceptional set, `ξ` does not vanish. -/
theorem riemannXi_ne_zero_of_notMem {z : ℂ} (hz : z ∉ xiExceptional) : riemannXi z ≠ 0 :=
  fun hc => hz (mem_xiExceptional_of_zero hc)

/-- **The exceptional set is countable.** -/
theorem countable_xiExceptional : xiExceptional.Countable :=
  Cvs.ZeroFree.countable_range_zeroSeq.union (smallS : Set ℂ).to_countable

theorem range_subset_xiExceptional : Set.range (zeroSeq riemannXi) ⊆ xiExceptional :=
  Set.subset_union_left

/-- **Hadamard, in the criterion's shape** — carrying the product identity alongside, so that
rung 3's conclusion can be stated for `ξ` itself and not only for `ξ'/ξ`. -/
theorem exists_hadamard_xiD :
    ∃ h : ℂ → ℂ, Differentiable ℂ h
      ∧ (∀ z : ℂ, riemannXi z
          = finiteFactor smallS mult z
            * (∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n))
            * Complex.exp (h z))
      ∧ (∀ z : ℂ, z ∉ xiExceptional →
          xiD z = (∑' n : zeroIndex riemannXi,
              (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n)) + deriv h z) := by
  obtain ⟨h, hhdiff, hprod, hsplit⟩ := Cvs.ZeroFree.exists_hadamard_riemannXi_split
  refine ⟨h, hhdiff, fun z => hprod z, fun z hz => ?_⟩
  have hxi : riemannXi z ≠ 0 := riemannXi_ne_zero_of_notMem hz
  simp only [xiD, smallSum, mult, smallS, hsplit z hxi]
  ring

end Cvs.ZeroFree
