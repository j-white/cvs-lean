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
import Cvs.Zeta.HadamardProduct.LandauNearSumIndex
import Cvs.Zeta.HadamardProduct.XiExceptionalSet
import Cvs.Zeta.RiemannXi

/-!
# Landau's near sum for `ξ`, in the criterion's shape
-/

noncomputable section

open Complex Filter Topology Finset Cvs.Zeta

namespace Cvs.ZeroFree

open scoped Classical in
/-- **Landau's near sum, split.** -/
theorem landau_sum_split {S : Finset ℂ} {m : ℂ → ℕ} {r : ℝ} (hr : 1 ≤ r)
    (hmdiv : ∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u)
    (hcomplete : ∀ u : ℂ, ‖u‖ ≤ r → m u ≠ 0 → u ∈ S) (z : ℂ) :
    ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)
      = Cvs.ZeroFree.smallSum z + ∑ n ∈ Cvs.ZeroFree.nearIdx S, 1 / (z - zeroSeq riemannXi n) := by
  have hmult : ∀ u : ℂ, m u = Cvs.ZeroFree.mult u := by
    intro u
    rw [Cvs.ZeroFree.mult, ← hmdiv u, Int.toNat_natCast]
  have h1 : ∑ u ∈ S with 1 ≤ ‖u‖, (m u : ℂ) / (z - u)
      = ∑ n ∈ Cvs.ZeroFree.nearIdx S, 1 / (z - zeroSeq riemannXi n) := by
    rw [Cvs.ZeroFree.sum_nearIdx S m hmdiv (fun u => 1 / (z - u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_one_div]
  have h2 : ∑ u ∈ S with ¬ (1 ≤ ‖u‖), (m u : ℂ) / (z - u) = Cvs.ZeroFree.smallSum z := by
    rw [Cvs.ZeroFree.smallSum]
    have hcong : ∑ u ∈ Cvs.ZeroFree.smallS, (Cvs.ZeroFree.mult u : ℂ) / (z - u)
        = ∑ u ∈ Cvs.ZeroFree.smallS, (m u : ℂ) / (z - u) :=
      Finset.sum_congr rfl fun u _ => by rw [hmult u]
    rw [hcong]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro u hu
      rw [Cvs.ZeroFree.smallS, Set.Finite.mem_toFinset] at hu
      rw [Finset.mem_filter]
      refine ⟨hcomplete u (le_trans hu.1.le hr) ?_, not_le.mpr hu.1⟩
      intro hc
      exact hu.2 (by rw [← hmdiv u, hc]; simp)
    · intro u hu hns
      rw [Finset.mem_filter] at hu
      have hlt : ‖u‖ < 1 := not_le.mp hu.2
      have hdz : ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)) = 0 := by
        by_contra hc
        exact hns (by rw [Cvs.ZeroFree.smallS, Set.Finite.mem_toFinset]; exact ⟨hlt, hc⟩)
      have : m u = 0 := by
        have := hmdiv u
        rw [hdz] at this
        exact_mod_cast this
      rw [this]
      simp
  rw [Cvs.ZeroFree.sum_split_by_norm S (fun u => (m u : ℂ) / (z - u)), h1, h2]
  ring

end Cvs.ZeroFree
