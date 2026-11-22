import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.DivideOutZeros
import Cvs.Zeta.Hadamard
import Cvs.Zeta.LandauLemma

/-!
# The inner factorisation

The instantiation that closes route B's construction.
-/

open Complex Set Metric Finset

namespace Cvs.Zeta

/-- The analytic order of the normalised product is the multiplicity, exactly as for the
monic one: the constant between them has order `0`. -/
theorem analyticOrderAt_normProd {S : Finset ℂ} {m : ℂ → ℕ} (hS : ∀ ρ ∈ S, ρ ≠ 0)
    {ρ : ℂ} (hρ : ρ ∈ S) :
    analyticOrderAt (normProd S m) ρ = (m ρ : ℕ∞) := by
  have hfun : normProd S m
      = (fun _ : ℂ => (∏ u ∈ S, (-(u⁻¹)) ^ m u)) * finiteFactor S m := by
    funext w; exact normProd_eq_const_mul_finiteFactor hS w
  have hc : AnalyticAt ℂ (fun _ : ℂ => (∏ u ∈ S, (-(u⁻¹)) ^ m u)) ρ := analyticAt_const
  have hF : AnalyticAt ℂ (finiteFactor S m) ρ :=
    (differentiable_finiteFactor S m).analyticAt ρ
  have hc0 : analyticOrderAt (fun _ : ℂ => (∏ u ∈ S, (-(u⁻¹)) ^ m u)) ρ = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr (const_ne_zero_of_forall_ne_zero hS)
  rw [hfun, analyticOrderAt_mul hc hF, hc0, zero_add, analyticOrderAt_finiteFactor hρ]

theorem analyticOrderAt_normProd_of_notMem {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ ρ ∈ S, ρ ≠ 0) {z : ℂ} (hz : z ∉ S) :
    analyticOrderAt (normProd S m) z = 0 := by
  rw [analyticOrderAt_eq_zero]
  exact Or.inr (normProd_ne_zero_of_notMem hS hz)

/-- Order comparison transfers from `analyticOrderAt` to `meromorphicOrderAt`. -/
theorem meromorphicOrderAt_le_of_analyticOrderAt_le {f φ : ℂ → ℂ} {z : ℂ}
    (hfa : AnalyticAt ℂ f z) (hφa : AnalyticAt ℂ φ z)
    (hfne : analyticOrderAt f z ≠ ⊤) (hφne : analyticOrderAt φ z ≠ ⊤)
    (h : analyticOrderAt φ z ≤ analyticOrderAt f z) :
    meromorphicOrderAt φ z ≤ meromorphicOrderAt f z := by
  rw [hfa.meromorphicOrderAt_eq, hφa.meromorphicOrderAt_eq]
  lift analyticOrderAt f z to ℕ using hfne with a ha
  lift analyticOrderAt φ z to ℕ using hφne with b hb
  simp only [ENat.map_natCast]
  exact_mod_cast h

/-- **The inner factorisation, for any entire `f` with `f 0 ≠ 0`.** `S` is the zero set of `f` in
the closed disc of radius `r`, `m` the multiplicities, and `g = f / ∏_{ρ∈S}(1-z/ρ)^{m ρ}`. -/
theorem exists_inner_factorization {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hford : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤) (hf0 : f 0 ≠ 0) (r : ℝ) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ ρ ∈ S, ρ ≠ 0) ∧ (∀ ρ ∈ S, ‖ρ‖ ≤ r) ∧
      AnalyticOnNhd ℂ g Set.univ ∧
      (∀ z, f z = g z * normProd S m z) ∧
      (∀ z : ℂ, ‖z‖ ≤ r → g z ≠ 0) ∧
      ((∑ σ ∈ S, (m σ : ℤ))
        = ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u) ∧
      (∀ ρ ∈ S, f ρ = 0) ∧
      (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor f Set.univ u) := by
  classical
  -- the zero set in the disc is finite
  set S : Finset ℂ := (finite_setOf_divisor_ne_zero hf r).toFinset with hSdef
  set m : ℂ → ℕ := fun u => (analyticOrderAt f u).toNat with hmdef
  have hmem : ∀ u : ℂ, u ∈ S ↔ ‖u‖ ≤ r ∧ (MeromorphicOn.divisor f Set.univ u : ℤ) ≠ 0 := by
    intro u; rw [hSdef]; simp
  -- membership is the same as a nonzero order
  have hdiv : ∀ u : ℂ, (MeromorphicOn.divisor f Set.univ u : ℤ) = (m u : ℤ) := by
    intro u
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf (Set.mem_univ u), hmdef]
    lift analyticOrderAt f u to ℕ using hford u with k hk
    simp
  have hord_eq : ∀ u : ℂ, analyticOrderAt f u = (m u : ℕ∞) := by
    intro u
    rw [hmdef]
    lift analyticOrderAt f u to ℕ using hford u with k hk
    simp
  have hS0 : ∀ ρ ∈ S, ρ ≠ 0 := by
    intro ρ hρ hc
    have h1 := ((hmem ρ).mp hρ).2
    rw [hdiv ρ, hc] at h1
    have : analyticOrderAt f 0 = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr hf0
    rw [hord_eq 0] at this
    simp at this
    exact h1 (by exact_mod_cast this)
  have hSr : ∀ ρ ∈ S, ‖ρ‖ ≤ r := fun ρ hρ => ((hmem ρ).mp hρ).1
  -- `normProd` is entire and its order never exceeds `f`'s
  have hnpa : ∀ z : ℂ, AnalyticAt ℂ (normProd S m) z :=
    fun z => (differentiable_normProd S m hS0).analyticAt z
  have hφ : AnalyticOnNhd ℂ (normProd S m) Set.univ := fun z _ => hnpa z
  have hnpne : ∀ z : ℂ, analyticOrderAt (normProd S m) z ≠ ⊤ := by
    intro z
    by_cases hz : z ∈ S
    · rw [analyticOrderAt_normProd hS0 hz]; simp
    · rw [analyticOrderAt_normProd_of_notMem hS0 hz]; simp
  have hnpord : ∀ z : ℂ, analyticOrderAt (normProd S m) z ≤ analyticOrderAt f z := by
    intro z
    by_cases hz : z ∈ S
    · rw [analyticOrderAt_normProd hS0 hz, hord_eq z]
    · rw [analyticOrderAt_normProd_of_notMem hS0 hz]; exact zero_le
  have hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z (Set.mem_univ z)).meromorphicOrderAt_eq]
    lift analyticOrderAt f z to ℕ using hford z with a ha
    simp
  have hfinφ : ∀ z : ℂ, meromorphicOrderAt (normProd S m) z ≠ ⊤ := by
    intro z
    rw [(hnpa z).meromorphicOrderAt_eq]
    lift analyticOrderAt (normProd S m) z to ℕ using hnpne z with a ha
    simp
  have hle : ∀ z : ℂ, meromorphicOrderAt (normProd S m) z ≤ meromorphicOrderAt f z :=
    fun z => meromorphicOrderAt_le_of_analyticOrderAt_le (hf z (Set.mem_univ z)) (hnpa z)
      (hford z) (hnpne z) (hnpord z)
  -- the multiplicities sum to the divisor over the disc
  have hcount : (∑ σ ∈ S, (m σ : ℤ))
      = ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u := by
    have hsupp : Function.support
        (fun u => (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u : ℤ))
        ⊆ (S : Set ℂ) := by
      intro u hu
      have hu0 : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u : ℤ) ≠ 0 := hu
      have humem : u ∈ Metric.closedBall (0 : ℂ) r := by
        by_contra hc
        exact hu0 (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc)
      have hball : ‖u‖ ≤ r := by simpa using humem
      refine (hmem u).mpr ⟨hball, ?_⟩
      rwa [divisor_eq_divisor_ball hf humem]
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
    refine Finset.sum_congr rfl fun u hu => ?_
    have humem : u ∈ Metric.closedBall (0 : ℂ) r := by
      simpa using ((hmem u).mp hu).1
    rw [← divisor_eq_divisor_ball hf humem, hdiv u]
  -- every listed point is a zero: its order is nonzero and `f` is analytic there
  have hSzero : ∀ ρ ∈ S, f ρ = 0 := by
    intro ρ hρ
    have h1 := ((hmem ρ).mp hρ).2
    rw [hdiv ρ] at h1
    have hm : m ρ ≠ 0 := by exact_mod_cast h1
    have hord : analyticOrderAt f ρ ≠ 0 := by
      rw [hord_eq ρ]
      exact_mod_cast hm
    by_contra hc
    exact hord (analyticOrderAt_eq_zero.mpr (Or.inr hc))
  refine ⟨S, m, toMeromorphicNFOn ((normProd S m)⁻¹ • f) Set.univ, hS0, hSr,
    analyticOnNhd_toMeromorphicNFOn_of_order_le hf hφ hfinf hfinφ hle,
    fun z => eq_mul_toMeromorphicNFOn_of_order_le hf hφ hfinf hle z, ?_, hcount, hSzero,
    fun u => (hdiv u).symm⟩
  intro z hzr
  refine toMeromorphicNFOn_ne_zero_of_order_eq hf hφ hfinf hfinφ ?_
  rw [(hf z (Set.mem_univ z)).meromorphicOrderAt_eq, (hnpa z).meromorphicOrderAt_eq]
  by_cases hz : z ∈ S
  · rw [analyticOrderAt_normProd hS0 hz, hord_eq z]
  · have hmz : m z = 0 := by
      by_contra hc
      exact hz ((hmem z).mpr ⟨hzr, by rw [hdiv z]; exact_mod_cast hc⟩)
    rw [analyticOrderAt_normProd_of_notMem hS0 hz, hord_eq z, hmz]
    simp

end Cvs.Zeta
