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
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.RiemannXi

/-!
# Matching Landau's near sum against the product's index set
-/

noncomputable section

open Complex Finset Cvs.Zeta

namespace Cvs.ZeroFree

open scoped Classical in
/-- The indices, with multiplicity, of the members of `S` satisfying `p`. -/
def sigmaFinset (p : ℂ → Prop) (k : ℂ → ℕ) (S : Finset ℂ) :
    Finset (Σ u : {u : ℂ // p u}, Fin (k (u : ℂ))) :=
  (S.subtype p).sigma fun _ => Finset.univ

open scoped Classical in
/-- **Collapsing the fibres.**  Summing a function of the underlying zero over the index set
weights each zero by its multiplicity. -/
theorem sum_sigmaFinset (p : ℂ → Prop) (k : ℂ → ℕ) (S : Finset ℂ) (f : ℂ → ℂ) :
    ∑ n ∈ sigmaFinset p k S, f ((n.1 : ℂ)) = ∑ u ∈ S with p u, (k u : ℂ) * f u := by
  rw [sigmaFinset, Finset.sum_sigma]
  have hfib : ∀ a : {u : ℂ // p u},
      (∑ _s ∈ (Finset.univ : Finset (Fin (k (a : ℂ)))), f (a : ℂ))
        = (k (a : ℂ) : ℂ) * f (a : ℂ) := by
    intro a
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hfib a]
  exact Finset.sum_subtype_eq_sum_filter (fun x => (k x : ℂ) * f x)

open scoped Classical in
/-- The near index set for `ξ`: the zeros of `S` of modulus `≥ 1`, with multiplicity. -/
def nearIdx (S : Finset ℂ) : Finset (zeroIndex riemannXi) :=
  sigmaFinset (fun u : ℂ => 1 ≤ ‖u‖)
    (fun u : ℂ => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) S

open scoped Classical in
/-- **Landau's near sum, over the product's indices.** With `m` identified as the divisor — which
is exactly what retains — the multiplicity weights disappear into the fibres. -/
theorem sum_nearIdx (S : Finset ℂ) (m : ℂ → ℕ)
    (hm : ∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) (f : ℂ → ℂ) :
    ∑ n ∈ nearIdx S, f (zeroSeq riemannXi n) = ∑ u ∈ S with 1 ≤ ‖u‖, (m u : ℂ) * f u := by
  have hk : ∀ u : ℂ, ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat = m u := by
    intro u
    rw [← hm u, Int.toNat_natCast]
  simp only [zeroSeq]
  rw [nearIdx, sum_sigmaFinset]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hk u]

/-- **The split by modulus.**  Landau's sum is its `‖ρ‖ ≥ 1` part — the canonical product's
zeros — plus its `‖ρ‖ < 1` part, which is `finiteFactor`'s. -/
theorem sum_split_by_norm (S : Finset ℂ) (g : ℂ → ℂ) :
    ∑ u ∈ S, g u = (∑ u ∈ S with 1 ≤ ‖u‖, g u) + ∑ u ∈ S with ¬ (1 ≤ ‖u‖), g u := by
  classical
  exact (Finset.sum_filter_add_sum_filter_not S (fun u => 1 ≤ ‖u‖) g).symm

end Cvs.ZeroFree
