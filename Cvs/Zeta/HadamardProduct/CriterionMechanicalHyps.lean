import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
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
import Cvs.Zeta.HadamardProduct.FarZeroTail
import Cvs.Zeta.HadamardProduct.LandauNearSumIndex

/-!
# The two mechanical hypotheses of the criterion
-/

noncomputable section

open Complex Filter Topology Finset

namespace Cvs.ZeroFree

open scoped Classical in
/-- **Membership in the near index set** is membership of the zero it names. -/
theorem mem_sigmaFinset {p : ℂ → Prop} {k : ℂ → ℕ} {S : Finset ℂ}
    {n : Σ u : {u : ℂ // p u}, Fin (k (u : ℂ))} :
    n ∈ Cvs.ZeroFree.sigmaFinset p k S ↔ ((n.1 : ℂ)) ∈ S := by
  rw [Cvs.ZeroFree.sigmaFinset, Finset.mem_sigma]
  constructor
  · rintro ⟨h1, -⟩
    exact Finset.mem_subtype.mp h1
  · intro h
    exact ⟨Finset.mem_subtype.mpr h, Finset.mem_univ _⟩

variable {ι : Type*} {a : ι → ℂ}

/-- The criterion's tail is below `FarZeroTail`'s. -/
theorem tsum_compl_le_farTail (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {r : ℝ} {N : Finset ι}
    (hN : ∀ n, n ∉ N → r < ‖a n‖) :
    ∑' n : {x : ι // x ∉ N}, 4 * ‖a (n : ι)‖⁻¹ ^ 2 ≤ Cvs.ZeroFree.farTail a r := by
  classical
  set g : ι → ℝ := fun n => if r < ‖a n‖ then 4 * ‖a n‖⁻¹ ^ 2 else 0 with hg
  have hgs : Summable g := Cvs.ZeroFree.summable_farTail ha r
  have heq : ∑' n : {x : ι // x ∉ N}, 4 * ‖a (n : ι)‖⁻¹ ^ 2
      = ∑' n : {x : ι // x ∉ N}, g (n : ι) := by
    refine tsum_congr fun n => ?_
    simp only [hg, if_pos (hN (n : ι) n.2)]
  have hsplit : ∑ n ∈ N, g n + ∑' n : {x : ι // x ∉ N}, g (n : ι) = Cvs.ZeroFree.farTail a r :=
    hgs.sum_add_tsum_subtype_compl N
  have hnn : 0 ≤ ∑ n ∈ N, g n := by
    refine Finset.sum_nonneg fun n _ => ?_
    simp only [hg]
    split <;> positivity
  rw [heq, ← hsplit]
  linarith

/-- **The criterion's `ε r → 0`.**  Any near set that omits nothing of modulus `≤ r` has a
vanishing far tail. -/
theorem tendsto_tsum_compl (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {N : ℝ → Finset ι}
    (hN : ∀ᶠ r : ℝ in atTop, ∀ n, n ∉ N r → r < ‖a n‖) :
    Tendsto (fun r : ℝ => ∑' n : {x : ι // x ∉ N r}, 4 * ‖a (n : ι)‖⁻¹ ^ 2)
      atTop (nhds 0) := by
  refine squeeze_zero' (Eventually.of_forall fun r => ?_) ?_ (Cvs.ZeroFree.tendsto_farTail ha)
  · exact tsum_nonneg fun n => by positivity
  · filter_upwards [hN] with r hr
    exact tsum_compl_le_farTail ha hr

end Cvs.ZeroFree
