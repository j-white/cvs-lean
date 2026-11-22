import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.FiniteBlockDivergence
import Cvs.Zeta.GaussKernel.WeightedConcentration

/-!
# The weighted concentration, both halves

`WeightedConcentration` carried a weight through the window, where finiteness supplies the bound.
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel

/-- **The weighted tail vanishes.**  Dominated convergence with the weight moved inside; the
cost is that the dominator must be summable *against the weight*. -/
theorem tendsto_tsum_weighted_far {a lam₀ : ℝ} {ι : Type*} (γ δ : ι → ℝ) (w : ι → ℕ)
    (hδ : ∀ i, |δ i| ≤ 1 / 2)
    (hfar : ∀ i, 1 / 2 < |γ i - a| ∧ 1 / 2 < |γ i + a|)
    (hb : Summable fun i => (w i : ℝ) *
      (Real.exp (lam₀ * ((δ i) ^ 2 - (γ i - a) ^ 2))
        + Real.exp (lam₀ * ((δ i) ^ 2 - (γ i + a) ^ 2))
        + 2 * Real.exp (lam₀ * ((δ i) ^ 2 - (γ i) ^ 2 - a ^ 2)))) :
    Filter.Tendsto
      (fun lam : ℝ => ∑' i, (w i : ℝ)
        * (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re)
      Filter.atTop (nhds 0) := by
  have hsq : ∀ i, (δ i) ^ 2 < (γ i - a) ^ 2 ∧ (δ i) ^ 2 < (γ i + a) ^ 2 := by
    intro i
    obtain ⟨h1, h2⟩ := hfar i
    have hd : (δ i) ^ 2 ≤ 1 / 4 := by
      nlinarith [abs_nonneg (δ i), sq_abs (δ i), hδ i]
    exact ⟨by nlinarith [abs_nonneg (γ i - a), sq_abs (γ i - a)],
           by nlinarith [abs_nonneg (γ i + a), sq_abs (γ i + a)]⟩
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun lam i => (w i : ℝ)
      * (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re)
    (g := fun _ : ι => (0 : ℝ)) hb
    (fun i => by
      simpa using (tendsto_re_gaussAmp_sq_of_far (hsq i).1 (hsq i).2).const_mul (w i : ℝ))
    (Filter.eventually_atTop.mpr ⟨lam₀, fun lam hlam i => by
      rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left
        (abs_re_gaussAmp_sq_le_of_le hlam (hsq i).1 (hsq i).2) (Nat.cast_nonneg _)⟩)
  simpa using h

/-- **The weighted total is frequently negative.**  `WeightedConcentration`'s window, this block's tail, and
`B110B`'s splitter — which is generic in the summand and so takes the weight unchanged. -/
theorem frequently_weighted_tsum_neg {ι : Type*} [DecidableEq ι] {S T : Finset ι}
    (hTS : T ⊆ S) (hT : T.Nonempty) {γ δ : ι → ℝ} {a c₀ lam₀ : ℝ} (h0 : 0 < c₀)
    (w : ι → ℕ) (hw1 : ∀ i, 1 ≤ w i)
    {P : ℝ → Prop} (hP : ∃ᶠ lam : ℝ in Filter.atTop, P lam)
    (hdom : ∀ i ∈ T, ∀ lam : ℝ, P lam →
      (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re
        ≤ -(1 / 2 * Real.exp (lam * c₀)))
    (hlt : ∀ i ∈ S, i ∉ T → ampRate a (γ i) (δ i) < c₀)
    (hsum : ∀ᶠ lam : ℝ in Filter.atTop, Summable fun i => (w i : ℝ)
      * (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re)
    (hδ : ∀ i : ((S : Set ι)ᶜ : Set ι), |δ i| ≤ 1 / 2)
    (hfar : ∀ i : ((S : Set ι)ᶜ : Set ι),
      1 / 2 < |γ i - a| ∧ 1 / 2 < |γ i + a|)
    (hb : Summable fun i : ((S : Set ι)ᶜ : Set ι) => (w i : ℝ) *
      (Real.exp (lam₀ * ((δ i) ^ 2 - (γ i - a) ^ 2))
        + Real.exp (lam₀ * ((δ i) ^ 2 - (γ i + a) ^ 2))
        + 2 * Real.exp (lam₀ * ((δ i) ^ 2 - (γ i) ^ 2 - a ^ 2)))) :
    ∃ᶠ lam : ℝ in Filter.atTop,
      ∑' i, (w i : ℝ)
        * (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re < 0 := by
  refine frequently_tsum_neg S hsum
    (Cvs.Criterion.weighted_block_lt hTS hT h0 hP w hw1 hdom hlt 1) ?_
  have htend := tendsto_tsum_weighted_far (a := a) (lam₀ := lam₀)
    (fun i : ((S : Set ι)ᶜ : Set ι) => γ i) (fun i => δ i) (fun i => w i) hδ hfar hb
  exact (htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le

end Cvs.Criterion
