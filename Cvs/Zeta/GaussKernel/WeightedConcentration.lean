import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.FiniteBlockDivergence

/-!
# The concentration carries a weight, on the window
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel

/-- **The block bound carries any weight bounded below by `1`.**  No upper bound is
hypothesised: the window is finite, so `Finset.sup` supplies one. -/
theorem weighted_block_lt {ι : Type*} [DecidableEq ι] {S T : Finset ι}
    (hTS : T ⊆ S) (hT : T.Nonempty) {γ δ : ι → ℝ} {a c₀ : ℝ} (h0 : 0 < c₀)
    {P : ℝ → Prop} (hP : ∃ᶠ lam : ℝ in Filter.atTop, P lam)
    (w : ι → ℕ) (hw1 : ∀ i, 1 ≤ w i)
    (hdom : ∀ i ∈ T, ∀ lam : ℝ, P lam →
      (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re
        ≤ -(1 / 2 * Real.exp (lam * c₀)))
    (hlt : ∀ i ∈ S, i ∉ T → ampRate a (γ i) (δ i) < c₀) (C : ℝ) :
    ∃ᶠ lam : ℝ in Filter.atTop,
      ∑ i ∈ S, (w i : ℝ)
          * (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re < -C := by
  classical
  obtain ⟨c₁, hc₁, hmax⟩ := exists_max_lt (S \ T) (fun i => ampRate a (γ i) (δ i))
    fun i hi => hlt i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2
  have hWle : ∀ i ∈ S, (w i : ℝ) ≤ ((S.sup w : ℕ) : ℝ) := by
    intro i hi
    exact_mod_cast Finset.le_sup (f := w) hi
  refine frequently_finset_sum_lt hTS hT (by norm_num : (0 : ℝ) < 1 / 2)
    (by positivity : (0 : ℝ) ≤ 4 * ((S.sup w : ℕ) : ℝ)) h0 hc₁ hP
    (fun i hi lam _ hPlam => ?_) (fun i hiS hiT lam hlam => ?_) C
  · -- the target: a weight at least `1` only deepens a negative summand
    have hs := hdom i hi lam hPlam
    have hw : (1 : ℝ) ≤ (w i : ℝ) := by exact_mod_cast hw1 i
    have hneg : (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re ≤ 0 := by
      have := Real.exp_pos (lam * c₀); linarith
    nlinarith
  · -- a competitor: bounded by `sup_S w` times its unweighted bound
    have hb : (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re
        ≤ 4 * Real.exp (lam * c₁) := by
      refine (re_gaussAmp_sq_le_four_exp hlam a (γ i) (δ i)).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (hmax i (Finset.mem_sdiff.mpr ⟨hiS, hiT⟩)) hlam
    have hwi : (w i : ℝ) ≤ ((S.sup w : ℕ) : ℝ) := hWle i hiS
    have hw0 : (0 : ℝ) ≤ (w i : ℝ) := Nat.cast_nonneg _
    have hexp : (0 : ℝ) < Real.exp (lam * c₁) := Real.exp_pos _
    rcases le_or_gt (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re 0 with hs | hs
    · have : (w i : ℝ) * (gaussAmp lam a ((γ i : ℂ) - (δ i : ℂ) * Complex.I) ^ 2).re ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hw0 hs
      nlinarith
    · nlinarith

end Cvs.Criterion
