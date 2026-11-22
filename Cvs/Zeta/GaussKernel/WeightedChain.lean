import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.BumpAlgebra
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-!
# The chain, at the divisor weight
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel Cvs.GaussKernel Cvs.GaussKernel

/-- The weighted shell lemma: competitors outside the shell lose for free. -/
theorem frequently_weighted_tsum_neg_of_shell
    {i₀ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hδ₀ : del i₀ ≠ 0) (hγ₀ : 0 < gam i₀)
    {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hεδ : ε < |del i₀|)
    (hεγ : 2 * ε < gam i₀)
    (hlocal : ∀ i, gam i = gam i₀ ∨ gam i = -gam i₀ →
      (del i) ^ 2 = (del i₀) ^ 2 ∨ (del i) ^ 2 < (del i₀) ^ 2)
    (hshell : ∀ i, gam i ≠ gam i₀ → gam i ≠ -gam i₀ → |gam i| < gam i₀ + 1 / 2 →
      ampRate (gam i₀ - ε) (gam i) (del i) < (del i₀) ^ 2 - ε ^ 2) :
    ∃ᶠ lam : ℝ in Filter.atTop,
      ∑' i : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight i : ℝ)
        * (gaussAmp lam (gam i₀ - ε)
            ((gam i : ℂ) - (del i : ℂ) * Complex.I) ^ 2).re < 0 :=
  Cvs.Criterion.frequently_weighted_tsum_neg_of_rate hδ₀ hγ₀ hε hε4 hεδ hεγ hlocal
    (fun i h1 h2 => by
      by_cases h : |gam i| < gam i₀ + 1 / 2
      · exact hshell i h1 h2 h
      · exact ampRate_lt_of_far_above hε (by linarith)
          (sq_le_quarter_of_abs_le (del_bdd i))
          (by linarith [not_lt.mp h]))

/-- The failure statement, at the divisor weight. -/
def WeightedFail : Prop :=
  ∀ a : ℝ, ¬ ∃ᶠ lam : ℝ in Filter.atTop,
    ∑' i : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight i : ℝ)
      * (gaussAmp lam a ((gam i : ℂ) - (del i : ℂ) * Complex.I) ^ 2).re < 0

/-- **A defeat costs the square of the distance**, at the weight.  `BumpAlgebra`'s
`exists_gain_of_not_frequently` with the weighted shell lemma in place of the unweighted one;
the proof is otherwise unchanged, because the weight appears nowhere in it. -/
theorem exists_gain_of_weighted_fail (hfail : WeightedFail)
    {i₀ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hδ₀ : del i₀ ≠ 0) (hγ₀ : 0 < gam i₀)
    (hrec : IsRecord gam del i₀) :
    ∃ j, gam i₀ < |gam j| ∧ (|gam j| - gam i₀) ^ 2 ≤ (del j) ^ 2 - (del i₀) ^ 2 := by
  classical
  obtain ⟨S, hS⟩ := exists_window_finset gam summable_zeta_quartic (|gam i₀| + 1)
  set R := S.filter (fun i => gam i ≠ gam i₀ ∧ gam i ≠ -gam i₀) with hR
  obtain ⟨ε, hε, hε4, hεδ, hεγ, hgaps⟩ :=
    exists_eps_bounds_abs R gam hγ₀ hδ₀
      (fun i hi => ((Finset.mem_filter.mp hi).2).1)
      (fun i hi => ((Finset.mem_filter.mp hi).2).2)
  have ha : (0 : ℝ) ≤ gam i₀ - ε := by linarith
  have hlocal : ∀ i, gam i = gam i₀ ∨ gam i = -gam i₀ →
      (del i) ^ 2 = (del i₀) ^ 2 ∨ (del i) ^ 2 < (del i₀) ^ 2 := by
    intro i hi
    have : |gam i| ≤ |gam i₀| := by
      rcases hi with h | h
      · rw [h]
      · rw [h, abs_neg]
    exact (lt_or_eq_of_le (hrec i this)).symm.imp id id
  by_contra hno
  push_neg at hno
  refine hfail (gam i₀ - ε) ?_
  refine frequently_weighted_tsum_neg_of_shell hδ₀ hγ₀ hε hε4 hεδ hεγ hlocal
    (fun i h1 h2 hshell => ?_)
  by_contra hbeat
  have habs : |gam i₀| = gam i₀ := abs_of_pos hγ₀
  have hmem : i ∈ R :=
    Finset.mem_filter.mpr ⟨(hS i).mpr (by rw [habs]; linarith), h1, h2⟩
  obtain ⟨hg1, hg2⟩ := hgaps i hmem
  rcases above_or_far_below hg1 hg2 with habove | hbelow
  · have hstrict : gam i₀ < |gam i| := by
      have h := two_mul_lt_abs_abs_sub hg1 hg2
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ |gam i| - gam i₀)] at h
      linarith
    have hgain := sq_dist_le_gain hε ha habove (not_lt.mp hbeat)
    linarith [hno i hstrict]
  · have hdom : (del i) ^ 2 ≤ (del i₀) ^ 2 := hrec i (by rw [habs]; linarith)
    exact hbeat (ampRate_lt_of_below hε ha hdom (by linarith))

theorem step_of_weighted_fail (hfail : WeightedFail)
    {i₀ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hδ₀ : del i₀ ≠ 0) (hγ₀ : 0 < gam i₀)
    (hrec : IsRecord gam del i₀) :
    ∃ j u, StepUp gam del (IsRecord gam del) i₀ j u := by
  obtain ⟨j, hjabove, hjgain⟩ := exists_gain_of_weighted_fail hfail hδ₀ hγ₀ hrec
  obtain ⟨j', hj'rec, hj'le, hj'ge⟩ := exists_record_ge gam del finite_window j
  refine ⟨j', |gam j| - gam i₀, by linarith, ?_, ?_, hj'rec⟩
  · have : |gam i₀| = gam i₀ := abs_of_pos hγ₀
    rw [this]; linarith
  · linarith

theorem goodStep_of_weighted_fail (hfail : WeightedFail)
    {i₀ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hg : GoodRecord gam del i₀) :
    ∃ j u, StepUp gam del (GoodRecord gam del) i₀ j u := by
  obtain ⟨hrec, hpos, hδ₀⟩ := hg
  obtain ⟨j, u, hu, hjle, hjgain, hjrec⟩ := step_of_weighted_fail hfail hδ₀ hpos hrec
  have hδj : del j ≠ 0 := by
    intro h
    rw [h] at hjgain
    have : (0 : ℝ) < (del i₀) ^ 2 := by positivity
    nlinarith [hjgain, sq_nonneg u]
  obtain ⟨j', hj'good, hj'abs, hj'sq⟩ :=
    goodRecord_of_record gam del hasMirror_zeta hjrec hδj
  exact ⟨j', u, hu, by rw [hj'abs]; exact hjle, by rw [hj'sq]; exact hjgain, hj'good⟩

/-- **The crowding statement, at the divisor weight.** -/
theorem card_le_of_weighted_fail (hfail : WeightedFail)
    {i₀ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hg : GoodRecord gam del i₀) (n : ℕ) :
    n ≤ ((finite_window (|gam i₀| + Real.sqrt n / 2)).toFinset).card :=
  chain_card_le gam del (GoodRecord gam del)
    (fun i hi => goodStep_of_weighted_fail hfail hi)
    i₀ hg finite_window del_bdd n

end Cvs.Criterion
