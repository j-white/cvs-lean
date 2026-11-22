import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedConcentrationHalves
import Cvs.Zeta.GaussKernel.WeightedDominator
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaZeroWindows

/-!
# The weighted rate lemma, at the zeros

`WeightedConcentrationHalves` gives the weighted engine and `WeightedDominator` its tail hypothesis at the divisor weight.
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel Cvs.GaussKernel

/-- **The divisor weight is at least one**, which is what the weighted block bound needs. -/
theorem one_le_divisorWeight (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    1 ≤ Cvs.Criterion.divisorWeight rho :=
  Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity_pos _

/-- **Eventual weighted summability**, the `hsum` of the engine. -/
theorem summable_weighted_re_gaussAmp_sq {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (Cvs.Criterion.divisorWeight rho : ℝ)
      * (gaussAmp lam a ((gam rho : ℂ) - (del rho : ℂ) * Complex.I) ^ 2).re := by
  refine Summable.of_norm_bounded
    (Cvs.Criterion.summable_divisorWeight_quartic.mul_left
      (Real.exp (lam / 4) * (4 * (1 + 2 * a ^ 2 + 4 / lam) ^ 2))) fun rho => ?_
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have hb : |(gaussAmp lam a ((gam rho : ℂ) - (del rho : ℂ) * Complex.I) ^ 2).re|
      ≤ (Real.exp (lam / 4) * (4 * (1 + 2 * a ^ 2 + 4 / lam) ^ 2))
          * (1 / (1 + (gam rho) ^ 4)) := by
    rw [mul_one_div]
    exact abs_re_gaussAmp_sq_le_inv_quartic hlam (del_bdd rho) a (gam rho)
  have hw : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hb hw) (le_of_eq ?_)
  rw [gam]; ring

theorem eventually_summable_weighted (a : ℝ) :
    ∀ᶠ lam : ℝ in Filter.atTop, Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (gaussAmp lam a ((gam rho : ℂ) - (del rho : ℂ) * Complex.I) ^ 2).re := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact summable_weighted_re_gaussAmp_sq hlam a

/-- **The weighted rate lemma.**  `B110C.frequently_tsum_neg_of_rate` with the divisor weight
carried through: the hypotheses are unchanged, because they constrain the zeros and not the
weight. -/
theorem frequently_weighted_tsum_neg_of_rate
    {i₀ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet} (hδ₀ : del i₀ ≠ 0) (hγ₀ : 0 < gam i₀)
    {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hεδ : ε < |del i₀|)
    (hεγ : 2 * ε < gam i₀)
    (hlocal : ∀ i, gam i = gam i₀ ∨ gam i = -gam i₀ →
      (del i) ^ 2 = (del i₀) ^ 2 ∨ (del i) ^ 2 < (del i₀) ^ 2)
    (hrate : ∀ i, gam i ≠ gam i₀ → gam i ≠ -gam i₀ →
      ampRate (gam i₀ - ε) (gam i) (del i) < (del i₀) ^ 2 - ε ^ 2) :
    ∃ᶠ lam : ℝ in Filter.atTop,
      ∑' i : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight i : ℝ)
        * (gaussAmp lam (gam i₀ - ε)
            ((gam i : ℂ) - (del i : ℂ) * Complex.I) ^ 2).re < 0 := by
  classical
  obtain ⟨S, hS⟩ := exists_window_finset gam summable_zeta_quartic (|gam i₀| + 1)
  have hi₀S : i₀ ∈ S := (hS i₀).mpr (by linarith)
  refine Cvs.Criterion.frequently_weighted_tsum_neg (lam₀ := 1)
    (Finset.filter_subset (fun i => (gam i = gam i₀ ∨ gam i = -gam i₀)
      ∧ ((del i) ^ 2 = (del i₀) ^ 2)) S)
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀S, Or.inl rfl, rfl⟩⟩
    (target_rate_pos hε hεδ) Cvs.Criterion.divisorWeight one_le_divisorWeight
    (frequently_amp_conditions hδ₀
      (by rw [show gam i₀ - (gam i₀ - ε) = ε by ring]; exact ne_of_gt hε)
      (mul_pos hγ₀ (by linarith))) (fun i hi lam hP => ?_) (fun i hiS hiT => ?_)
    (eventually_summable_weighted _)
    (fun i => del_bdd i) (fun i => ?_) ?_
  · obtain ⟨hγi, hδi⟩ := (Finset.mem_filter.mp hi).2
    refine re_gaussAmp_sq_le_neg_half_of_orbit hγi hδi ?_
    have := re_gaussAmp_sq_le_neg_half_of (lam := lam) (a := gam i₀ - ε)
      (γ := gam i₀) (δ := del i₀) hP
    rwa [show (del i₀) ^ 2 - (gam i₀ - (gam i₀ - ε)) ^ 2 = (del i₀) ^ 2 - ε ^ 2 by ring] at this
  · refine ampRate_lt_cases_rate hε hεγ (fun hγ => ?_) (hrate i)
    rcases hlocal i hγ with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨hiS, hγ, h⟩) hiT
    · exact h
  · have hnot : ¬ (|gam (i : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet)| ≤ |gam i₀| + 1) :=
      fun h => i.2 ((hS _).mpr h)
    exact far_of_not_mem_window hε hε4 (by linarith [not_le.mp hnot])
  · exact (Cvs.Criterion.summable_weighted_bumps one_pos (gam i₀ - ε)).subtype _

end Cvs.Criterion
